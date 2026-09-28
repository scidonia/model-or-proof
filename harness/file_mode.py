"""File mode: the unit of proof is the file, closed by demonstration (plan D26).

The prover is given a working copy of the seed and a shell; it edits the file itself and runs Lean on
it, and the harness decides closure with the oracle in :mod:`harness.closure_oracle` — integrity,
elaboration, and the axiom set. That is the difference from tactic mode, where the driver splices one
tactic per turn into a repl's proof state: here the art is the model's, and the harness's part is the
working copy, the budget, the evidence, and the verdict.

Three things this module is careful about, because each has already cost the experiment a run:

* **The integrity baseline is the pristine text, never the working tree.** A shell can write anywhere,
  so a candidate that "matches" an edited seed would pass integrity while proving a different theorem.
  The caller passes the text recorded before the run (``route_b`` holds it from the seed's baseline),
  and the seed's own digest is re-checked afterwards and recorded — a moved seed is reported and the
  run does not count as closed, whatever the candidate looks like.
* **Integrity violations are reported, not prevented.** The model may rewrite the statement if it
  likes; the row then says the candidate is not a closure of what we pinned. Prevention would hide the
  very failure the check exists to catch.
* **The heartbeat answers "is it stuck, and where".** A file-mode turn is not a tactic: the driver
  cannot count progress per proposal, so the working copy's size and mtime are watched while the turn
  runs, and the session's own transcript is counted once it lands.

Closure is the oracle's word, and only the oracle's: the file elaborating with the pinned statement and
no ``sorryAx``.
"""

from __future__ import annotations

import os
import pathlib
import sys
import threading
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from harness import closure_oracle  # noqa: E402
from harness.closure import ProviderError, heartbeat, provider_failure_kind  # noqa: E402
from harness.outside_watch import OutsideWatch  # noqa: E402
from harness.result import COST_BASIS  # noqa: E402  (the row's cost_basis default)

DEFAULT_TOOLS = "bash"

#: What the file-mode message carries, in order (finding F7): one list, used by the message and recorded in
#: the row, so the setup cannot claim sections the session never saw. "closure criteria" is the grading
#: contract from plan D26 — the three things the oracle decides on, stated before the model starts.
FILE_MODE_PROMPT_SECTIONS = ("specification", "statement", "working file", "closure criteria")

#: How many consecutive rounds with an *identical* check result and a *byte-identical* working file end the
#: run as `no_progress`, distinct from `timeout` (plan D24's round-boundary decision, ruled 2026-09-26).
#: The degenerate case is a false statement: the mutant control ran 94 rounds reporting `sorryAx` with the
#: file untouched, turn times collapsing from 117 s to 2 s. Five is deliberately conservative — the same
#: axioms *and* the same bytes, not merely slow progress — because a detector that fires on a converging
#: run would end real work. It is not a cut: the per-turn deadline stays gone, and this reads facts the
#: round boundary already has.
NO_PROGRESS_ROUNDS = 5



def statement_of(pristine: str, theorem: str | None = None) -> str:
    """The seed's theorem declaration, from ``theorem`` to its assignment token.

    What the file-mode prompt shows as "the statement under test": the declaration itself, not the whole
    file — the model can read the file's definitions in its working copy, and quoting them into the
    prompt would be a second copy that could drift from the one integrity pins.

    The theorem is read off the seed when the caller has no name for it (`closure_oracle.seed_theorem`,
    plan D5's one-theorem shape). A `"mutex"` default here was the same bug the oracle had: the tier-1
    corollary is `mutex_n0` and Bakery's is `mutual_exclusion`, so the declaration could not be located.
    """
    import re

    theorem = theorem or closure_oracle.seed_theorem(pristine)
    match = re.search(rf"^theorem\s+{re.escape(theorem)}\b.*?:=", pristine, re.M | re.S)
    if not match:
        return pristine.strip().splitlines()[-1] if pristine.strip() else ""
    return match.group(0).rstrip().removesuffix(":=").rstrip()


def file_prompt(working: pathlib.Path, *, statement: str, feedback: str | None = None) -> str:
    """The turn's message: what closes the theorem, and what the last round said if this is a retry.

    The three criteria are the *grading contract* (plan D26), stated before the model starts rather than only
    in the check's report after a failed round. They are what the oracle will decide on and they say nothing
    about how to prove the theorem — a contract, not a hint. File mode hands the session a shell with `lean`
    on its path, so the model can check all three itself before it stops; the point is to convert
    fail-then-retry into a self-check. The oracle stays the only authority: no verdict and no measurement
    changes, and a run that ignored these lines would be graded exactly as before.
    """
    lines = [
        "The statement under test:",
        "",
        statement.strip(),
        "",
        f"Your working file: {working.name} (in the current directory).",
        "",
        "It closes only if all three of these hold, and they are exactly what the check decides:",
        "",
        "1. The file elaborates.",
        "2. The statement above it, and every definition before that, are byte-identical to the seed:",
        "   replace the `sorry` and nothing else, up to and including `:=`.",
        "3. What you prove depends on no axioms beyond `propext`, `Classical.choice` and `Quot.sound` —",
        "   in particular no `sorry` or `sorryAx` may remain anywhere in the file.",
        "",
        "You have a shell with `lean` on your path, so you can check all three yourself before you stop.",
        "Work inside `.runs/` — the directory holding your working file — and nowhere else. A file written",
        "anywhere else in the package is a write outside the working copy, and the run's verdict is",
        "withheld when that happens, so the proof would not count even if it were correct.",
    ]
    if feedback:
        lines += ["", "The previous round did not close it. What the check reported:", "", feedback]
    lines += ["", "Close the theorem in that file."]
    return "\n".join(lines)


def _size_and_mtime(path: pathlib.Path) -> tuple[int, float]:
    try:
        stat = path.stat()
        return stat.st_size, stat.st_mtime
    except OSError:
        return -1, 0.0


def preserve_in_progress(working: pathlib.Path, run_dir: pathlib.Path) -> str:
    """Copy the working file into the run directory, so a cut or crashed run leaves its work (§8).

    ``sweep_working_copies`` deletes ``.runs/`` at the next launch, so without this a run stopped
    mid-proof leaves no record of what the model had written — the same argument as the closure copy
    (finding F6), applied to work in progress rather than to a finished artifact. It changes no
    semantics: the copy is evidence, never an input, and the oracle still reads the working copy.

    Returns what to say about it on the heartbeat, rather than writing the line itself, so both call
    sites report the same way. An unreadable working file is not a reason to lose the run's row: the
    caller gets the reason and the row is still landed.
    """
    try:
        text = working.read_text()
    except OSError as error:
        return f"in-progress copy skipped ({error})"
    target = run_dir / working.name
    try:
        target.write_text(text)
    except OSError as error:
        return f"in-progress copy failed ({error})"
    return f"in-progress copy: {len(text)} bytes -> {target.name}"


def watch_file(path: pathlib.Path, stop: threading.Event, *, interval_s: float, label: str) -> None:
    """Print the working file's size and mtime until ``stop`` (plan D26's file-mode heartbeat).

    A file-mode turn can run for minutes with nothing on the driver's side to report, so the evidence
    that the model is *working* rather than wedged is the file it is working on: a growing or rewritten
    file is progress, a file untouched for the whole turn is not.

    The first sample is taken **before** the loop and labelled as the baseline (finding F5): starting from
    ``None`` made the first tick always read ``changed``, which is a claim about the file that nothing
    supports — the first observation is not a change.
    """
    size, mtime = _size_and_mtime(path)
    last: tuple[int, float] = (size, mtime)
    unchanged_for = 0.0
    first = True
    while not stop.wait(interval_s):
        size, mtime = _size_and_mtime(path)
        changed = last != (size, mtime)
        unchanged_for = 0.0 if changed else unchanged_for + interval_s
        last = (size, mtime)
        if size < 0:
            heartbeat(f"file {label}: no file at {path.name} yet")
        elif first:
            heartbeat(
                f"file {label}: {size} bytes at the first sample (a baseline, not a change)"
            )
        else:
            heartbeat(
                f"file {label}: {size} bytes, {'changed' if changed else f'unchanged {unchanged_for:.0f}s'}"
            )
        first = False


def transcript_records(session_dir: pathlib.Path) -> tuple[int, int]:
    """How many records the session's transcripts hold, and how many bytes (plan D26).

    The transcript lives under the session's **role directory** — ``<run_dir>/<role>/*.jsonl`` — so scanning
    the run directory itself finds nothing and reports ``(0, 0)`` for a transcript that is right there
    (finding F5: a 50-record, 96 KB transcript read as zero, and misreported as "lands at close"). The role
    layout is tried first, then a flat directory, so a caller may point at either level.
    """
    records = 0
    size = 0
    candidates = sorted(session_dir.glob("*/*.jsonl")) or sorted(session_dir.glob("*.jsonl"))
    for transcript in candidates:
        # `stat().st_size`, not `len(read_text())`: the latter is characters, and a Lean transcript carries
        # multi-byte characters (the inaccessible-name dagger among them), so the two differ by ~1% and only
        # one of them is a byte count (finding F5's spirit: the number must mean what it says).
        size += transcript.stat().st_size
        records += sum(1 for line in transcript.read_text().splitlines() if line.strip())
    return records, size


def run_file(
    session,
    *,
    task: str,
    tier: int,
    repetition: int,
    mutant: bool,
    working: pathlib.Path,
    run_dir: pathlib.Path,
    seed_path: pathlib.Path,
    package: pathlib.Path,
    pristine: str,
    cap_s: float,
    cap_usd: float,
    setup: dict,
    statement: str = "",
    theorem: str | None = None,
    clock=time.monotonic,
    watch_interval_s: float = 15.0,
) -> dict:
    """Run file mode over ``working`` until the oracle calls it closed, or a budget binds.

    Returns the row. The closure object carries all three checks plus whether the seed still matches the
    text the run started from, so a reader can see *why* the verdict is what it is. The Lean search path
    the checks run with is captured **before the session opens** and carried into every one of them, so
    the environment is not one the shell could have shaped; it is recorded in the closure object.
    """
    label = working.stem
    started = clock()
    heartbeat(f"phase: file session for {working.name} (tools: the model's own shell)")
    theorem = theorem or closure_oracle.theorem_name(pristine)
    pristine_sha = closure_oracle.sha256_text(pristine)
    # The elaboration/check environment, captured **before the session opens**: the file-mode shell can
    # reach the package's lakefile, so a search path computed after its turn would be a path the
    # candidate influenced. One value for the whole run, handed to every `check` and recorded in the
    # closure object, so the environment a verdict was reached in is checkable afterwards.
    captured = closure_oracle.capture_lean_path(package)
    lean_path = captured or closure_oracle.dependency_lean_path(package)
    heartbeat(
        "phase: file-mode LEAN_PATH "
        + (
            "captured from `lake env printenv LEAN_PATH` before the session"
            if captured
            else "derived from the package manifest (`lake` gave no answer)"
        )
        + f" ({len(lean_path.split(os.pathsep))} entries)"
    )
    # Finding F2: the shell's working copy is not the only file in reach. The seed, its recorded baseline
    # text and the seed record are all outside it, so their digests are taken before the session opens and
    # compared after the loop — on *every* exit path, including a provider failure, where the old code
    # skipped the check and left `seed_intact` at its hopeful initial value. A run whose shell wrote
    # outside its copy does not count as a closure, whatever the file it produced looks like.
    outside = {
        "seed": seed_path,
        "baseline": seed_path.parent / "baseline" / seed_path.name,
        "record": seed_path.parent / "seeds.json",
    }
    outside_before = {
        name: (closure_oracle.sha256_text(path.read_text()) if path.is_file() else None)
        for name, path in outside.items()
    }
    # The seed as **loaded**, distinctly from the seed as **left** (the end-state `seed_intact`, filled
    # after the loop). The row's tactic path already reads `matches` as the loaded value
    # (`route_b.py`'s `load_baseline` and its baseline block), so this is the same key meaning on both
    # paths: a run that began from an edited seed and was repaired mid-run says so, rather than
    # reporting only the hopeful end state.
    seed_matches_loaded = outside_before["seed"] == pristine_sha

    turns = 0
    rounds = 0
    # The bytes the oracle last checked, taken once per round and never reread (see the check site): the row's
    # digest and the closure copy both come from this, so nothing can be swapped in between.
    candidate: str | None = None
    # The round-boundary repetition signal (plan D24, as ruled): the previous round's check result and
    # candidate digest, and how many consecutive rounds have matched it exactly.
    previous_signature: tuple | None = None
    no_progress_rounds = 0
    # The working-copy-only boundary, observed rather than enforced: no unprivileged user namespaces on this
    # host, so `harness.outside_watch` watches the package the shell can reach and records every event outside
    # the working copy. One watch for the whole run, so no round can write outside it unseen.
    boundary = OutsideWatch(seed_path.parent, working.parent)
    boundary.start()
    heartbeat(f"phase: boundary watch on {seed_path.parent.name}/ (allowed: {working.parent.name}/)")
    error: dict | None = None
    outcome = "timeout"
    closure_result: dict | None = None
    seed_intact = True
    feedback: str | None = None
    while True:
        elapsed = clock() - started
        usage = session.usage()
        if elapsed >= cap_s:
            outcome = "timeout"
            error = {"kind": "budget", "message": f"the wall-clock budget of {cap_s:g}s bound before closure"}
            break
        if float(usage.get("cost_usd", 0.0)) >= cap_usd:
            outcome = "timeout"
            error = {"kind": "budget", "message": f"the dollar budget of ${cap_usd:g} bound before closure"}
            break
        rounds += 1
        stop = threading.Event()
        watcher = threading.Thread(
            target=watch_file,
            args=(working, stop),
            kwargs={"interval_s": watch_interval_s, "label": label},
            daemon=True,
        )
        watcher.start()
        turn_started = clock()
        try:
            reply = session.attempt(file_prompt(working, statement=statement, feedback=feedback))
        except ProviderError as failure:
            # File mode has no per-turn cut (D24 as re-ruled after the transport experiment: a per-turn
            # deadline closes the OMP session, so it is a kill rather than a chunk and cannot be
            # continued). Every provider failure therefore ends the run, which is what the row records.
            error = {"kind": provider_failure_kind(failure), "status": failure.status, "message": failure.message}
            outcome = "error"
            # The turn failed, so no round end will run: copy what it wrote before the run ends. This is
            # the path where the evidence matters most — a cut or a dead session is exactly the case that
            # leaves nothing behind otherwise.
            heartbeat(f"file {label}: {preserve_in_progress(working, run_dir)}")
            break
        finally:
            stop.set()
            watcher.join(timeout=watch_interval_s + 1.0)
        turns += 1
        heartbeat(
            f"file {label}: round {rounds} ended (turn {turns}, {clock() - turn_started:.1f}s)"
        )
        # What the model has written so far, kept where the next launch's sweep of `.runs/` cannot reach
        # it: a run that is cut or killed later still leaves the work it had done (finding F6's argument,
        # for work in progress).
        heartbeat(f"file {label}: {preserve_in_progress(working, run_dir)}")
        records, size = transcript_records(run_dir)
        if records:
            heartbeat(f"file {label}: transcript {records} record(s), {size} bytes")
        else:
            # Not zero: *pending*. A session's transcript lands when it closes, so "0 records" would read as
            # "the session did nothing" when it means "not written yet" (finding F5).
            heartbeat(
                f"file {label}: transcript pending (nothing under {run_dir.name}/<role>/ yet; a "
                "session's transcript lands when it closes)"
            )

        # One snapshot of the candidate's bytes, taken after the session's round, and used for everything
        # that follows: the oracle's check, the row's digest and the closure copy. Hashing or copying a later
        # reread is a race the reviewer demonstrated - a swap between the check and the copy produced a
        # sidecar whose `.lean` held `sorry` while `digests_agree` was true.
        candidate = working.read_text()
        closure_result = closure_oracle.check(
            candidate,
            pristine=pristine,
            package=package,
            # The candidate's *own* module — the seed's file stem, which is what it is elaborated as and what
            # the checker imports — and the fully-qualified theorem name. Both explicit because the bug this
            # closes was a name *assumed* rather than read: a `"mutex"` default made a byte-identical seed
            # report an integrity failure on every seed that was not token-ring's tier-2 file.
            module=seed_path.stem,
            theorem=theorem,
            lean_path=lean_path,
        )
        seed_intact = closure_oracle.sha256_text(seed_path.read_text()) == pristine_sha
        heartbeat(
            f"file {label}: integrity={closure_result['integrity']} "
            f"elaborates={closure_result['elaborates']} axioms={closure_result['axioms']} "
            f"seed_intact={seed_intact}"
        )
        if closure_oracle.verdict(closure_result, seed_intact=seed_intact):
            outcome = "closed"
            break
        # The repetition signal (plan D24, as ruled): a round is *the same* as the last when the check
        # reported the same thing *and* the candidate's bytes are identical. Both facts are already in hand
        # at a round boundary, so this adds no observation — and requiring both is what keeps it off a
        # converging run, where the file changes even when a round fails. Repeated rounds end the run as
        # `no_progress` rather than running the budget down: "repeated itself" and "tried for two hours" are
        # different facts about the model, and the row should say which happened.
        signature = (
            closure_result["integrity"],
            closure_result["elaborates"],
            closure_result["closed"],
            tuple(sorted(closure_result["axioms"] or ())),
            closure_oracle.sha256_text(candidate),
        )
        no_progress_rounds = no_progress_rounds + 1 if signature == previous_signature else 0
        previous_signature = signature
        if no_progress_rounds >= NO_PROGRESS_ROUNDS:
            outcome = "no_progress"
            error = {
                "kind": "no_progress",
                "message": (
                    f"the check reported the same result and the file was byte-identical for "
                    f"{no_progress_rounds + 1} consecutive rounds: the run repeated itself rather than "
                    "making progress"
                ),
            }
            heartbeat(
                f"file {label}: no progress for {no_progress_rounds + 1} rounds "
                f"({closure_result['axioms']}); ending as no_progress"
            )
            break
        # The next round's feedback is what the oracle saw, verbatim where it is Lean's own words: the
        # model fixes what the check reported, not what the harness thinks of it.
        # The model gets Lean's **errors** first: that is what it can act on, and the oracle's own
        # sentences come after. `raw_tail` is deliberately not used here — it is the elaboration's last
        # lines (the linter's notes, or the checker's report), which is how a failing round used to be
        # told nothing while looking informed.
        problems = []
        errors = closure_result.get("errors") or []
        if errors:
            problems.append("Lean did not accept the file. Its own output:\n" + "\n".join(errors))
        if not seed_intact:
            problems.append(
                f"the seed file {seed_path} has changed since the run started; the proof must be written "
                "against the statement as recorded, not against an edited seed"
            )
        if not closure_result["integrity"]:
            problems.append(
                "the file no longer matches the seed up to the theorem's `:=`: something before the "
                "proof body was changed, and the statement must be left exactly as it is"
            )
        if not errors and closure_result.get("timed_out"):
            # An explicitly identified timeout: Lean never finished, so there is no diagnostic to select
            # and the last lines are better than silence. A diagnostic-free failure that is *not* a timeout
            # is deliberately not covered here — forwarding arbitrary output is the defect F3 closes.
            problems.append(
                "Lean did not finish elaborating the file within the check's bound; last output:\n"
                + "\n".join(closure_result["raw_tail"])
            )
        if not closure_result["closed"]:
            if closure_result.get("axiom_report") not in (None, "ok"):
                # No usable report: there is no set to talk about, and saying "depends on axioms" would be
                # a diagnosis we cannot support (finding F1's vocabulary: missing/ambiguous).
                problems.append(
                    f"the axiom report could not be read ({closure_result['axiom_report']}): the harness "
                    "cannot tell whether the proof is complete, only that the check did not pass"
                )
            elif closure_result["axioms"] is not None:
                problems.append(
                    "the theorem still depends on axioms outside "
                    f"{sorted(closure_oracle.ALLOWED_AXIOMS)}: {closure_result['axioms']}"
                )
            else:
                problems.append("the axiom check did not pass and carried no set to report")
        feedback = "\n\n".join(problems)
        # A round that changed nothing is still a round: the budget is the terminator, not a round count.
        heartbeat(f"file {label}: not closed yet, feeding the check back to the model")

    usage = session.usage()
    # F2: re-hash outside the copy on *every* exit path, including the provider-failure break above.
    outside_after = {
        name: (closure_oracle.sha256_text(path.read_text()) if path.is_file() else None)
        for name, path in outside.items()
    }
    outside_writes = sorted(name for name, digest in outside_after.items() if digest != outside_before[name])
    seed_intact = outside_after["seed"] == pristine_sha
    # The observed boundary (`harness.outside_watch`): what the shell did outside its working copy, and whether
    # the observation itself went blind. Either one means the run is not a closure, whatever its file says.
    outside_events, watch_blind = boundary.stop()
    closure = {
        **(closure_result or {}),
        "seed_intact": seed_intact,
        # The search path the checks ran with, captured before the session opened: part of the run's
        # evidence, so a reader can see which environment the verdict was reached in.
        "lean_path": lean_path,
        "outside_writes": outside_writes,
        "outside_events": outside_events,
        "watch_blind": watch_blind,
        "verdict": bool(
            closure_result
            and not outside_writes
            and not outside_events
            and not watch_blind
            and closure_oracle.verdict(closure_result, seed_intact=seed_intact)
        ),
        # Why the final judgement was withheld, when it was (planner's ruling). `outcome` answers "how did
        # the loop stop" and `verdict` answers "is this a proof, boundary conditions included" — two
        # different questions, so a reader meeting `outcome: closed` beside `verdict: False` needs to see
        # that a boundary condition withheld it rather than that the oracle refused the proof. Empty on a
        # run whose verdict stands, which is the ordinary case.
        "withheld": [
            name
            for name, blocked in (
                ("seed_intact", not seed_intact),
                ("oracle", not (closure_result and closure_oracle.verdict(closure_result, seed_intact=seed_intact))),
                ("outside_writes", bool(outside_writes)),
                ("outside_events", bool(outside_events)),
                ("watch_blind", bool(watch_blind)),
            )
            if blocked
        ],
        "rounds": rounds,
        # How much of the run was repetition rather than work (plan D24, as ruled): consecutive rounds whose
        # check result and candidate bytes were identical. Zero on a run that never repeated itself, and the
        # count that ended a `no_progress` run, so a reader sees *why* the run stopped rather than inferring
        # it from the outcome name alone.
        "no_progress_rounds": no_progress_rounds,
        # What the checks were *told* to check, as opposed to what they assumed: the module is the seed's own
        # file stem and the theorem its fully-qualified name, both read off the seed. A reader can see which
        # declaration the axioms belong to, the same way `pristine_sha256` says which text was pinned.
        "module": seed_path.stem,
        "theorem": theorem,
    }
    # The closure copy is written **from the snapshot the oracle checked** (finding: the sidecar race), so the
    # bytes that survive are the bytes that were verified — nothing downstream may reread the path. `run_dir`
    # is `results/omp/<token>`, so its grandparent is the results directory.
    copy_path: pathlib.Path | None = None
    if closure["verdict"] and candidate is not None:
        closure_dir = run_dir.parent.parent / "closures" / task
        closure_dir.mkdir(parents=True, exist_ok=True)
        copy_path = closure_dir / f"{run_dir.name}.lean"
        copy_path.write_text(candidate)
    return {
        "task": task,
        "mode": "file",
        "tier": tier,
        "repetition": repetition,
        "mutant": mutant,
        "outcome": outcome,
        "wall_clock_s": round(clock() - started, 3),
        "cost_usd": float(usage.get("cost_usd", 0.0)),
        "cost_basis": usage.get("cost_basis", COST_BASIS),
        # The oracle's three checks, the seed's own integrity, the out-of-copy writes and the verdict they
        # add up to: a row that says `closed` says which evidence closed it (finding F2's exit-path check).
        # `axioms` is sorted here because a set is not JSON (the oracle returns the set the contract names).
        "closure": {
            **(
                {**closure, "axioms": sorted(closure["axioms"])}
                if closure.get("axioms") is not None
                else closure
            )
        },
        "proof": {
            "turns": turns,
            "input_tokens": usage.get("input", 0),
            "output_tokens": usage.get("output", 0),
            "cached_input_tokens": usage.get("cached_input", 0),
            "provider_retries": usage.get("provider_retries", 0),
            "model": usage.get("model"),
            "thinking": usage.get("thinking"),
            "resolved_model": usage.get("resolved_model"),
            # A field that exists to make a substitution visible cannot say nothing (planner's ruling):
            # the port computes this from every turn it saw, so the row states it the same way the tactic
            # rows do rather than leaving a reader to compare `resolved_model` against the selector.
            "resolvedModelIsFallback": bool(usage.get("is_fallback", False)),
            # The transport composes no prompt sections for file mode (the message is built here), so
            # the row records *our* composition: the same sections every round, plus the oracle's
            # feedback once a retry has happened.
            "prompt": {
                "sections": list(FILE_MODE_PROMPT_SECTIONS)
                + (["oracle feedback"] if rounds > 1 else [])
            },
        },
        "artifacts": {
            "proof": str(working),
            # The digest of the bytes the oracle checked — from the snapshot, never reread from the path
            # (finding: the sidecar race). `promote.py` reads exactly this field to bind an artifact to the row
            # that claims it, and the closure copy is verified against it.
            "artifact_sha256": closure_oracle.sha256_text(candidate) if candidate is not None else None,
            # Where the durable copy is, written from that same snapshot (finding F6). `route_b` writes the
            # sidecar beside it and checks this file's digest against the field above.
            "closure_copy": str(copy_path) if copy_path is not None else None,
            "omp_sessions": str(run_dir),
            "baseline": {"seed": str(seed_path), "sha256": pristine_sha, "matches": seed_matches_loaded},
        },
        "setup": {**setup, "mode": "file", "tools": DEFAULT_TOOLS},
        "error": error,
    }
