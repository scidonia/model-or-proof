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

import pathlib
import sys
import threading
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from harness import closure_oracle  # noqa: E402
from harness.closure import ProviderError, heartbeat  # noqa: E402
from harness.result import COST_BASIS, compute_basis  # noqa: E402

DEFAULT_TOOLS = "bash"



def statement_of(pristine: str, theorem: str = "mutex") -> str:
    """The seed's theorem declaration, from ``theorem`` to its assignment token.

    What the file-mode prompt shows as "the statement under test": the declaration itself, not the whole
    file — the model can read the file's definitions in its working copy, and quoting them into the
    prompt would be a second copy that could drift from the one integrity pins.
    """
    import re

    match = re.search(rf"^theorem\s+{re.escape(theorem)}\b.*?:=", pristine, re.M | re.S)
    if not match:
        return pristine.strip().splitlines()[-1] if pristine.strip() else ""
    return match.group(0).rstrip().removesuffix(":=").rstrip()


def file_prompt(working: pathlib.Path, *, statement: str, feedback: str | None = None) -> str:
    """The turn's message: the file to close, and what the last round said if this is a retry."""
    lines = [
        "The statement under test:",
        "",
        statement.strip(),
        "",
        f"Your working file: {working.name} (in the current directory).",
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


def watch_file(path: pathlib.Path, stop: threading.Event, *, interval_s: float, label: str) -> None:
    """Print the working file's size and mtime until ``stop`` (plan D26's file-mode heartbeat).

    A file-mode turn can run for minutes with nothing on the driver's side to report, so the evidence
    that the model is *working* rather than wedged is the file it is working on: a growing or rewritten
    file is progress, a file untouched for the whole turn is not.
    """
    last: tuple[int, float] | None = None
    unchanged_for = 0.0
    while not stop.wait(interval_s):
        size, mtime = _size_and_mtime(path)
        unchanged_for = 0.0 if last != (size, mtime) else unchanged_for + interval_s
        last = (size, mtime)
        if size < 0:
            heartbeat(f"file {label}: no file at {path.name} yet")
        else:
            heartbeat(
                f"file {label}: {size} bytes, {'changed' if unchanged_for == 0 else f'unchanged {unchanged_for:.0f}s'}"
            )


def transcript_records(session_dir: pathlib.Path) -> tuple[int, int]:
    """How many records the session's transcript holds, and how many bytes (plan D26).

    The tool-call record lands with the transcript, so this is the after-the-fact half of the heartbeat:
    the file watcher says the turn was alive, the transcript says what the session did.
    """
    records = 0
    size = 0
    for transcript in sorted(session_dir.glob("*.jsonl")):
        text = transcript.read_text()
        size += len(text)
        records += sum(1 for line in text.splitlines() if line.strip())
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
    text the run started from, so a reader can see *why* the verdict is what it is.
    """
    label = working.stem
    started = clock()
    heartbeat(f"phase: file session for {working.name} (tools: the model's own shell)")
    theorem = theorem or closure_oracle.theorem_name(pristine)
    pristine_sha = closure_oracle.sha256_text(pristine)

    turns = 0
    rounds = 0
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
            error = {"kind": "provider_failure", "status": failure.status, "message": failure.message}
            outcome = "error"
            break
        finally:
            stop.set()
            watcher.join(timeout=watch_interval_s + 1.0)
        turns += 1
        heartbeat(
            f"file {label}: round {rounds} ended (turn {turns}, {clock() - turn_started:.1f}s)"
        )
        records, size = transcript_records(run_dir)
        heartbeat(f"file {label}: transcript {records} record(s), {size} bytes")

        closure_result = closure_oracle.check(
            working.read_text(), pristine=pristine, package=package, theorem=theorem
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
        # The next round's feedback is what the oracle saw, verbatim where it is Lean's own words: the
        # model fixes what the check reported, not what the harness thinks of it.
        # The model gets Lean's **errors** first: that is what it can act on, and the oracle's own
        # sentences come after. `raw_tail` is deliberately not used here — its three lines are the
        # appended `#print axioms` result and the linter's notes, which is how a failing round used to be
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
        if not closure_result["elaborates"] and not errors:
            # Nothing quotable — a timeout, say. The last three lines are better than silence.
            problems.append("Lean did not elaborate the file:\n" + "\n".join(closure_result["raw_tail"]))
        if not closure_result["closed"]:
            problems.append(
                "the theorem still depends on axioms outside "
                f"{sorted(closure_oracle.ALLOWED_AXIOMS)}: {closure_result['axioms']}"
            )
        feedback = "\n\n".join(problems)
        # A round that changed nothing is still a round: the budget is the terminator, not a round count.
        heartbeat(f"file {label}: not closed yet, feeding the check back to the model")

    usage = session.usage()
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
        # The oracle's three checks, the seed's own integrity, and the verdict they add up to: a row
        # that says `closed` says which evidence closed it.
        "closure": {
            **(
                {**(closure_result or {}), "axioms": sorted(closure_result["axioms"])}
                if closure_result and closure_result.get("axioms") is not None
                else (closure_result or {})
            ),
            "seed_intact": seed_intact,
            "verdict": bool(
                closure_result and closure_oracle.verdict(closure_result, seed_intact=seed_intact)
            ),
            "rounds": rounds,
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
            # The transport composes no prompt sections for file mode (the message is built here), so
            # the row records *our* composition: the same sections every round, plus the oracle's
            # feedback once a retry has happened.
            "prompt": {
                "sections": ["specification", "statement", "working file"]
                + (["oracle feedback"] if rounds > 1 else [])
            },
        },
        "artifacts": {
            "proof": str(working),
            "omp_sessions": str(run_dir),
            "baseline": {"seed": str(seed_path), "sha256": pristine_sha, "matches": seed_intact},
        },
        "setup": {**setup, "mode": "file", "tools": DEFAULT_TOOLS},
        "error": error,
    }
