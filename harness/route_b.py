"""Route B: run one task through the closure loop and emit a result row (docs/protocol.md §8).

Mirrors ``harness.tlc_run``: one CLI, one run, one appended row — here into
``results/proof.jsonl``, through ``append_row(results_dir, "proof", row)`` (plan D8). The row is
produced by ``harness.closure.run_loop``, so every Route B row comes from one instrument; this module
adds only what the CLI knows: the prover's toolchain and the artifact's closure.

The prover is ``harness.lean_repl.LeanReplProver`` (plan step 4) and the model is
``harness.model.OmpModel`` (plan D20). The committed seed named by ``--proof`` is **immutable**:
its recorded baseline (``seeds.json`` + ``baseline/<file>``) is what each run copies to its own working
path under ``.runs/``, and that copy is the artifact the run closes (plan D15). The copy's content
**before** the run is what the artifact is diffed against afterwards, so a human-supplied declaration
marks the run ``assisted`` (plan D5; a committed seed that no longer matches its baseline is caught
separately and recorded), and the seed's imports are what the run's specification is assembled from —
the definitions and the statements of what is established, which the row records rather than claims
(plans D14/D15) — while the artifact's closure is asserted after the loop, never trusted from the
transcript (protocol §8). Every module the verdict rests on is evidenced by its source hash, the olean
it resolves to, and the ``lake build`` that produced it (plan D13).

**A run that got this far always produces a row.** Whatever ended it — the prover failing to load the
seed or run a step (D12), a mutant that closed (a rig defect), or the artifact being unreadable — the
row is appended with an ``error`` naming it and what the run spent, and the exit code is nonzero
(``EXIT_BY_ERROR_KIND``). The traceback that loses the row is the failure mode this module exists to
prevent: the row is the observation, and no path between the run and ``append_row`` may raise.

**What a run *is* gets recorded, not assumed.** The default race is the headline configuration —
``proof+refutation`` (plans D16/D17) — so the row carries the arms that ran, each arm's own turns,
tokens and dollars under one shared pool, the setup that produced it (model, thinking level, prompt
sections, refutation channel and templates) and an ``exploratory`` marking derived from that setup: a
run whose arms are not the headline ones is exploratory by construction, never pooled with the
headline by a reader's judgement. ``.runs/`` holds one invocation's working copies — swept before each
run writes its own (plan D18) and left in place afterwards, because that artifact is what
``scripts/promote.py`` promotes a closure from.
"""

from __future__ import annotations

import argparse
import os
import hashlib
import json
import re
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from harness import lean_lex, model as model_constants  # noqa: E402
from harness.closure import (  # noqa: E402
    NO_WITNESS,
    heartbeat,
    set_heartbeat_label,
    detect_assisted,
    excerpt_of,
    parse_declarations,
    run_loop,
    seed_work,
)
from harness.model import OmpModel  # noqa: E402
from harness.result import append_row  # noqa: E402

REPO = Path(__file__).resolve().parents[1]
DEFAULT_REPL_BIN = "tools/repl/.lake/build/bin/repl"
PROVENANCE = REPO / "tools" / "repl" / "PROVENANCE.md"

# D15 — the committed seed is immutable, and every run starts from it. `seeds.json` beside the seeds
# pins each seed's sha256, and `baseline/<file>` is the pristine text itself: a hash cannot restore a
# file that a legacy in-place run rewrote, and a run's copy of such a file would carry no `sorry` for
# the loop to close. Each repetition writes its working copy from the baseline into `.runs/`, inside
# the lake package (plan D2 import context) so the seed's imports still resolve, and the row records
# whether the on-disk seed still matches the record.
SEEDS_RECORD = "seeds.json"
BASELINE_DIR = "baseline"
RUNS_DIR = ".runs"

# D17 — the headline configuration is fixed and recorded; anything else is `exploratory` and never
# pooled with it. This slice's headline races both arms (plan D16), so a run that fields the proof arm
# alone — or that the operator marks by hand — is exploratory by construction rather than by promise.
HEADLINE_ARMS = "proof+refutation"

# The exit codes for a run that is not a result. The row says what happened; the exit code keeps a
# scripted run from reading it as a finished result. An unclosed artifact is recorded (1) because the
# budget was spent and the row is the outcome (plan D6); an unclean import (2), a failed package build
# (8) and an unrecorded baseline (9) are refused before anything runs, because the run's verdict would
# rest on a proof that is not there (plan D13/D15); the prover failing mid-run (3), a mutant that
# closed (4), a provider failure (5) and a seed with no goal left (7, the failure the baseline exists
# to prevent) are likewise recorded rather than raised. Timeout and success are the two normal outcomes
# and exit 0; *any* error row exits nonzero, an error kind this map does not know included.
EXIT_UNCLOSED_ARTIFACT = 1
EXIT_UNCLEAN_IMPORT = 2
EXIT_PROVER_FAILURE = 3
EXIT_MUTANT_CLOSED = 4
EXIT_PROVIDER_FAILURE = 5
EXIT_UNCLASSIFIED_ERROR = 6
EXIT_SEED_ALREADY_CLOSED = 7
EXIT_BUILD_FAILED = 8
EXIT_NO_BASELINE = 9
EXIT_RIG_REFUTATION = 10
EXIT_ARM_UNAVAILABLE = 12

# The code each recorded error earns. The row and these codes are what a scripted caller reads, so an
# error it does not know still exits nonzero rather than letting a broken run look finished.
EXIT_BY_ERROR_KIND = {
    "unclosed_artifact": EXIT_UNCLOSED_ARTIFACT,
    "artifact_unreadable": EXIT_UNCLOSED_ARTIFACT,
    "prover_failure": EXIT_PROVER_FAILURE,
    "mutant_closed": EXIT_MUTANT_CLOSED,
    "provider_failure": EXIT_PROVIDER_FAILURE,
    "seed_already_closed": EXIT_SEED_ALREADY_CLOSED,
    "rig_refutation": EXIT_RIG_REFUTATION,
    "arm_unavailable": EXIT_ARM_UNAVAILABLE,
}

# A provenance row: a table cell naming what is pinned, then the value in its backticks.
_PINNED_RE = re.compile(r"(?m)^\|\s*(?P<cell>[^|]+?)\s*\|\s*`(?P<value>[^`]+)`")

# A seed's `import` of another module: the module name, which is a path under the lake package for a
# project-local module and is skipped when it resolves to nothing there (Mathlib, Batteries, …). The
# `public`/`private` modifiers and the `all` form are Lean 4 syntax at this pin: an import a run loads
# but the guard neither resolved nor hashed would be exactly the blind spot the guard exists to close,
# so the pattern sees them (ticket P1-4).
_IMPORT_RE = re.compile(
    r"(?m)^[ \t]*(?:(?:public|private)\s+)?import\s+(?:(?P<all>all)\s+)?(?P<module>[A-Za-z_][\w'.]*)"
)


def import_statements(text: str) -> list[re.Match]:
    """A Lean module's `import` commands, modifiers and `all` included, code only.

    A line inside a comment or a string is prose, not an import (``harness.lean_lex``): a module whose
    header explains `import Mathlib` invents no module, and earns no refusal.
    """
    found: list[re.Match] = []
    index = 0
    while index < len(text):
        skipped = lean_lex.skip_noncode(text, index)
        if skipped is not None:
            index = skipped
            continue
        match = _IMPORT_RE.match(text, index)
        if match is None:
            index += 1
            continue
        found.append(match)
        index = match.end()
    return found


def load_driver():
    """The Lean prover driver — ``LeanReplProver`` and the artifact-close assertion (plan step 4).

    Imported inside the CLI rather than at module scope so that ``harness.route_b`` stays importable
    while that step is unimplemented, and so an absent driver fails as a named prerequisite instead of
    a bare import error.
    """
    try:
        from harness.lean_repl import LeanReplProver, count_unclosed
    except ModuleNotFoundError as error:
        raise SystemExit(
            f"harness.lean_repl is not implemented yet: the Lean prover driver is plan step 4 ({error})"
        ) from error
    return LeanReplProver, count_unclosed


class Refusal(Exception):
    """A run that must not start (plan D13/D15).

    Nothing was measured, so there is no row to write: the CLI reports the reason and exits with the
    code it carries. A failure *after* the run started lands a row instead — that is what the loop's
    error kinds are for — and the two must not be confused, because a refused cell is not an
    observation.
    """

    def __init__(self, code: int, message: str) -> None:
        super().__init__(message)
        self.code = code
        self.message = message


@dataclass(frozen=True)
class Baseline:
    """The committed seed a run starts from (plan D15).

    ``seed`` is the committed file the row names, ``text`` the pristine seed recorded for it,
    ``sha256`` that text's recorded hash, and ``matches`` whether the committed file on disk still
    hashes to it — the check that catches a human's invariant written into the committed seed, or a
    legacy in-place run's proof, rather than laundering it into the run.
    """

    seed: Path
    text: str
    sha256: str
    matches: bool


def run_session_dir(seed: Path, results_dir: Path, mutant: bool, repetition: int) -> Path:
    """Where this run's OMP sessions live (plans D17/D20): one directory per run, one per role.

    Run-scoped and outside the seed's package so nothing of the repository's context can leak into a
    prompt, but *inside* the run's own results directory so the transcript a row points at sits beside
    the row — and so a caller that writes its rows somewhere temporary does not scatter sessions into
    the repository. The name carries the seed and the second the run started, because a battery of
    several cases in one invocation must not let two cases share a session directory (the `--session-dir`
    is a directory, not a session: two runs in one would interleave their transcripts).
    """
    stamp = time.strftime("%Y%m%dT%H%M%S")
    name = f"{seed.stem}{'-mutant' if mutant else ''}-{stamp}-r{repetition}"
    directory = results_dir / "omp" / name
    directory.mkdir(parents=True, exist_ok=True)
    return directory


def harness_revision(seed: Path, baseline: Baseline) -> dict:
    """A digest of what this run actually is (plan D17): sources plus the data the prompt reads.

    The harness the run imports (`harness/*.py`), the examples the prompt carries, the seed, and the
    baseline record — hashed at run start. A row is then attributable even while the tree is dirty (two
    slices uncommitted), and an iteration comparison cannot silently mix code versions: the digest
    changes when any of them does.
    """
    files: dict[str, str] = {}
    for source in sorted((REPO / "harness").glob("*.py")):
        files[relative(source)] = hashlib.sha256(source.read_bytes()).hexdigest()
    for data in (model_constants.EXAMPLES_PATH, seed, seed.parent / SEEDS_RECORD):
        if data.is_file():
            files[relative(data)] = hashlib.sha256(data.read_bytes()).hexdigest()
    digest = hashlib.sha256("\n".join(f"{name} {value}" for name, value in sorted(files.items())).encode())
    return {"digest": digest.hexdigest(), "files": files}


def record_baseline(seed: Path) -> dict:
    """Pin a seed as its own baseline: the loud, explicit way to add one (plans D15/D22).

    The experiment's seeds are pinned once and never rewritten; a *new* seed — the capability battery's,
    for instance — has no record yet, and ``route_b`` refuses (exit 9) to run a seed whose provenance it
    cannot state. This is the sanctioned way to give it one: the seed's current text is written to
    ``seeds.json`` and ``baseline/<file>`` beside it, exactly as the committed seeds are recorded, so a
    later run's baseline check has something real to compare against. It returns what it wrote, and the
    caller prints it: a pin that happens quietly is a pin nobody can audit.
    """
    text = seed.read_text()
    digest = hashlib.sha256(text.encode()).hexdigest()
    record_path = seed.parent / SEEDS_RECORD
    record = json.loads(record_path.read_text()) if record_path.is_file() else {}
    record[seed.name] = digest
    record_path.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    pristine = seed.parent / BASELINE_DIR / seed.name
    pristine.parent.mkdir(parents=True, exist_ok=True)
    pristine.write_text(text)
    return {
        "seed": relative(seed),
        "sha256": digest,
        "record": relative(record_path),
        "baseline": relative(pristine),
    }


def load_baseline(seed: Path) -> Baseline:
    """The recorded baseline a run copies, or a refusal saying why there is none (plan D15).

    ``seeds.json`` beside the seeds pins each seed's sha256, and ``baseline/<file>`` is the pristine
    text. A measured run must be able to say what it started from, so a missing record, a seed the
    record does not name, a missing pristine text, or a baseline whose own text does not hash to the
    recorded value refuses the run instead of guessing.
    """
    record_path = seed.parent / SEEDS_RECORD
    if not record_path.is_file():
        raise Refusal(
            EXIT_NO_BASELINE,
            f"{record_path} is missing: a measured run starts from the committed seeds' recorded "
            "baseline (plan D15)",
        )
    try:
        record = json.loads(record_path.read_text())
    except (OSError, json.JSONDecodeError) as failure:
        raise Refusal(
            EXIT_NO_BASELINE, f"{record_path} cannot be read as the seed record: {failure}"
        ) from failure
    if not isinstance(record, dict) or not isinstance(record.get(seed.name), str):
        raise Refusal(
            EXIT_NO_BASELINE,
            f"{record_path} does not record {seed.name}: the baseline this run must start from is "
            "unrecorded (plan D15)",
        )
    pristine = seed.parent / BASELINE_DIR / seed.name
    if not pristine.is_file():
        raise Refusal(
            EXIT_NO_BASELINE,
            f"{pristine} is missing: the recorded seed's pristine text is what a run copies, because "
            "a hash cannot restore a file (plan D15)",
        )
    text = pristine.read_text()
    digest = hashlib.sha256(text.encode()).hexdigest()
    if digest != record[seed.name]:
        raise Refusal(
            EXIT_NO_BASELINE,
            f"{pristine} hashes to {digest}, not the recorded {record[seed.name]}: the baseline is "
            "not what the record says it is (plan D15)",
        )
    live = seed.read_text() if seed.is_file() else ""
    return Baseline(seed=seed, text=text, sha256=digest, matches=hashlib.sha256(live.encode()).hexdigest() == digest)


def sweep_working_copies(seed: Path) -> list[Path]:
    """Discard the previous runs' working copies before this invocation writes its own (plan D18).

    ``.runs/`` is a scratch area: every repetition writes its copy from the recorded baseline, so a
    stale copy could only be mistaken for this run's artifact. Sweeping at the *start* of an invocation
    keeps the directory at one invocation's copies and nothing accumulates across runs, while leaving
    the run that just finished its artifact — which is what ``scripts/promote.py`` promotes a closure
    from, and what a terminal promotion step needs to still be there.
    """
    runs = seed.parent / RUNS_DIR
    if not runs.is_dir():
        return []
    swept = sorted(runs.glob(f"{seed.stem}-r*{seed.suffix}"))
    for stale in swept:
        stale.unlink()
    return swept


def setup_of(arms: str) -> dict:
    """The configuration a row records (plan D17): what makes iterated runs distinguishable.

    The model selector, thinking level, temperature, token cap and prompt sections are
    ``harness.model``'s single source of truth, and the refutation arm's channel, template and
    instruction are that client's too — ``None`` until that side states them, because a row records the
    setup that produced it and a setup this harness cannot name is exactly what a reader needs to see
    rather than a plausible-looking stand-in. The few-shot examples are versioned and recorded by path
    and hash (plan D19), so a prompt change is visible in a row instead of implied by it. The arm keys
    are the loop's and are added by ``run_loop``.
    """
    return {
        "model": model_constants.MODEL_SELECTOR,
        "thinking": model_constants.THINKING_LEVEL,
        # The call shape itself (plan D20): the transport, its version and the flags every role's
        # session starts with, so a row is attributable to the exact invocation rather than to a model
        # name and a hope. `temperature`/`max_tokens` are absent because the harness no longer sets
        # them — OMP owns the call shape — and the row reports them as null for the same reason.
        "omp": model_constants.omp_invocation(),
        "prompt": {"sections": list(model_constants.PROMPT_SECTIONS)},
        "examples": examples_setup(),
        "refutation": {
            "channel": "cmd",
            "template": getattr(model_constants, "REFUTATION_TEMPLATE", None),
            "instruction": getattr(model_constants, "REFUTATION_INSTRUCTION", None),
            # The vocabulary the arm answers in (plan D16/D17): the sentinel that ends it when there is
            # no witness to find, which is the expected answer on a true statement.
            "no_witness": NO_WITNESS,
        },
    }


def examples_setup() -> dict:
    """The few-shot examples the prompt carries, as the setup records them (plan D19).

    The version the client reads and the file's own sha256: the hash is the evidence a reader checks
    when asking *which* examples a run was shown, and the version is what a plan or a README can name.
    A missing file is recorded as such (``sha256: None``) rather than raising here — the client is what
    requires it, and it reads the file when a run is constructed.
    """
    path = model_constants.EXAMPLES_PATH
    try:
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError:
        digest = None
    return {
        "version": model_constants.EXAMPLES_VERSION,
        "path": relative(path),
        "sha256": digest,
    }


def working_copy(baseline: Baseline, repetition: int) -> Path:
    """The per-run working copy the driver works on, written from the baseline (plan D15).

    Inside the lake package — ``.runs/`` beside the seeds — so the seed's imports still resolve (plan
    D2), and written fresh before every repetition, so `--reps N` starts each repetition from the
    committed statement rather than from the previous repetition's proof, and a re-run of an
    already-closed cell starts fresh too.
    """
    runs = baseline.seed.parent / RUNS_DIR
    runs.mkdir(parents=True, exist_ok=True)
    copy = runs / f"{baseline.seed.stem}-r{repetition}{baseline.seed.suffix}"
    copy.write_text(baseline.text)
    return copy


def run_lake_build(root: Path) -> dict:
    """Build the seed's package and report how it went, refusing a build that failed (plan D13).

    Route B's verdict rests on the *olean* the repl resolves an import to, not on that import's source
    text: a source that is clean today can sit beside an olean built from the version that still ended
    in ``sorry``. The build is run before the measured runs and is not part of their wall-clock; a
    non-zero exit refuses the cell, because the run never started and there is nothing to measure. This
    is a stubbable seam: no scenario runs ``lake``.
    """
    cmd = ["lake", "build"]
    heartbeat(f"phase: lake build in {root}")
    started = time.monotonic()
    completed = subprocess.run(cmd, cwd=str(root), capture_output=True, text=True)
    result = {
        "cmd": cmd,
        "exit": completed.returncode,
        "seconds": round(time.monotonic() - started, 3),
    }
    if completed.returncode != 0:
        output = "\n".join((completed.stdout + completed.stderr).strip().splitlines()[-20:])
        raise Refusal(
            EXIT_BUILD_FAILED,
            f"{' '.join(cmd)} in {root} exited {completed.returncode}: the oleans a run would load "
            f"are not what the sources say (plan D13)\n{output}",
        )
    return result


def module_name(source: Path, root: Path) -> str:
    """The Lean module a project-local file defines: its path under the package, dotted (plan D13)."""
    try:
        inside = source.resolve().relative_to(root.resolve())
    except ValueError:
        inside = Path(source.name)
    return str(inside.with_suffix("")).replace("/", ".")


def olean_evidence(source: Path, root: Path, build: dict) -> dict:
    """One module's evidence: the source hash, the olean it resolves to, and the build (plan D13).

    `lake env repl` loads the *olean*, so "the olean was current" has to be evidence rather than
    assumption: the row carries the olean's own sha256 and mtime and whether it is there at all, beside
    the source hash and the ``lake build`` that produced it.
    """
    try:
        digest = hashlib.sha256(source.read_bytes()).hexdigest()
    except OSError:
        digest = None
    olean = root / ".lake" / "build" / "lib" / "lean" / f"{module_name(source, root)}.olean"
    if olean.is_file():
        olean_entry = {
            "path": relative(olean),
            "sha256": hashlib.sha256(olean.read_bytes()).hexdigest(),
            "mtime": olean.stat().st_mtime,
            "status": "present",
        }
    else:
        olean_entry = {"path": relative(olean), "sha256": None, "mtime": None, "status": "missing"}
    return {"sha256": digest, "olean": olean_entry, "lake_build": build}


def guard_imports(copy: Path, count_unclosed) -> list[Path]:
    """The import-clean guard (plan D13): refuse when an imported source still carries a hole.

    A run closes a theorem over the repl's verdict on the command in front of it, and a ``sorry``
    inside an imported theorem's value is invisible to that verdict: a tier-1 ``success`` could
    otherwise rest on the imported ``mutex`` still being ``sorry``-proved. The copy's project-local
    imports are resolved and checked here, on the same working copy the driver will load.
    """
    sources = local_import_sources(copy)
    for source in sources:
        unclosed = count_unclosed(source.read_text())
        if unclosed:
            raise Refusal(
                EXIT_UNCLEAN_IMPORT,
                f"{relative(source)} still contains {unclosed} sorry/Admitted/axiom: refusing to run "
                f"{relative(copy)}, whose proof would rest on it (plan D13)",
            )
    return sources


def import_evidence(seed: Path, sources: Sequence[Path], root: Path, build: dict) -> dict:
    """The evidence a run's verdict rests on, per module: the seed's own module and its imports.

    Keyed by the module's source path, like the source-only hashes it replaces, and covering the
    seed's own module as well as what it imports: the tier-1 run loads the tier-2 result as an olean,
    so a stale ``TokenRing.olean`` matters exactly as much as a stale import (plan D13).
    """
    return {
        relative(source): olean_evidence(source, root, build) for source in (seed, *sources)
    }


def seed_drift(baseline: Baseline) -> dict | None:
    """What a human changed in the committed seed since it was recorded (plan D15, ticket P1-2).

    ``None`` when the committed seed still hashes to its record: there is nothing to diff. Otherwise
    ``detect_assisted``'s verdict on (recorded text, committed text) — the declarations the committed
    seed gained, changed or lost, of *any* kind, named. That is the seed-side counterpart of the
    artifact diff: a `def`/`notation`/`abbrev`/`instance` a human slipped in beside the goal is named in
    the row's ``auxiliary_invariants`` and marks the run assisted, exactly as an added declaration in
    the artifact does. A record that has been *re-pinned* to the changed text is indistinguishable from
    a seed that always read that way — the record is ground truth, and every definition of the model
    legitimately lives there — so the diff is only meaningful while the two disagree.
    """
    if baseline.matches:
        return None
    live = baseline.seed.read_text() if baseline.seed.is_file() else ""
    # `human=True`: what the committed seed gained is a human's edit — the loop never writes that file —
    # so an added declaration there is human work, unlike an addition in the run's own artifact (D19).
    return detect_assisted(baseline.text, live, human=True)


def assisted_reasons(
    baseline: Baseline, seed_text: str, shown: dict, drift: dict | None = None
) -> list[str]:
    """Why a run is assisted before it takes a step (plan D15, protocol §11 decision 5).

    Three families, none of which the artifact diff can see because they are already in the seed the
    loop receives: the committed seed differing from its recorded baseline (a human's invariant, or a
    legacy in-place proof — named declaration by declaration when ``drift`` is given), human work inside
    the recorded seed beyond the statement under test (``seed_work``), and a declaration the excerpt
    would not show because it establishes nothing — including an ``example``, whose unnamed claim is
    human work (P1-2).
    """
    reasons: list[str] = []
    if drift is not None:
        changed = (
            drift["auxiliary_invariants"] + drift["changed_declarations"] + drift["missing_declarations"]
        )
        reasons.append(
            f"{relative(baseline.seed)} does not match its recorded baseline {baseline.sha256}: "
            f"{', '.join(changed) if changed else 'its text'} differs — the run starts from the recorded "
            "text, and what the committed seed changed is named in the row's declaration lists"
        )
    elif not baseline.matches:
        reasons.append(
            f"{relative(baseline.seed)} does not match its recorded baseline {baseline.sha256}: the "
            "committed seed has been edited since it was pinned, and the run starts from the recorded "
            "text, not from the edit"
        )
    reasons.extend(seed_work(seed_text))
    for source in shown.get("imports", []):
        for declaration in source["declarations"]:
            label = declaration["name"] or f"<{declaration['kind']}>"
            if declaration["shown"] is None:
                reasons.append(
                    f"{source['path']}: {declaration['kind']} {label} not shown "
                    f"({declaration.get('reason', 'nothing established')})"
                )
            elif declaration["kind"] == "example":
                reasons.append(
                    f"{source['path']}: example shown to the model — an unnamed claim is human work"
                )
    return reasons


def toolchain_of(proof: Path) -> str | None:
    """The Lean version pinned beside the artifact, from the nearest ``lean-toolchain`` (plan step 1)."""
    for directory in proof.resolve().parents:
        candidate = directory / "lean-toolchain"
        if candidate.is_file():
            return candidate.read_text().strip()
    return None


def project_root(proof: Path) -> Path:
    """The lake package the seed lives in: where a sibling ``import`` resolves.

    The same rule the driver's process uses to find the repl's working directory (plan D2), so the
    modules a run is shown are the ones Lean would have loaded for it.
    """
    for directory in proof.resolve().parents:
        if (directory / "lakefile.toml").is_file() or (directory / "lakefile.lean").is_file():
            return directory
    return proof.resolve().parent


def local_import_sources(proof: Path) -> list[Path]:
    """The project-local modules the seed imports, transitively, in the order they are reached.

    An ``import`` that resolves to no file under the package — ``Mathlib``, ``Batteries`` — is not the
    project's own source and has no specification to show; only what the seed's own package states is
    part of the run's specification (plan D14).

    ``import all`` is refused rather than resolved: it loads a module *and* everything it publicly
    re-exports, so there is no bounded module set to resolve, hash or check for holes — the run's proof
    could rest on sources this guard never read, which is what plan D13 refuses (ticket P1-4).
    """
    root = project_root(proof)
    found: list[Path] = []
    seen = {proof.resolve()}
    pending = [proof.resolve()]
    while pending:
        source = pending.pop(0)
        for match in import_statements(source.read_text()):
            if match.group("all"):
                raise Refusal(
                    EXIT_UNCLEAN_IMPORT,
                    f"{relative(source)} imports `all {match.group('module')}`: `import all` loads an "
                    "unbounded module set, so the run's proof could rest on sources this guard never "
                    "read (plan D13)",
                )
            module = match.group("module")
            candidate = (root / module.replace(".", "/")).with_suffix(".lean")
            if candidate in seen or not candidate.is_file():
                continue
            seen.add(candidate)
            found.append(candidate)
            pending.append(candidate)
    return found


def specification_of(proof: Path) -> tuple[str, dict]:
    """The specification a run is shown, with an account of what it showed (plan D14/D15).

    The seed is shown **verbatim** — it is what the run closes, statement and definitions exactly as
    the human wrote it — and each project-local import follows, reduced to its definitions and the
    statements of the proofs it completed: the model can use the imported theorem a tier-1 corollary
    instantiates, while no proof body and no statement nobody established enters the prompt. Mathlib is
    not the project's own source and is not shown; a run against the tier-2 seed states its own
    definitions, so only its text is shown.

    The second element is the account the row records as ``prompt.shown``: per source, what was shown
    and how, so that "no helper-lemma statement was shown" is something a reader checks in the row
    rather than a promise the row makes (P1-2). The seed's entry is ``how: "verbatim"`` and every
    declaration in it is ``shown: "body"`` — the file is shown as written, the statement under test
    together with the placeholder it carries — while an import's entry is ``how: "excerpt"`` and each
    declaration says whether its body or only its statement was shown, or that it was not shown at all
    and why.
    """
    text = proof.read_text().strip()
    shown = {
        "seed": {
            "path": relative(proof),
            "how": "verbatim",
            "declarations": [
                {"name": declaration.name, "kind": declaration.kind, "shown": "body"}
                for declaration in parse_declarations(text)
            ],
        },
        "imports": [],
    }
    parts = [text]
    for source in local_import_sources(proof):
        excerpt, declarations = excerpt_of(source.read_text())
        parts.append(f"-- {relative(source)}, imported by the seed:\n\n{excerpt}")
        shown["imports"].append(
            {"path": relative(source), "how": "excerpt", "declarations": declarations}
        )
    return "\n\n".join(part for part in parts if part), shown


def relative(path: Path) -> str:
    return str(path.relative_to(REPO)) if path.is_relative_to(REPO) else str(path)


def repl_identity(provenance: Path = PROVENANCE) -> dict:
    """The repl's pinned revision — commit and toolchain — from its provenance record (plan D2).

    A row names a prover by revision, not by path (protocol §4.4): the binary is a build artifact that
    can be rebuilt, while the commit is what says which sources produced the goal states the model saw.
    A provenance record that stops pinning either is a defect rather than a default, so it raises
    instead of writing a row whose prover is unidentified.
    """
    if not provenance.is_file():
        raise SystemExit(f"{provenance} is missing: the repl's revision is unrecorded (plan D2)")
    cells = {
        match.group("cell"): match.group("value") for match in _PINNED_RE.finditer(provenance.read_text())
    }
    unrecorded = [cell for cell in ("Commit", "Toolchain") if cell not in cells]
    if unrecorded:
        raise SystemExit(
            f"{provenance} does not pin {', '.join(unrecorded)}: the repl's revision is unrecorded"
        )
    return {"commit": cells["Commit"], "toolchain": cells["Toolchain"]}


def write_closure_sidecar(rows_path: Path, row: dict, *, task: str, results_dir: Path) -> Path | None:
    """Copy a closure's bytes out of `.runs/` and write the sidecar that binds them (finding F6).

    `.runs/` is gitignored and swept at the next invocation's start, so a `closed` row whose artifact is
    gone cannot be reverified — and a row claiming closure whose artifact is gone is close to unfalsifiable.
    The checked bytes are copied to `results/closures/<task>/<token>.lean`, task and token being what the row
    already names, and a sidecar beside them states the row's address, both digests and the verdict, so the
    closure can be checked from the copy and the record without trusting either alone.

    A copy whose digest disagrees with the one the row recorded is reported **loudly**: that means the file
    changed between the oracle's check and this copy, and the pair is not evidence of anything.
    """
    if row.get("outcome") != "closed":
        return None
    # The copy itself is written by `file_mode` **from its one snapshot** of the candidate (finding: the
    # sidecar race), so this sidecar verifies that copy rather than making a fresh one from a path that may
    # have been swapped since the oracle read it. A missing copy is loud: a closed row with no durable
    # artifact is the thing F6 exists to prevent.
    recorded = row["artifacts"].get("artifact_sha256")
    copy_path = Path(row["artifacts"].get("closure_copy") or "")
    if not copy_path.is_file():
        print(
            f"LOUD: the row says closed on {row['artifacts'].get('proof')} but no closure copy exists at "
            f"{copy_path!s}; the artifact is not durable and the row is not evidence"
        )
        return None
    copied = hashlib.sha256(copy_path.read_bytes()).hexdigest()
    # A row that records *no* digest is not a disagreement — it predates the field (the file-mode row that
    # prompted this, written before `artifact_sha256` existed). Only a digest that differs is a finding.
    agrees = None if recorded is None else copied == recorded
    sidecar = {
        "row": f"{relative(rows_path)}:{len(rows_path.read_text().splitlines())}",
        "task": task,
        "tier": row.get("tier"),
        "mode": row.get("mode"),
        "omp_sessions": row["artifacts"]["omp_sessions"],
        "artifact": relative(copy_path),
        "artifact_sha256": copied,
        "row_artifact_sha256": recorded,
        "digests_agree": agrees,
        "pristine_sha256": row["artifacts"]["baseline"]["sha256"],
        # The row's closure block *whole*, not a fixed subset: the sidecar is the durable record, and a key
        # list here is how `module` and `theorem` went missing from it the moment they were added to the row
        # — the same "a value that has to be maintained in two places agrees until it does not" shape as the
        # `"mutex"` default. The row's closure is already JSON-clean (its axioms are a sorted list).
        "closure": row["closure"],
    }
    sidecar_path = copy_path.with_suffix(".json")
    sidecar_path.write_text(json.dumps(sidecar, indent=2, sort_keys=True) + "\n")
    if agrees is False:
        print(
            f"LOUD: the closure copy's digest {copied} does not match the {recorded} the row records; "
            "the artifact changed after it was checked, and the pair is not evidence"
        )
    elif recorded is None:
        # Not a mismatch, but worth saying: this row predates `artifact_sha256`, so the copy, its digest and
        # the oracle's re-verification are the evidence rather than the row's own field.
        print(
            f"note: the row records no artifact digest (it predates the field); the copy's digest {copied} "
            "and the recorded closure verdict are the evidence"
        )
    return sidecar_path


def run_file_mode(
    args, *, task: str, results_dir: Path, seed: Path, baseline: Baseline, cap_s: float, cap_usd: float
) -> int:
    """One file-mode run per repetition: a tool-using session and the closure oracle (plan D26).

    The working copy is the unit of work, as in tactic mode, but nothing is spliced into a proof state:
    the session is given a shell and the file, and the oracle's three checks - integrity against the
    *recorded* seed, elaboration, and the axiom set - decide whether the run closed. The row records
    `mode: "file"` and the whole `closure` object, so a reader sees the evidence, not just a verdict.
    """
    from harness import file_mode, model  # file mode pulls in the transport only when it is used

    swept = sweep_working_copies(seed)
    if swept:
        heartbeat(f"phase: swept {len(swept)} stale working copy/copies of {relative(seed)}")
    status = 0
    for repetition in range(1, args.reps + 1):
        copy = working_copy(baseline, repetition)
        run_dir = run_session_dir(seed, results_dir, args.mutant, repetition)
        heartbeat(f"phase: run {relative(seed)} r{repetition} (mode: file)")
        # The actual file-mode invocation (finding F7): one role, the working copy's own directory, the
        # file-mode message's sections and the tool flags - not the tactic-mode setup, whose
        # `proof`/`refutation`/`plan` roles, temporary cwd and refutation configuration describe a session
        # that never ran. Built per repetition because the working copy's directory is per repetition.
        setup = {
            "model": model_constants.MODEL_SELECTOR,
            "thinking": model_constants.THINKING_LEVEL,
            "mode": "file",
            "tier": args.tier,
            "role": "file",
            "tools": file_mode.DEFAULT_TOOLS,
            "cwd": relative(copy.parent),
            "prompt": {"sections": list(file_mode.FILE_MODE_PROMPT_SECTIONS)},
            "system_prompt": "harness.model.FILE_MODE_SYSTEM_PROMPT",
            # The nested invocation as it actually ran: one role, the working copy's directory. Without these
            # the block would record the tactic roles and a temporary cwd for a session that never ran
            # (finding F7's remainder).
            "omp": model.omp_invocation(
                tools=file_mode.DEFAULT_TOOLS,
                roles=("file",),
                cwd=relative(copy.parent),
                # File mode has no per-turn cut (D24 as re-ruled): the recorded bound is the provider
                # client's, and `turn_deadline_s=None` says so rather than leaving 360 in the record.
                turn_deadline_s=None,
                provider_timeout_s=model.PROVIDER_TIMEOUT_S,
            ),
        }
        session = model.OmpFileModel(
            session_root=run_dir,
            cwd=copy.parent,
            timeout_s=model.PROVIDER_TIMEOUT_S,
            startup_timeout_s=model.STARTUP_TIMEOUT_S,
        )
        # The host load at the run's start (planner's ruling): paired in `append_row` with the load at
        # its end, so a row taken under contention says so instead of reading as ordinary spread.
        load_before = [round(value, 2) for value in os.getloadavg()]
        try:
            row = file_mode.run_file(
                session,
                task=task,
                tier=args.tier,
                repetition=repetition,
                mutant=args.mutant,
                working=copy,
                run_dir=run_dir,
                seed_path=seed,
                package=seed.parent,
                pristine=baseline.text,
                cap_s=cap_s,
                cap_usd=cap_usd,
                setup=setup,
                statement=file_mode.statement_of(baseline.text),
            )
        finally:
            session.close()
        rows_path = append_row(results_dir, "proof", row, load_before=load_before)
        # F6: the closure's bytes and the sidecar that binds them to this row, written the moment the row
        # exists — before anything can sweep `.runs/`.
        sidecar = write_closure_sidecar(rows_path, row, task=task, results_dir=results_dir)
        if sidecar is not None:
            heartbeat(f"phase: closure copy {relative(sidecar)}")
        closure = row["closure"]
        # `.get` throughout: a provider failure ends the run *before* the oracle ever runs, so its row has no
        # `integrity`/`elaborates`/`axioms` — and a summary that assumed them crashed with a KeyError after
        # the row was already appended, turning a recorded outcome into a traceback (the P1 invariant).
        print(
            f"file mode r{repetition}: {row['outcome']} in {row['wall_clock_s']}s "
            f"(rounds {closure['rounds']}, turns {row['proof']['turns']}, "
            f"cost ${row['cost_usd']:.4f}) integrity={closure.get('integrity')} "
            f"elaborates={closure.get('elaborates')} axioms={closure.get('axioms')} "
            f"seed_intact={closure.get('seed_intact')} "
            f"outside_events={len(closure.get('outside_events') or [])} "
            f"watch_blind={closure.get('watch_blind')}"
        )
        if row["outcome"] != "closed":
            status = EXIT_UNCLOSED_ARTIFACT
    return status


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="harness.route_b")
    parser.add_argument(
        "--task",
        help="task manifest under tasks/ (required unless --record-baseline)",
    )
    parser.add_argument(
        "--proof",
        required=True,
        help=(
            "the committed seed whose recorded baseline the run copies; the seed itself is never "
            "written (plan D15)"
        ),
    )
    parser.add_argument("--mutant", action="store_true", help="run the task's mutant, which must not close")
    parser.add_argument(
        "--tier", type=int, default=2, choices=(1, 2), help="2 = the general theorem, 1 = the N0 corollary"
    )
    parser.add_argument(
        "--param-N",
        type=int,
        default=None,
        help="the instance the run is stated at (default: the manifest's N0 for tier 1)",
    )
    parser.add_argument("--reps", type=int, default=1)
    parser.add_argument(
        "--mode",
        default="tactic",
        choices=("tactic", "file"),
        help=(
            "how the proof is closed (plan D26): `tactic` (one tactic per turn, driven by the loop) or "
            "`file` (a tool-using session edits the working copy; the closure oracle decides). The two "
            "are different configurations and their rows are never pooled."
        ),
    )
    parser.add_argument(
        "--arms",
        default=HEADLINE_ARMS,
        choices=("proof", HEADLINE_ARMS),
        help=(
            "the race to field: the proof arm alone, or both arms under one shared budget "
            f"(plan D16); the headline configuration is {HEADLINE_ARMS}"
        ),
    )
    parser.add_argument(
        "--exploratory",
        action="store_true",
        help="mark the row exploratory (plan D17): a setup that is not the headline one, never pooled",
    )
    parser.add_argument(
        "--record-baseline",
        action="store_true",
        help=(
            "pin --proof as its own baseline (seeds.json + baseline/<file>) and exit: the explicit way "
            "to record a new seed, printing exactly what it wrote (plan D15)"
        ),
    )
    parser.add_argument("--results", help="the results directory (required unless --record-baseline)")
    parser.add_argument("--cap-s", type=float, default=None)
    parser.add_argument("--cap-usd", type=float, default=None)
    parser.add_argument("--repl-bin", default=DEFAULT_REPL_BIN, help="lean-repl executable")
    args = parser.parse_args(argv)

    if args.record_baseline:
        # No run and no row: the seed is pinned and the tool says what it wrote, loudly enough to audit.
        # Nothing about the refusal to run an unrecorded seed changes — this is how a seed stops being
        # unrecorded.
        recorded = record_baseline(Path(args.proof))
        print(
            "recorded {seed} as its own baseline: sha256 {sha256}, record {record}, pristine text "
            "{baseline}".format(**recorded)
        )
        return 0
    unnamed = [name for name, value in (("--task", args.task), ("--results", args.results)) if not value]
    if unnamed:
        parser.error(f"{' and '.join(unnamed)} required for a run")

    LeanReplProver, count_unclosed = load_driver()

    manifest = json.loads(Path(args.task).read_text())
    task = manifest["name"]
    results_dir = Path(args.results)
    seed = Path(args.proof)
    repl_bin = Path(args.repl_bin)
    cap_s = args.cap_s if args.cap_s is not None else float(manifest["budgets"]["wall_clock_s"])
    cap_usd = args.cap_usd if args.cap_usd is not None else float(manifest["budgets"]["usd"])
    param_N = (
        args.param_N
        if args.param_N is not None
        else (manifest.get("n0") if args.tier == 1 else None)
    )
    exit_code = 0

    try:
        # D15 — what the run starts from, before anything is measured: the committed seed's recorded
        # baseline, and its package. Both refusals below happen before a turn, so there is no row:
        # nothing was measured, and a refused cell is not an observation.
        baseline = load_baseline(seed)
        # The pristine baseline is immutable (the planner's ruling): `promote.py` rewrites the seed for tier 1
        # but never re-pins `baseline/<file>`, so every run re-seeds from the `sorry` text. If a baseline ever
        # does arrive closed, that is a defect in the rig and is refused - before either mode, so both read
        # one sentence - never reported as a zero-turn "closed". The wording is the driver's own for a closed
        # seed, so a reader who meets it in file mode recognises the rule rather than a new one.
        if count_unclosed(baseline.text) == 0:
            print(
                f"{relative(seed.parent / BASELINE_DIR / seed.name)} carries no unclosed "
                "goal: a measured run starts from the recorded baseline, never from a file a previous run "
                "rewrote (plans D15/D26)",
                file=sys.stderr,
            )
            return EXIT_SEED_ALREADY_CLOSED
        if args.mode == "file":
            # File mode: the same working copy and the same recorded baseline, but the proof is the
            # session's to write and the oracle's to check (plan D26) - a different instrument, so a
            # different run path rather than a branch inside the tactic loop.
            return run_file_mode(
                args,
                task=task,
                results_dir=results_dir,
                seed=seed,
                baseline=baseline,
                cap_s=cap_s,
                cap_usd=cap_usd,
            )
        root = project_root(seed)
        # D13 — the build whose oleans the run will load, run once and outside the measured wall-clock;
        # a build that fails means the oleans are not what the sources say, so nothing is measured.
        build = run_lake_build(root)
        tool = {
            "name": "lean",
            "toolchain": toolchain_of(seed),
            "repl": {**repl_identity(), "binary": relative(repl_bin)},
        }
        negative_control = (
            {
                "mutant": seed.name,
                # A mutant is expected to be *refuted* when the refutation arm races (plan D16: an
                # informative success, not a budget burn); with the proof arm alone the best the rig can
                # show is that the loop never closed it, which is what the pre-D16 control claimed.
                "expected": "refuted" if args.arms != "proof" else "fail_to_close",
                "observed": None,
            }
            if args.mutant
            else None
        )
        # D16/D17 — the race this invocation fields, and the setup it records. A setup that is not the
        # headline one is exploratory by construction rather than by promise: the row carries the arm
        # configuration, so the marking is derived from what ran.
        exploratory = bool(args.exploratory) or args.arms != HEADLINE_ARMS
        setup = setup_of(args.arms)
        # D17: what this run *is* — the harness sources it imports and the data its prompt reads,
        # digested at run start — so a dirty tree cannot make two rows silently incomparable.
        setup["harness_revision"] = harness_revision(seed, baseline)
        # D18 — one invocation's working copies, never a pile: the previous runs' copies go before this
        # invocation writes its own, and the artifact of the run that just finished stays for the
        # operator to promote (scripts/promote.py).
        sweep_working_copies(seed)

        for repetition in range(1, args.reps + 1):
            # A fresh working copy from the baseline: the driver works here, the artifact is this file,
            # and the committed seed is never written (plan D15).
            # The heartbeat's per-run boundary (plan D24): with several cases or repetitions in one
            # invocation, stderr says which one is running.
            # Every line this process prints is this run's (plan D25): a parallel battery reads four
            # interleaved streams, and the label is what tells them apart.
            set_heartbeat_label(f"{seed.stem}{'-mutant' if args.mutant else ''}")
            heartbeat(f"phase: run {relative(seed)} r{repetition}")
            copy = working_copy(baseline, repetition)
            seed_text = copy.read_text()
            # D13, on the same copy the driver loads: an import that still carries a hole refuses the
            # run outright — no row, since no run happened — and every module the verdict rests on is
            # evidenced by its source hash, the olean it resolves to, and the build that made it.
            sources = guard_imports(copy, count_unclosed)
            imports = import_evidence(seed, sources, root, build)
            # The specification the run is shown is fixed here, from the copy as it stands before the
            # first tactic (plan D14): the driver rewrites the artifact when a proof closes, and the
            # model must not be shown the proof it is being asked for. Its account says what was shown
            # (P1-2), and human work inside it marks the run assisted before the loop runs (D15).
            specification, shown = specification_of(copy)
            drift = seed_drift(baseline)
            assisted_before = assisted_reasons(baseline, seed_text, shown, drift)
            # This run's OMP sessions (plans D17/D20): one directory per role, run-scoped and
            # persisted, so OMP's own transcript is the run's per-turn record. The client owns the
            # processes; the row owns the paths and ids.
            sessions = run_session_dir(seed, results_dir, args.mutant, repetition)
            model_client = OmpModel(specification=specification, session_root=sessions)
            # As above: the run's starting load, paired with the ending one in `append_row`.
            load_before = [round(value, 2) for value in os.getloadavg()]
            row = run_loop(
                # `mutant` reaches the driver as well as the loop: a run that closed a false statement
                # must not leave the verdict spliced into the copy, so the driver refuses to write it
                # (plan D7).
                LeanReplProver(copy, [args.repl_bin], mutant=args.mutant),
                model_client,
                task=task,
                mode=args.mode,
                param_N=param_N,
                tier=args.tier,
                repetition=repetition,
                cap_s=cap_s,
                cap_usd=cap_usd,
                mutant=args.mutant,
                seed_text=seed_text,
                artifact_path=copy,
                assisted_before=assisted_before,
                seed_diff_before=drift,
                arms=args.arms,
                setup=setup,
                exploratory=exploratory,
            )
            row["tool"] = tool
            # The artifact is the working copy the driver wrote; the seed it started from, the baseline
            # that seed is recorded against, and the modules the verdict rests on are the evidence
            # beside it (plans D5/D13/D15). `artifact_sha256` is filled in below from the same bytes the
            # closure check reads: it is what a later promotion verifies against, because a human can
            # touch the tree between a run and its promotion (plan D19) and the row is the run's own
            # record of what the artifact was.
            row["artifacts"] = {
                "proof": relative(copy),
                "seed": relative(seed),
                "baseline": {
                    "file": relative(seed.parent / SEEDS_RECORD),
                    "sha256": baseline.sha256,
                    "matches": baseline.matches,
                },
                "imports": imports,
                "artifact_sha256": None,
                # This run's OMP session directory (plan D17): the transcripts are OMP's own record of
                # every turn, so a run is watchable while it is happening and traceable afterwards.
                "omp_sessions": relative(sessions),
            }
            # The transport's account of the sessions it ran: id, transcript file, the model and
            # thinking level it reports, and the system prompt it actually sent (digested, with
            # whatever OMP added beyond ours quoted) — so cost is keyed to a session id and the run's
            # condition is evidence rather than intent (plans D17/D20).
            row["setup"]["omp"] = {**row["setup"]["omp"], "roles": model_client.identity()}
            for identity in row["setup"]["omp"]["roles"].values():
                # Rows name paths relative to the repository, like every other artifact path.
                identity["session_dir"] = relative(Path(identity["session_dir"]))
            row["prompt"] = {**row["prompt"], "shown": shown}
            if negative_control is not None:
                negative_control = {**negative_control, "observed": row["mutant"]}
            row["negative_control"] = negative_control
            # The artifact's closure is asserted here, never trusted from the prover's transcript (§8):
            # a run whose artifact still carries sorry/Admitted/axiom is not a success. The verdict goes
            # into the row — naming the count and the artifact that carries them, which stays where it
            # was written — and into the exit code, so a scripted run cannot read it as a finished
            # result (plan D6: an outcome, never an exception that loses the row). The guard is
            # evaluated for every run, the mutant included, and the count is recorded even when it
            # cannot flip the outcome: it is the evidence behind a rig-defect row as much as behind a
            # success.
            try:
                data = copy.read_bytes()
                artifact_text = data.decode()
            except (OSError, UnicodeDecodeError) as failure:
                # The check cannot run at all, so nothing clears this run either: the row is written
                # with the verdict and the artifact's hash absent (null) rather than assumed, and the
                # run is loud. A run that already ended in error keeps the error that ended it — that is
                # the cause the reader needs — and only a run that would otherwise read as finished
                # takes this one.
                row["proof"]["artifact_unclosed_goals"] = None
                if row["error"] is None:
                    row["outcome"] = "error"
                    row["error"] = {
                        "kind": "artifact_unreadable",
                        "message": f"could not read {relative(copy)} to assert its closure: {failure}",
                    }
            else:
                # One read for both: the hash and the closure verdict describe the same bytes, so
                # nothing can change between them.
                row["artifacts"]["artifact_sha256"] = hashlib.sha256(data).hexdigest()
                unclosed = count_unclosed(artifact_text)
                row["proof"]["artifact_unclosed_goals"] = unclosed
                if row["outcome"] == "success" and unclosed:
                    row["outcome"] = "error"
                    row["error"] = {
                        "kind": "unclosed_artifact",
                        "unclosed_goals": unclosed,
                        "message": (
                            f"the prover reported no unclosed goals but {relative(copy)} still "
                            f"contains {unclosed} sorry/Admitted/axiom"
                        ),
                    }
            if row["error"] is not None:
                # The row is what happened; this is how loudly it says so. A run that ended in error
                # did not produce a result, whatever the row's numbers are — an error kind with no code
                # of its own included, which is why the fallback is nonzero too.
                exit_code = max(
                    exit_code,
                    EXIT_BY_ERROR_KIND.get(row["error"]["kind"], EXIT_UNCLASSIFIED_ERROR),
                )
            append_row(results_dir, "proof", row, load_before=load_before)
            print(
                f"{task}{'-mutant' if args.mutant else ''} r{repetition}: {row['outcome']} in "
                f"{row['wall_clock_s']}s (startup {row['startup_s']}s, proof {row['proof_s']}s), "
                f"turns={row['proof']['turns']}, tokens="
                f"{row['proof']['input_tokens']}/{row['proof']['output_tokens']}, "
                f"cost=${row['cost_usd']:.4f}"
                + (f", mutant={row['mutant']}" if row["mutant"] else "")
            )
            if row["error"] is not None:
                print(
                    f"{task} r{repetition}: {row['error']['kind']}: {row['error']['message']}",
                    file=sys.stderr,
                )
    except Refusal as refusal:
        # Nothing was measured, so there is no row: the reason goes to the operator and the exit code
        # says which refusal it was (plans D13/D15).
        print(refusal.message, file=sys.stderr)
        return refusal.code
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
