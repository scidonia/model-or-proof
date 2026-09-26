#!/usr/bin/env python3
"""Run the capability battery: eight statements through the loop, one table (plan D22).

The battery is the yardstick for a setup: a change to the prompt, the planning turn, the examples, the
automation order, the arms or the model is made *one at a time* and measured here, so we learn which
change helps a setup close proofs reliably and rapidly. Every case goes through `harness.route_b` — the
one instrument that writes rows — so a battery row is comparable with any other Route B row, sessions
and all.

    nix develop -c python3 scripts/battery.py                 # every case in tasks/battery.json
    nix develop -c python3 scripts/battery.py --case gauss_sum # one case, for an iteration
    nix develop -c python3 scripts/battery.py --jobs 4         # four cases in flight at once
    nix develop -c python3 scripts/battery.py --record-baselines  # pin the seeds and exit

`--jobs N` runs N cases at once, each in its own `route_b` process with its own repl. The cases are
independent - their own seed, their own working copy, their own row - so concurrency changes nothing
about the verdicts, but it *does* change the per-case wall-clock, because cases now share the host and
the model provider: `wall_s` is only comparable across runs at the same `--jobs`, which the table's
header records. Each concurrent case holds a repl with Mathlib loaded (~9 GB resident, measured); about
five fit comfortably on the free RAM of the current host. Output stays attributable: every case's lines
are prefixed with the case name, and the case's own heartbeat lines carry it too.

What each case passes: `expected` is the outcome the setup must reach — `closed` for a provable
statement, `negative` for the false one. The runner exits non-zero if a provable case does not close, or
if the false case is not `refuted` within its budget: a cap-burn on the negative control is a finding,
not a pass (plan D22). An `error` row is printed with the whole error object — the kind, the message and
whatever the failing layer put beside them — because a table that says only "error" costs a re-run to
diagnose.

A new seed has no recorded baseline, and `harness.route_b` refuses (exit 9) to run one — correctly: a row
must be able to say what the run started from. So the runner pins the battery's seeds on first use
through `route_b --record-baseline` and says so on stdout; it never pins a seed that is not a fresh seed
(exactly one goal hole), because a baseline that pins an edited or closed file is a lie about provenance.
"""

import argparse
import hashlib
import json
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO))

from harness import route_b  # noqa: E402
from harness.lean_repl import count_unclosed  # noqa: E402

DEFAULT_MANIFEST = REPO / "tasks" / "battery.json"
DEFAULT_RESULTS = REPO / "results"


class BatteryError(Exception):
    """The battery cannot be run at all: a missing case, a seed that is not a fresh seed."""


def fresh_seed(seed: Path) -> None:
    """Refuse a seed that is not the battery's shape: one statement, one goal hole (plan D22)."""
    if not seed.is_file():
        raise BatteryError(f"{route_b.relative(seed)} is missing: the manifest names a seed that is not there")
    holes = count_unclosed(seed.read_text())
    if holes != 1:
        raise BatteryError(
            f"{route_b.relative(seed)} carries {holes} goal holes, not one: a battery seed is one "
            "statement with one `sorry`, and a baseline pinned over anything else would misstate what "
            "the run started from"
        )


def ensure_baseline(seed: Path, *, report) -> None:
    """Give a battery seed the record `route_b` insists on, and say so (plans D15/D22).

    Recording is explicit and loud — the pin is printed with its hash and both paths — and it happens
    only for a seed that is a fresh seed. An already-recorded seed whose record still matches is left
    alone; one whose committed file has drifted is left for the drift to be reported by the run itself
    (`assisted`, `baseline.matches: false`), which is exactly what that machinery is for.
    """
    fresh_seed(seed)
    record_path = seed.parent / route_b.SEEDS_RECORD
    recorded = None
    if record_path.is_file():
        board = json.loads(record_path.read_text())
        recorded = board.get(seed.name)
    digest = hashlib.sha256(seed.read_bytes()).hexdigest()
    if recorded == digest:
        return
    written = route_b.record_baseline(seed)
    report(
        f"recorded the baseline for {written['seed']} "
        f"({'unchanged record updated' if recorded else 'first record'}): "
        f"sha256 {written['sha256'][:16]}… → {written['record']} + {written['baseline']}"
    )


def run_case(
    case: dict, manifest: dict, manifest_path: Path, results_dir: Path, repl_bin: str, *, report
) -> dict:
    """One case through `harness.route_b`, returning the row it appended (plan D22)."""
    seed = REPO / case["seed"]
    cap_s = case.get("cap_s") or manifest["budgets"]["wall_clock_s"]
    cap_usd = case.get("cap_usd") or manifest["budgets"]["usd"]
    argv = [
        sys.executable,
        str(REPO / "harness" / "route_b.py"),
        "--task",
        str(manifest_path),
        "--proof",
        str(seed),
        "--results",
        str(results_dir),
        "--arms",
        manifest["setup"]["arms"],
        "--repl-bin",
        repl_bin,
        "--cap-s",
        str(cap_s),
        "--cap-usd",
        str(cap_usd),
    ]
    if case["expected"] == "negative":
        # What declares the statement false: the refutation arm's witness is then the expected outcome
        # rather than the rig defect a witness against a true statement would be (plan D16).
        argv.append("--mutant")
    # The child's output is streamed, not captured until the end: a case takes minutes, and the
    # heartbeat on its stderr is what says a run is alive rather than wedged. Every line is prefixed
    # with the case's name, so four cases in flight are still four readable runs (plan D25).
    # The boundary this case's row must land after (finding P1.1): the record already holds rows for
    # these seeds from earlier invocations, so only what is appended from here on can be this case's
    # evidence. A child that exits before appending then fails loudly instead of inheriting an earlier
    # run's success.
    rows_path = results_dir / "proof.jsonl"
    boundary = len(rows_path.read_text().splitlines()) if rows_path.is_file() else 0
    proc = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    tail: list[str] = []
    for line in proc.stdout:
        report(f"[{case['name']}] {line.rstrip()}")
        tail.append(line.rstrip())
        if len(tail) > 200:
            tail.pop(0)
    code = proc.wait()
    row = fresh_row_for(
        results_dir, boundary, manifest["name"], seed, case=case["name"], code=code, tail=tail
    )
    row["_exit_code"] = code
    row["_stderr"] = "\n".join(tail)
    return row


def fresh_row_for(
    results_dir: Path, boundary: int, task: str, seed: Path, *, case: str, code: int, tail: list[str]
) -> dict:
    """The row **this invocation** appended for this case, or a loud failure (finding P1.1).

    Rows from earlier invocations are not evidence for this one. The record holds several rows per seed
    already, so accepting any matching row would let a child that exits before appending inherit an
    earlier success — the case would pass on someone else's proof. Two rules follow, and both are loud:

    * only lines after ``boundary`` (the line count taken before the child was spawned) can be this
      case's record, matched on task and seed;
    * a line there that will not parse is a defect in the writer, not something to skip past — the
      record cannot be trusted, and the case is not scored against an older row instead.

    The row and the child must also agree: a row that claims ``success`` or ``refuted`` while the child
    exited non-zero (or died on a signal) is a contradiction, and the case fails rather than passing on
    whichever half is convenient.
    """
    rows_path = results_dir / "proof.jsonl"
    lines = rows_path.read_text().splitlines() if rows_path.is_file() else []
    wanted = route_b.relative(seed)
    found: tuple[int, dict] | None = None
    for index, line in enumerate(lines):
        if index < boundary or not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as malformed:
            raise BatteryError(
                f"{case}: line {index + 1} of {route_b.relative(rows_path)} was appended during this "
                f"run and does not parse ({malformed}); the record is not trustworthy, so this case is "
                "not scored against an earlier row instead"
            ) from malformed
        artifacts = row.get("artifacts") or {}
        if row.get("task") == task and artifacts.get("seed") == wanted:
            found = (index + 1, row)
    if found is None:
        raise BatteryError(
            f"{case}: route_b exited {code} without appending a row for {wanted} in this run (nothing "
            f"after line {boundary} matches) — output: {' | '.join(tail[-8:])[-400:]!r}"
        )
    line_number, row = found
    if code < 0:
        raise BatteryError(
            f"{case}: route_b was killed by signal {-code} after appending its row on line "
            f"{line_number}; the row is a partial record of a run that did not finish"
        )
    if row.get("outcome") in ("success", "refuted") and code != 0:
        raise BatteryError(
            f"{case}: the row on line {line_number} says {row['outcome']!r} but route_b exited {code} — "
            "the row and the child disagree about the run"
        )
    row["_row_line"] = line_number
    return row


def verdict(case: dict, row: dict) -> tuple[bool, str]:
    """Whether the case met its expectation, and why not (plan D22)."""
    outcome = row["outcome"]
    if case["expected"] == "negative":
        if outcome == "refuted":
            return True, ""
        if outcome == "timeout":
            return False, f"the negative control burned its cap ({row['budget_exceeded']}) without a witness"
        return False, f"the negative control ended {outcome!r}, not 'refuted'"
    if outcome == "success":
        return True, ""
    if outcome == "timeout":
        return False, f"did not close within the cap ({row['budget_exceeded']})"
    return False, f"ended {outcome!r}, not 'success'"


def closing_agent(row: dict) -> str:
    """Who closed it: the automation pass, the model, or nobody (plan D22)."""
    if row["proof"].get("automation_closed"):
        return "automation"
    if row["outcome"] == "success" or row["outcome"] == "refuted":
        return "model"
    return "-"


def summarise(case: dict, row: dict) -> dict:
    proof = row["proof"]
    return {
        "case": case["name"],
        "expected": case["expected"],
        "outcome": row["outcome"],
        "agent": closing_agent(row),
        "turns": proof["turns"],
        "wall_clock_s": row["wall_clock_s"],
        "cost_usd": row["cost_usd"],
        "artifact_closed": proof.get("artifact_unclosed_goals") == 0,
        "unclosed_goals": proof.get("unclosed_goals"),
        # Refusals split by whose fault they were (plan D24): a `transport` refusal is the rig failing to
        # hand the step to Lean, and pooling it with the model's own rejected tactics would report the
        # rig's bug as a model failure. The per-entry `kind`s in the row stay the authoritative detail.
        "refusals": refusal_split(proof.get("failures") or []),
        "refutation": row.get("refutation"),
        "error": row.get("error"),
    }


def refusal_split(failures) -> dict:
    """A row's refusals, counted by kind (plan D24): ``lean`` (Lean rejected the step) and ``transport``
    (the rig could not hand it to Lean). Both are recorded per entry in the row; this is only the
    summary's view, kept split so a rig fault is never read as a model failure.
    """
    return {kind: sum(1 for entry in failures if entry.get("kind") == kind) for kind in ("lean", "transport")}


def print_table(summaries: list[dict], report, *, jobs: int = 1) -> None:
    header = (
        f"{'case':22} {'expected':9} {'outcome':9} {'agent':10} {'turns':>5} {'wall_s':>7} "
        f"{'cost_usd':>9} {'artifact':8} {'goals':>5} {'refusals l/t':>13} {'refutation':11} result"
    )
    report(header)
    report("-" * len(header))
    report(
        f"# --jobs {jobs}: per-case wall_s is comparable only across runs at the same --jobs "
        "(concurrent cases share the host and the provider); outcomes and costs are unaffected"
    )
    for summary in summaries:
        goals = "-" if summary["unclosed_goals"] is None else str(summary["unclosed_goals"])
        refusals = summary.get("refusals") or {"lean": 0, "transport": 0}
        refusal_cell = f"{refusals['lean']}/{refusals['transport']}"
        report(
            f"{summary['case']:22} {summary['expected']:9} {summary['outcome']:9} {summary['agent']:10} "
            f"{summary['turns']:>5} {summary['wall_clock_s']:>7.1f} {summary['cost_usd']:>9.5f} "
            f"{'closed' if summary['artifact_closed'] else 'open':8} {goals:>5} "
            f"{refusal_cell:>13} {summary['refutation'] or '-':11} "
            f"{'PASS' if summary['passed'] else 'FAIL'}"
        )
        if summary["error"] is not None:
            report(f"    error: {json.dumps(summary['error'])}")
        if summary["note"]:
            report(f"    {summary['note']}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="scripts/battery.py")
    parser.add_argument("--manifest", default=str(DEFAULT_MANIFEST))
    parser.add_argument("--results", default=str(DEFAULT_RESULTS))
    parser.add_argument("--repl-bin", default=route_b.DEFAULT_REPL_BIN)
    parser.add_argument("--case", action="append", help="run only this case (repeatable)")
    parser.add_argument(
        "--jobs",
        type=int,
        default=1,
        metavar="N",
        help="cases in flight at once (default 1: today's serial behaviour, and the reference for "
        "wall-clock comparisons). Each concurrent case is its own route_b process with its own repl and "
        "Mathlib loaded: measured ~9 GB resident, and about five fit comfortably on the free RAM of "
        "this host. Pass/fail is unaffected by concurrency; per-case wall-clock is not.",
    )
    parser.add_argument(
        "--record-baselines",
        action="store_true",
        help="pin every seed's baseline and exit, without running anything",
    )
    args = parser.parse_args(argv)

    manifest_path = Path(args.manifest)
    manifest = json.loads(manifest_path.read_text())
    cases = manifest["cases"]
    if args.case:
        wanted = set(args.case)
        unknown = wanted - {case["name"] for case in cases}
        if unknown:
            parser.error(f"unknown case(s): {', '.join(sorted(unknown))}")
        cases = [case for case in cases if case["name"] in wanted]

    jobs = max(1, min(args.jobs, len(cases)))
    printer = threading.Lock()

    def report(line: str = "") -> None:
        with printer:
            print(line, flush=True)

    report(f"battery: {len(cases)} case(s) from {route_b.relative(manifest_path)}, "
           f"arms {manifest['setup']['arms']}, row budget {manifest['budgets']['wall_clock_s']:g}s / "
           f"${manifest['budgets']['usd']:g} per case unless the case overrides it")
    # This invocation's identity (finding P1.1). A case is scored only on a row appended after the run
    # started — the record already holds rows for these seeds — and the table names each row's line, so a
    # reader can check the provenance of a result rather than trusting the file's latest matching row.
    run_token = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    report(f"run token: {run_token} (every reported row was appended after this invocation started)")

    if args.record_baselines:
        for case in cases:
            ensure_baseline(REPO / case["seed"], report=report)
        report("baselines recorded; no run")
        return 0

    results_dir = Path(args.results)
    report(
        f"concurrency: --jobs {jobs}"
        + (
            f" ({jobs} of {len(cases)} cases in flight; each holds a repl with Mathlib, ~9 GB resident)"
            if jobs > 1
            else " (serial: one case at a time)"
        )
    )

    # The baselines are pinned before any case runs, and serially: recording one is a read-modify-write
    # of the shared record, which concurrent cases would race.
    for case in cases:
        ensure_baseline(REPO / case["seed"], report=report)

    def one(case: dict) -> dict:
        """Run one case and summarise it: the unit a worker thread takes."""
        try:
            report(f"[{case['name']}] starting {route_b.relative(REPO / case['seed'])}")
            row = run_case(case, manifest, manifest_path, results_dir, args.repl_bin, report=report)
        except BatteryError as failure:
            return (
                {
                    "case": case["name"],
                    "expected": case["expected"],
                    "outcome": "no row",
                    "agent": "-",
                    "turns": 0,
                    "wall_clock_s": 0.0,
                    "cost_usd": 0.0,
                    "artifact_closed": False,
                    "unclosed_goals": None,
                    "refusals": {"lean": 0, "transport": 0},
                    "refutation": None,
                    "error": {"kind": "no_row", "message": str(failure)},
                    "passed": False,
                    "note": "",
                }
            )
        passed, note = verdict(case, row)
        summary = summarise(case, row)
        summary["passed"] = passed
        address = f"row {row['_row_line']} of {route_b.relative(results_dir / 'proof.jsonl')}"
        summary["note"] = (
            f"OMP sessions: {route_b.relative(Path(row['artifacts']['omp_sessions']))}; {address} (run {run_token})"
            if passed
            else f"{note}; {address} (run {run_token})"
        )
        if not passed and row.get("error") is None and row.get("_stderr"):
            summary["note"] = f"{note}; output: {row['_stderr'][-200:]}"
        return summary

    if jobs == 1:
        summaries = [one(case) for case in cases]
    else:
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            summaries = list(pool.map(one, cases))  # input order: the table stays deterministic

    report()
    print_table(summaries, report, jobs=jobs)
    failures = [summary["case"] for summary in summaries if not summary["passed"]]
    report()
    report(
        f"{len(summaries) - len(failures)}/{len(summaries)} passed"
        + (f"; failing: {', '.join(failures)}" if failures else "")
    )
    report(f"rows appended to {route_b.relative(results_dir / 'proof.jsonl')}; "
           "each row names its OMP session directory under results/omp/")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
