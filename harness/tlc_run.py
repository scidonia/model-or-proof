"""Route A: run one TLA+ task under TLC and emit a result row (docs/protocol.md §6, §7).

The row is the measurement. Its numbers come from TLC's final summary and from nothing else: a
progress line is a running count, not an answer, and a killed run is a timeout rather than a verdict.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from harness.result import COST_BASIS, append_row, compute_cost_usd  # noqa: E402

# TLC prints the same phrases in periodic progress lines and in the final summary; only the summary
# is anchored at the start of a line and terminated by "states left on queue.".
SUMMARY_RE = re.compile(
    r"(?m)^([\d,]+) states generated, ([\d,]+) distinct states found, ([\d,]+) states left on queue\.\s*$"
)
PROGRESS_RE = re.compile(
    r"Progress\(\d+\) at [^\n]*?: ([\d,]+) states generated \([^)]*\), ([\d,]+) distinct states found"
)
DEPTH_RE = re.compile(r"The depth of the complete state graph search is (\d+)\.")
VIOLATION_RE = re.compile(r"Error: (?:Invariant|Temporal property) (\S+) is violated\.")
CFG_CONSTANT_RE = re.compile(r"(?m)^\s*CONSTANTS?\s+N\s*=\s*(\d+)")
CFG_INVARIANT_RE = re.compile(r"(?m)^\s*INVARIANTS?\s+(\S+)")
TLC_VERSION_RE = re.compile(r"Version ([\d.]+) of")
# TLC's banner states the effective profile of the run it is about to start, e.g.
# "Running breadth-first search Model-Checking with fp 28 and seed 1 with 1 worker on 20 cores with
# 12743MB heap and 64MB offheap memory (…)" — the real banner for -Xmx14336m on the pinned JRE, whose
# heap is the JVM's usable maximum rather than the requested option. These fields are what a pinned
# Route A cell claims the run used, so they are read back from the run's own output, not the request.
BANNER_HEAP_RE = re.compile(r"\bwith (\d+)MB heap\b")
BANNER_FP_RE = re.compile(r"\bwith fp (\d+)\b")
BANNER_SEED_RE = re.compile(r"\band seed (-?\d+)\b")
# The JVM prints the options it was handed, e.g. "Picked up JAVA_TOOL_OPTIONS: -Xmx14336m". That line
# is the *delivery witness* for a requested heap: the JVM's own statement of the -Xmx it received. It
# is deliberately not the banner, whose heap is the usable maximum on a different basis (8/9 of -Xmx
# under ParallelGC) and which therefore never confirms the delivered option.
PICKUP_RE = re.compile(r"Picked up JAVA_TOOL_OPTIONS: (.+)")
XMX_RE = re.compile(r"-Xmx(\d+)m\b")


def _num(text: str) -> int:
    return int(text.replace(",", ""))


def parse_tlc_log(text: str) -> dict:
    """Summarise a TLC log.

    ``generated``/``distinct``/``left``/``depth`` are None unless the run reached its final summary.
    ``states_reached`` is the explored state count at the moment the log ends — the final distinct
    count on a completed run, the last progress line's count on a killed one.
    """
    parsed = {
        "generated": None,
        "distinct": None,
        "left": None,
        "depth": None,
        "states_reached": None,
        "violation": None,
    }

    summary = None
    for match in SUMMARY_RE.finditer(text):  # last match wins: progress lines must never be the answer
        summary = match
    if summary is not None:
        parsed["generated"], parsed["distinct"], parsed["left"] = (
            _num(group) for group in summary.groups()
        )

    depth = DEPTH_RE.search(text)
    if depth is not None:
        parsed["depth"] = int(depth.group(1))

    progress = PROGRESS_RE.findall(text)
    if summary is not None:
        parsed["states_reached"] = parsed["distinct"]
    elif progress:
        parsed["states_reached"] = _num(progress[-1][1])

    violation = VIOLATION_RE.search(text)
    if violation is not None:
        parsed["violation"] = violation.group(1)

    return parsed


def parse_tlc_banner(text: str) -> dict | None:
    """The effective profile TLC's banner reports, or None when the log carries no banner.

    The banner is the *observed* side of the profile contract: it is what the launched JVM and TLC
    actually used, as opposed to what the caller asked for. Fields the banner does not state are null,
    so a partial banner can only ever fail to confirm a request, never silently satisfy one.
    """
    heap = BANNER_HEAP_RE.search(text)
    fp = BANNER_FP_RE.search(text)
    seed = BANNER_SEED_RE.search(text)
    if heap is None and fp is None and seed is None:
        return None
    return {
        "heap_mib": int(heap.group(1)) if heap else None,
        "fp_index": int(fp.group(1)) if fp else None,
        "seed": int(seed.group(1)) if seed else None,
    }


def parse_heap_delivery(text: str) -> str | None:
    """The ``-Xmx<n>m`` the JVM says it was handed, or None when no pickup line states one.

    This is the *delivery* side of a requested heap, and it is a different quantity from the banner's
    usable heap: the JVM echoes the option it received, while the banner reports the maximum the run
    could actually use. When several pickup lines exist the last one wins, matching the JVM's own
    last-option-wins handling of its command line.
    """
    delivered = None
    for match in PICKUP_RE.finditer(text):
        options = XMX_RE.findall(match.group(1))
        if options:
            delivered = options[-1]
    return f"-Xmx{delivered}m" if delivered is not None else None


# The row-facing names of the profile controls, used in the mismatch diagnostic so the sentence names
# the quantity rather than the dict key (scenario 7 requires the fingerprint mismatch to be named).
PROFILE_LABELS = {"fp_index": "fingerprint fp", "seed": "seed"}


def profile_mismatch(
    requested: dict, observed: dict | None, heap_delivery: str | None
) -> str | None:
    """The first *requested* control the run contradicts, or None when the run confirms every one.

    Only non-null requests are compared: a null request is "not asked for", not "asked for null", so an
    unpinned run cannot mismatch an ambient setting it never claimed (scenario 6). The heap is checked
    against the JVM's own delivery witness rather than the banner — a banner echoing the request is not
    evidence that the JVM received it — while the fingerprint index and seed are checked against the
    banner, where TLC states them. A request the run cannot confirm is a mismatch: an unconfirmed pin
    is not a confirmed one, and a request with no banner at all is unconfirmed by definition.
    """
    if observed is None and any(value is not None for value in requested.values()):
        return "a fixed profile was requested, but the run printed no TLC profile banner"

    heap = requested["heap_mib"]
    if heap is not None:
        wanted = f"-Xmx{heap}m"
        if heap_delivery != wanted:
            return (
                f"requested heap {wanted}, but the JVM reported "
                f"{heap_delivery if heap_delivery is not None else 'no JAVA_TOOL_OPTIONS pickup'}"
            )

    for field, label in PROFILE_LABELS.items():
        want = requested[field]
        if want is None:
            continue
        got = observed.get(field) if observed else None
        if got != want:
            return (
                f"requested {label} {want}, but TLC reported "
                f"{got if got is not None else 'no banner value'}"
            )
    return None


def read_cfg(config: Path) -> dict:
    """The instance parameters a cfg fixes: the value of N and the invariant's name."""
    text = Path(config).read_text()
    constant = CFG_CONSTANT_RE.search(text)
    invariant = CFG_INVARIANT_RE.search(text)
    return {
        "param_N": _num(constant.group(1)) if constant else None,
        "property": invariant.group(1) if invariant else None,
    }


def _kill_tree(proc: subprocess.Popen) -> None:
    """Kill a process and everything it spawned.

    The pinned wrapper execs the JVM, so the process started here *is* the JVM. Killing its process
    group (runs are launched with ``start_new_session``) takes the JVM and any children it started, and
    closes the pipe the reader thread is waiting on.
    """
    if proc.poll() is not None:
        return
    try:
        os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        proc.kill()
    proc.wait()


def probe_tlc_version(tlc_bin: str) -> str:
    """TLC's version, or "unknown" when the binary cannot be asked."""
    try:
        proc = subprocess.Popen(
            [tlc_bin, "-help"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            start_new_session=True,
        )
    except OSError:
        return "unknown"
    try:
        out, _ = proc.communicate(timeout=5)
    except subprocess.TimeoutExpired:
        _kill_tree(proc)
        return "unknown"
    match = TLC_VERSION_RE.search(out)
    return match.group(1) if match else "unknown"


def _peak_rss_mb(pid: int) -> float | None:
    try:
        with open(f"/proc/{pid}/status") as handle:
            for line in handle:
                if line.startswith("VmHWM:"):
                    return int(line.split()[1]) / 1024.0
    except OSError:
        return None
    return None


def run_tlc(
    spec: Path,
    config: Path,
    *,
    tlc_bin: str = "tlc",
    cap_s: float = 7200.0,
    workers: int = 1,
    heap_mib: int | None = None,
    fp_index: int | None = None,
    seed: int | None = None,
) -> dict:
    """Run TLC over one instance, capped at ``cap_s`` seconds, and return the raw observation.

    ``heap_mib``/``fp_index``/``seed`` are the *requested* fixed profile (`None` = not requested). The
    heap is delivered to the JVM only, via the child's ``JAVA_TOOL_OPTIONS``; ``tlc -Xmx`` is rejected by
    the pinned wrapper, which execs Java with the remaining arguments after the main class. ``-fp`` and
    ``-seed`` are TLC options and go in the option region of the command line, before the spec.
    """
    spec = Path(spec).resolve()
    config = Path(config).resolve()
    # The runner sets the child's cwd to the spec's directory, so a relative binary path would no
    # longer resolve: make the interpreter's own resolution explicit before launching.
    if os.sep in tlc_bin or Path(tlc_bin).exists():
        tlc_bin = str(Path(tlc_bin).resolve())
    # The state pool is per *invocation*, not per spec (the planner's ruling: runner soundness, not
    # scheduling). TLC's default metadir is `<spec's directory>/states/`, shared by every run of that spec,
    # so one run's `-cleanup` deletes another's pool mid-enumeration — and the victim reads as an instance
    # hitting a limit rather than as a sibling's sabotage, which is a failure a reader would believe. A
    # private metadir makes concurrent calibrations safe instead of merely discouraged: no run can reach
    # another's files even with the same spec.
    #
    # It lives under the spec's own directory rather than in `TMPDIR` (the planner's ruling): a directory in
    # a temporary namespace outlives the run and sits outside everything that cleans up after a task, while
    # one here is cleared by the same sweep that clears a task's scratch.
    scratch = spec.parent / ".tlc-states"
    scratch.mkdir(parents=True, exist_ok=True)
    metadir = tempfile.mkdtemp(prefix="run-", dir=scratch)
    # `-cleanup` is deliberately **not** passed. Its only job was removing the metadir, and the harness
    # already creates a private one per run and removes it in the `finally` below — so the flag was a
    # deletion whose timing we could not state, and on EWD998 it removed the pool the run was still using:
    # N=4 died at 75,753,775 states with `StatePoolReader`, N=5 and N=6 with `StatePoolWriter` at ~250k,
    # while the same N=5 spec without the flag passed sixteen times its with-flag death point. The metadir's
    # lifetime is ours now, on every exit path.
    cmd = [
        tlc_bin, "-workers", str(workers),
        *(["-fp", str(fp_index)] if fp_index is not None else []),
        *(["-seed", str(seed)] if seed is not None else []),
        "-metadir", metadir,
        "-config", str(config), str(spec),
    ]
    # The requested heap is a JVM property, not a TLC option: the pinned wrapper runs
    # `java … tlc2.TLC <args>`, so a `-Xmx` in TLC's argv is not seen by the JVM and TLC rejects it.
    # `JAVA_TOOL_OPTIONS` is read by the JVM at startup, so it reaches the TLC child (and only the
    # child: the runner's own interpreter is not a JVM) and the banner then reports the effective heap.
    # An explicit request replaces any inherited value: the row claims *this* heap, and silently
    # keeping a second `-Xmx` from the caller's environment would make the row's claim unattributable.
    env = os.environ.copy()
    if heap_mib is not None:
        # `_JAVA_OPTIONS` (and, on newer JDKs, `JDK_JAVA_OPTIONS`) is read by the JVM *after*
        # JAVA_TOOL_OPTIONS and overrides it (measured on the pinned JRE: an ambient
        # `_JAVA_OPTIONS=-Xmx1000m` left the JAVA_TOOL_OPTIONS pickup printing -Xmx14336m while the usable
        # heap fell to 958MB). Left in place it would make an explicit request a lie the row cannot show.
        # Only an explicit request scrubs them — an unpinned run keeps the caller's environment — and they
        # are removed from the child's copy, never from the caller's process.
        env.pop("_JAVA_OPTIONS", None)
        env.pop("JDK_JAVA_OPTIONS", None)
        env["JAVA_TOOL_OPTIONS"] = f"-Xmx{heap_mib}m"

    started = time.monotonic()
    proc = subprocess.Popen(
        cmd,
        cwd=str(spec.parent),
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
        start_new_session=True,
    )

    state: dict = {"startup_s": None, "peak_rss_mb": 0.0, "timed_out": False}
    lines: list[str] = []

    def watch_memory() -> None:
        while proc.poll() is None:
            rss = _peak_rss_mb(proc.pid)
            if rss is not None:
                state["peak_rss_mb"] = max(state["peak_rss_mb"], rss)
            time.sleep(0.05)

    def read_output() -> None:
        for line in proc.stdout:  # type: ignore[union-attr]
            if state["startup_s"] is None and "Starting..." in line:
                state["startup_s"] = round(time.monotonic() - started, 3)
            lines.append(line)

    reader = threading.Thread(target=read_output, daemon=True)
    memory = threading.Thread(target=watch_memory, daemon=True)
    reader.start()
    memory.start()

    try:
        proc.wait(timeout=cap_s)
    except subprocess.TimeoutExpired:
        state["timed_out"] = True
        _kill_tree(proc)
    finally:
        reader.join(timeout=10)
        memory.join(timeout=10)
        # The pool's removal belongs here rather than to a TLC flag: `finally` runs on the normal path, the
        # capped path (`TimeoutExpired` above) and an exception, so no sweep leaves a metadir behind and no
        # removal happens while the run that owns it is still using it.
        shutil.rmtree(metadir, ignore_errors=True)

    wall_clock_s = round(time.monotonic() - started, 3)
    log = "".join(lines)
    parsed = parse_tlc_log(log)
    requested = {"heap_mib": heap_mib, "fp_index": fp_index, "seed": seed}
    observed = parse_tlc_banner(log)
    delivered = parse_heap_delivery(log)
    # A contradictory banner outranks the run's own verdict other than a timeout: a completed summary
    # whose profile does not match the request is not evidence about the *requested* configuration, and
    # neither is a violation found under an unconfirmed fingerprint/seed. It never outranks a timeout,
    # which says nothing about what was checked and is already not a verdict.
    mismatch = profile_mismatch(requested, observed, delivered)

    if state["timed_out"]:
        outcome = "timeout"
    elif mismatch is not None:
        outcome = "error"
    elif parsed["violation"] is not None:
        outcome = "violation"
    elif parsed["generated"] is not None and proc.returncode == 0:
        outcome = "success"
    else:
        outcome = "error"

    return {
        "outcome": outcome,
        "wall_clock_s": wall_clock_s,
        "startup_s": state["startup_s"],
        "peak_rss_mb": round(state["peak_rss_mb"], 1) if state["peak_rss_mb"] else None,
        "states_reached": parsed["states_reached"],
        "parsed": parsed,
        # What was asked for versus what the run reported using: the row's provenance, not the run's
        # verdict. `heap_delivery` is the JVM's own `-Xmx` witness (null when it printed none) and
        # `observed` is the banner's profile (null when the log carried no banner at all).
        "tlc_profile": {
            "requested": requested,
            "heap_delivery": delivered,
            "observed": observed,
        },
        "profile_error": mismatch,
        "log": log,
        "cmd": cmd,
    }


def failure_tail(log: str, limit: int = 12) -> list[str]:
    """The lines that say *why* a TLC run failed, in TLC's own words (F3's rule for the third path).

    A row recording ``error`` without the reason is not diagnosable from its own record: the only other
    pointer is ``artifacts.log``, a path a reader holding the row cannot follow. TLC names its failures
    precisely — ``Lexical error at line …, column …``, ``Invariant … is violated``, ``StatePoolWriter …``,
    ``*** Errors:`` — so this routes that output into the row rather than inventing a vocabulary.

    A normal successful run has none of these, so an ``error`` with an empty tail is itself evidence: the
    process died without saying why, which is the case where the log is the only recourse.
    """
    markers = ("Error:", "Fatal", "*** Errors", "Lexical error", "error while", "Error ")
    kept: list[str] = []
    for line in log.splitlines():
        stripped = line.strip()
        if stripped and any(stripped.startswith(marker) for marker in markers):
            kept.append(stripped)
    return kept[-limit:]


def build_row(
    *,
    task: str,
    param_N: int | None,
    property_name: str | None,
    repetition: int,
    observation: dict,
    tool: dict,
    spec: Path,
    config: Path,
    log_path: Path,
    negative_control: dict | None = None,
) -> dict:
    parsed = observation["parsed"]
    completed = parsed["generated"] is not None and observation.get("profile_error") is None
    # A profile mismatch is a failure TLC itself never printed, so the row's failure tail starts with the
    # harness's own sentence and is followed by whatever TLC did say. Without it the diagnostic would be
    # no more specific than the banner in `artifacts.log`.
    error = failure_tail(observation["log"])
    if observation.get("profile_error"):
        error = [observation["profile_error"], *error]
    return {
        "task": task,
        "route": "tlc",
        "tool": tool,
        "param_N": param_N,
        "property": property_name,
        "tier": 1,
        "repetition": repetition,
        "outcome": observation["outcome"],
        # F3's rule for the third path (the planner's ruling): a TLC row that says `error` carries TLC's own
        # failure tail, the way file mode carries Lean's output and the oracle carries the provider's
        # message. `outcome` stays the machine-readable summary — `success`/`violation`/`timeout`/`error` —
        # and this is the "why" beside it, so a failing calibration can be diagnosed from its own record
        # rather than only from `artifacts.log`. `None` on a run that did not fail.
        "error": error if observation["outcome"] == "error" else None,
        # The run's provenance: the requested fixed profile (explicit nulls for flags the caller omitted,
        # so an unpinned run is never labelled as a pinned one) against the profile the run's banner
        # reported. A mismatch makes the row an `error` with no `tlc` summary above (`completed`), so a
        # contradictory banner can never settle a pinned cell.
        "tlc_profile": observation["tlc_profile"],
        "wall_clock_s": observation["wall_clock_s"],
        "startup_s": observation["startup_s"],
        "peak_rss_mb": observation["peak_rss_mb"],
        "states_reached": observation["states_reached"],
        "cost_usd": compute_cost_usd(observation["wall_clock_s"]),
        "cost_basis": COST_BASIS,
        "tlc": (
            {
                "generated": parsed["generated"],
                "distinct": parsed["distinct"],
                "left": parsed["left"],
                "depth": parsed["depth"],
                "workers": observation["workers"],
            }
            if completed
            else None
        ),
        "proof": None,
        "artifacts": {
            "spec": str(spec.relative_to(REPO)) if spec.is_relative_to(REPO) else str(spec),
            "config": str(config.relative_to(REPO)) if config.is_relative_to(REPO) else str(config),
            "log": str(log_path),
        },
        "negative_control": negative_control,
    }


REPO = Path(__file__).resolve().parents[1]


def _positive_int(text: str) -> int:
    try:
        value = int(text)
    except ValueError:
        raise argparse.ArgumentTypeError(f"expected an integer, got {text!r}") from None
    if value <= 0:
        raise argparse.ArgumentTypeError(f"expected a positive integer, got {text!r}")
    return value


def _fp_index(text: str) -> int:
    """TLC's fingerprint polynomial index: `-fp` accepts 0..130."""
    try:
        value = int(text)
    except ValueError:
        raise argparse.ArgumentTypeError(f"expected an integer, got {text!r}") from None
    if not 0 <= value <= 130:
        raise argparse.ArgumentTypeError(f"expected a fingerprint index in 0..130, got {text!r}")
    return value


def _signed_long(text: str) -> int:
    """TLC's `-seed` is a Java `long`, so the accepted range is the signed 64-bit one."""
    try:
        value = int(text)
    except ValueError:
        raise argparse.ArgumentTypeError(f"expected an integer, got {text!r}") from None
    if not -(2**63) <= value < 2**63:
        raise argparse.ArgumentTypeError(f"expected a signed 64-bit long, got {text!r}")
    return value


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="harness.tlc_run")
    parser.add_argument("--task", required=True, help="task manifest under tasks/")
    parser.add_argument("--mutant", action="store_true", help="run the task's mutant instead")
    parser.add_argument("--instance", type=int, default=None, help="param_N to select")
    parser.add_argument("--reps", type=int, default=1)
    parser.add_argument("--results", required=True)
    parser.add_argument("--cap-s", type=float, default=None)
    parser.add_argument("--tlc-bin", default="tlc")
    parser.add_argument("--workers", type=int, default=1)
    # The optional fixed-profile flags (scenarios 5–7). Each is None when omitted and is then recorded as
    # an explicit null in `tlc_profile.requested` — "not requested" is not "requested to be the default".
    parser.add_argument(
        "--heap-mib", type=_positive_int, default=None,
        help="TLC child JVM max heap in MiB, delivered as JAVA_TOOL_OPTIONS=-Xmx<n>m",
    )
    parser.add_argument(
        "--fp-index", type=_fp_index, default=None,
        help="TLC fingerprint polynomial index (TLC -fp), 0..130",
    )
    parser.add_argument(
        "--seed", type=_signed_long, default=None,
        help="TLC enumeration seed (TLC -seed), a signed 64-bit long",
    )
    args = parser.parse_args(argv)

    manifest = json.loads(Path(args.task).read_text())
    task = manifest["name"]
    results_dir = Path(args.results)

    if args.mutant:
        spec = Path(manifest["mutant"]["spec"])
        config = Path(manifest["mutant"]["config"])
        negative_control = {"mutant": spec.name, "expected": "violation", "observed": None}
    else:
        instances = manifest["instances"]
        chosen = None
        if args.instance is not None:
            chosen = next(i for i in instances if i["param_N"] == args.instance)
        elif len(instances) == 1:
            chosen = instances[0]
        if chosen is None:
            parser.error("task has several instances: pass --instance <param_N>")
        spec = Path(manifest["spec"])
        config = Path(chosen["config"])
        negative_control = None

    cfg = read_cfg(config)
    cap_s = args.cap_s if args.cap_s is not None else float(manifest["budgets"]["wall_clock_s"])
    tool = {"name": "tlaplus", "tlc": probe_tlc_version(args.tlc_bin), "workers": args.workers}
    logs_dir = results_dir / "logs"
    logs_dir.mkdir(parents=True, exist_ok=True)

    for repetition in range(1, args.reps + 1):
        # The host load at the run's start (planner's ruling): a concurrent TLC inflates a Route A row the
        # same way it inflates a Route B one, and a reader cannot tell from the row alone. Paired at append.
        load_before = [round(value, 2) for value in os.getloadavg()]
        observation = run_tlc(
            spec, config,
            tlc_bin=args.tlc_bin, cap_s=cap_s, workers=args.workers,
            heap_mib=args.heap_mib, fp_index=args.fp_index, seed=args.seed,
        )
        observation["workers"] = args.workers
        stamp = time.strftime("%Y%m%dT%H%M%S")
        log_path = logs_dir / f"{task}{'-mutant' if args.mutant else ''}-{stamp}-r{repetition}.log"
        log_path.write_text("".join(observation["cmd"]) + "\n\n" + observation["log"])
        if negative_control is not None:
            negative_control = {**negative_control, "observed": observation["outcome"]}
        row = build_row(
            task=task,
            param_N=cfg["param_N"],
            property_name=cfg["property"],
            repetition=repetition,
            observation=observation,
            tool=tool,
            spec=spec,
            config=config,
            log_path=log_path,
            negative_control=negative_control,
        )
        append_row(results_dir, "tlc", row, load_before=load_before)
        print(
            f"{task}{'-mutant' if args.mutant else ''} r{repetition}: {row['outcome']} "
            f"in {row['wall_clock_s']}s"
            + (f", distinct={row['tlc']['distinct']}" if row["tlc"] else "")
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
