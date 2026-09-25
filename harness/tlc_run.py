"""Route A: run one TLA+ task under TLC and emit a result row (docs/protocol.md §6, §7).

The row is the measurement. Its numbers come from TLC's final summary and from nothing else: a
progress line is a running count, not an answer, and a killed run is a timeout rather than a verdict.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import signal
import subprocess
import sys
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
CFG_CONSTANT_RE = re.compile(r"(?m)^\s*CONSTANT\s+N\s*=\s*(\d+)")
CFG_INVARIANT_RE = re.compile(r"(?m)^\s*INVARIANTS?\s+(\S+)")
TLC_VERSION_RE = re.compile(r"Version ([\d.]+) of")


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

    TLC's launcher shell leaves the JVM in a child process; killing only the shell leaves the pipe
    open, so the reader waits for a process nobody is waiting for and the run's wall-clock is wrong.
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
) -> dict:
    """Run TLC over one instance, capped at ``cap_s`` seconds, and return the raw observation."""
    spec = Path(spec).resolve()
    config = Path(config).resolve()
    # The runner sets the child's cwd to the spec's directory, so a relative binary path would no
    # longer resolve: make the interpreter's own resolution explicit before launching.
    if os.sep in tlc_bin or Path(tlc_bin).exists():
        tlc_bin = str(Path(tlc_bin).resolve())
    cmd = [tlc_bin, "-workers", str(workers), "-cleanup", "-config", str(config), str(spec)]

    started = time.monotonic()
    proc = subprocess.Popen(
        cmd,
        cwd=str(spec.parent),
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

    wall_clock_s = round(time.monotonic() - started, 3)
    log = "".join(lines)
    parsed = parse_tlc_log(log)

    if state["timed_out"]:
        outcome = "timeout"
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
        "log": log,
        "cmd": cmd,
    }


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
    completed = parsed["generated"] is not None
    return {
        "task": task,
        "route": "tlc",
        "tool": tool,
        "param_N": param_N,
        "property": property_name,
        "tier": 1,
        "repetition": repetition,
        "outcome": observation["outcome"],
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
        observation = run_tlc(spec, config, tlc_bin=args.tlc_bin, cap_s=cap_s, workers=args.workers)
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
        append_row(results_dir, "tlc", row)
        print(
            f"{task}{'-mutant' if args.mutant else ''} r{repetition}: {row['outcome']} "
            f"in {row['wall_clock_s']}s"
            + (f", distinct={row['tlc']['distinct']}" if row["tlc"] else "")
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
