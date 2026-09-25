"""Behavior scenarios for the TLC runner (tests/tlc-run-contract.md)."""

import json
import os
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
TASK = REPO / "tasks" / "token-ring.json"
FIXTURES = Path(__file__).resolve().parent / "fixtures"


def run_runner(tmp_path, *extra, timeout=180):
    """Invoke the runner as the researcher does: a command line, from the repository root."""
    env = dict(os.environ)
    env["PYTHONPATH"] = str(REPO)
    proc = subprocess.run(
        [sys.executable, "-m", "harness.tlc_run", "--task", str(TASK), "--results", str(tmp_path), *extra],
        cwd=REPO,
        env=env,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    return proc


def rows(tmp_path):
    path = tmp_path / "tlc.jsonl"
    assert path.exists(), f"no result rows written; runner stderr:\n"
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def test_completed_check_yields_success_row(tmp_path):
    """Scenario 1: a completed check yields a success row with TLC's final counts."""
    proc = run_runner(tmp_path, "--reps", "1")
    assert proc.returncode == 0, proc.stderr

    rows_ = rows(tmp_path)
    assert len(rows_) == 1
    row = rows_[0]
    assert row["task"] == "token-ring"
    assert row["route"] == "tlc"
    assert row["outcome"] == "success"
    assert row["param_N"] == 3
    assert row["tlc"] == {
        "generated": 73,
        "distinct": 36,
        "left": 0,
        "depth": 11,
        "workers": 1,
    }
    assert row["wall_clock_s"] > 0
    assert 0 <= row["startup_s"] <= row["wall_clock_s"]
    assert Path(row["artifacts"]["log"]).exists()


def test_progress_lines_are_not_the_final_summary(tmp_path):
    """Scenario 2: progress lines are never mistaken for the final summary."""
    from harness.tlc_run import parse_tlc_log

    log = (FIXTURES / "tlc_progress_then_summary.log").read_text()
    parsed = parse_tlc_log(log)

    assert parsed["generated"] == 73
    assert parsed["distinct"] == 36
    assert parsed["left"] == 0
    assert parsed["depth"] == 11
    assert parsed["states_reached"] == 36


def test_violated_invariant_yields_violation_row(tmp_path):
    """Scenario 3: a violated invariant yields a violation row carrying the trace."""
    proc = run_runner(tmp_path, "--mutant")
    assert proc.returncode == 0, proc.stderr

    row = rows(tmp_path)[0]
    assert row["outcome"] == "violation"
    assert row["param_N"] == 3
    log = Path(row["artifacts"]["log"])
    assert log.exists()
    assert "is violated" in log.read_text()


def test_killed_run_is_a_timeout_not_a_verdict(tmp_path):
    """Scenario 4: a killed run is a timeout, not a verdict."""
    proc = run_runner(
        tmp_path,
        "--tlc-bin",
        str(FIXTURES / "fake_tlc_slow.sh"),
        "--cap-s",
        "1",
        timeout=60,
    )
    assert proc.returncode == 0, proc.stderr

    row = rows(tmp_path)[0]
    assert row["outcome"] == "timeout"
    assert row["states_reached"] == 337897
    assert row["tlc"] is None
    assert Path(row["artifacts"]["log"]).exists()
