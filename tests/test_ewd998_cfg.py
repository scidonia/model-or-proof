"""Behavior scenarios for the cfg parser's EWD998 block forms (tests/ewd998-cfg-contract.md)."""

from pathlib import Path

REPO = Path(__file__).resolve().parents[1]

from harness.tlc_run import read_cfg  # noqa: E402


def test_ewd998_small_cfg_parses_n3():
    """Scenario 1: the paper's N = 3 instance parses."""
    cfg = read_cfg(REPO / "specs" / "tla" / "ewd998" / "EWD998Small.cfg")
    assert cfg["param_N"] == 3, cfg
    assert cfg["property"] == "TerminationDetection", cfg


def test_ewd998_cfg_parses_n4():
    """Scenario 2: the branch's N = 4 config parses."""
    cfg = read_cfg(REPO / "specs" / "tla" / "ewd998" / "EWD998.cfg")
    assert cfg["param_N"] == 4, cfg
    assert cfg["property"] == "TerminationDetection", cfg


def test_token_ring_single_line_still_parses():
    """Scenario 3: the single-line CONSTANT form still parses (regression)."""
    cfg = read_cfg(REPO / "specs" / "tla" / "token-ring" / "TokenRing.cfg")
    assert cfg["param_N"] == 3, cfg
    assert cfg["property"] == "Mutex", cfg
