"""Behavior scenarios for the token-ring equivalence audit (tests/equivalence-token-ring-contract.md)."""

from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
AUDIT = REPO / "docs" / "equivalence-token-ring.md"

OPERATORS = ["Nodes", "TypeOK", "Init", "Request", "Enter", "Release", "Next", "Mutex", "Spec"]


def text():
    return AUDIT.read_text()  # FileNotFoundError before the audit is written (the expected red run).


def table_rows(audit):
    """Parse the correspondence table (a markdown table with a 'TLA+ | Lean' header)."""
    lines = audit.splitlines()
    rows = {}
    in_table = False
    for line in lines:
        stripped = line.strip()
        if stripped.startswith("|") and ("TLA+" in stripped or "operator" in stripped.lower()) and "lean" in stripped.lower():
            in_table = True
            continue
        if in_table and stripped.startswith("|") and "---" not in stripped:
            cells = [c.strip() for c in stripped.strip("|").split("|")]
            if len(cells) >= 2 and cells[0]:
                rows[cells[0]] = cells[1]
            continue
        if in_table and not stripped.startswith("|"):
            break
    return rows


def test_every_operator_has_a_lean_correspondence():
    """Scenario 1: every operator is a row in the correspondence table with a non-empty Lean side."""
    rows = table_rows(text())
    for op in OPERATORS:
        assert op in rows, f"operator {op} is not a row of the correspondence table"
        assert rows[op], f"operator {op} has an empty Lean correspondence"


def test_tiers_and_faithfulness_are_stated():
    """Scenario 2: the two Lean statements and the no-strengthen/no-weaken claim are named."""
    audit = text()
    assert "mutex" in audit, "the general theorem's Lean statement is not named"
    assert "mutex_n0" in audit or "mutexN0" in audit, "the N0 corollary's Lean statement is not named"
    assert "strengthen" in audit.lower(), "no-strengthen guarantee not stated"
    assert "weaken" in audit.lower(), "no-weaken guarantee not stated"
