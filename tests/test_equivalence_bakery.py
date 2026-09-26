"""Behavior scenarios for the Bakery equivalence audit (tests/equivalence-bakery-contract.md)."""

from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
AUDIT = REPO / "docs" / "equivalence-bakery.md"

OPERATORS = [
    "P", "TypeOK", "Init", "LL", "SetFlag", "ChooseTicket", "Enter", "Exit",
    "Next", "MutualExclusion", "Spec",
]


def text():
    return AUDIT.read_text()  # FileNotFoundError before the audit is written (the expected red run).


def table_rows(audit):
    """Parse the correspondence table (a pipe-table whose header names TLA+/operator and Lean)."""
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
    """Scenario 1: every Bakery operator is a row of the correspondence table with a non-empty Lean side."""
    rows = table_rows(text())
    for op in OPERATORS:
        assert op in rows, f"operator {op} is not a row of the correspondence table"
        assert rows[op], f"operator {op} has an empty Lean correspondence"


def test_general_theorem_and_faithfulness_are_stated():
    """Scenario 2: the general theorem, the named corollary, and the faithfulness claim are named."""
    audit = text()
    assert "mutual_exclusion" in audit, "the general theorem's Lean statement is not named"
    assert "strengthen" in audit.lower(), "no-strengthen guarantee not stated"
    assert "weaken" in audit.lower(), "no-weaken guarantee not stated"
    assert "mutual_exclusion_n0" in audit, "the N0 corollary is not named"
