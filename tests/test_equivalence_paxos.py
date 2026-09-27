"""Structural audit contracts; semantic equivalence requires the documented manual review."""

import json
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
AUDIT = REPO / "docs" / "equivalence-paxos.md"
CLAUSES = (
    "Acceptors", "Values", "Quorums", "QuorumAssumption", "Ballots", "vars",
    "Send", "None", "Init", "Phase1a", "Phase1b", "Phase2a", "Phase2b",
    "Next", "Spec", "VotedForIn", "ChosenIn", "Chosen", "Consistency",
    "Messages", "TypeOK",
)


def table(audit: str, heading: str) -> dict[str, list[str]]:
    section = audit.split(heading, 1)[1].split("\n## ", 1)[0]
    rows = {}
    for line in section.splitlines():
        if line.startswith("|") and "---" not in line:
            cells = [part.strip() for part in line.strip("|").split("|")]
            if cells and cells[0] in CLAUSES:
                rows[cells[0]] = cells[1:]
    return rows


def test_import_to_finite_projection_maps_all_agreement_clauses():
    rows = table(AUDIT.read_text(), "## 1. Imported Paxos → finite TLC projection")
    for clause in CLAUSES:
        assert clause in rows, f"{clause} is missing from the source/projection audit"
        assert len(rows[clause]) >= 2 and all(rows[clause][:2]), clause


def test_projection_to_unbounded_lean_maps_all_agreement_clauses():
    rows = table(AUDIT.read_text(), "## 2. Finite projection → Lean model")
    for clause in CLAUSES:
        assert clause in rows, f"{clause} is missing from the projection/Lean audit"
        assert len(rows[clause]) >= 2 and all(rows[clause][:2]), clause


def test_human_comparator_is_identified_as_distinct_first_refinement():
    audit = AUDIT.read_text()
    human = next(
        json.loads(line) for line in (REPO / "results" / "human.jsonl").read_text().splitlines()
        if json.loads(line)["record_id"] == "ijcar2010-paxos"
    )
    first, second = human["figures"]
    assert first["proof"] == "first_refinement_safety" and first["value"] == 550
    assert second["proof"] == "second_refinement" and second["partial"] is True
    assert "550 lines" in audit and "first refinement" in audit.lower()
    assert "incomplete" in audit.lower() and "not identical" in audit.lower()
    assert "530" in audit and "22" in audit
