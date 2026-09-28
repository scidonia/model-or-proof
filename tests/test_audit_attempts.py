"""Scenario 5 of tests/audit-boundary-contract.md: the declared-dependency exception.

A tier-1 arm is *given* its task's proved theorem by the preparer (the receipt lists it under
`included`), so reading it is the design. Every other `*Proved*` read is contamination, and an attempt
with no row declares nothing.
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.audit_attempts import audit_attempt  # noqa: E402


def build_attempt(tmp_path, *, tier, proved_module, own_module="PaxosN6Pilot.lean", with_row=True):
    """One attempt directory plus the row beside it, as the cell lays them out."""
    stem = Path(own_module).stem
    attempt = tmp_path / "results" / "attempt-001"
    package = tmp_path / "workspaces" / "attempt-001" / "paxos"
    package.mkdir(parents=True)
    (package / own_module).write_text("theorem t : True := by\n  sorry\n")
    if proved_module is not None:
        (package / proved_module).write_text("theorem proven : True := by trivial\n")
    session = attempt / "omp" / f"{stem}-20260928T000000-r1"
    (session / "file").mkdir(parents=True)
    record = {
        "type": "message",
        "message": {
            "content": [
                {
                    "type": "toolCall",
                    "name": "Bash",
                    "arguments": {
                        "command": f"cat {proved_module}" if proved_module else "true",
                        "cwd": None,
                    },
                }
            ]
        },
    }
    (session / "file" / "20260928T000000_abc.jsonl").write_text(json.dumps(record) + "\n")
    if with_row:
        (attempt / "proof.jsonl").write_text(
            json.dumps(
                {
                    "tier": tier,
                    "task": "paxos",
                    "artifacts": {"baseline": {"seed": str(package / own_module)}},
                }
            )
            + "\n"
        )
    return session


def test_tier1_declared_dependency_read_is_clean(tmp_path):
    """The preparer put it in the package; reading it is the design, not reuse."""
    session = build_attempt(tmp_path, tier=1, proved_module="PaxosProved.lean")
    report = audit_attempt(session)
    assert report["verdict"] == "clean", report
    hit = next(hit for hit in report["hits"] if hit["class"] == "promoted-proof")
    assert hit.get("declared") is True, hit


def test_tier1_read_of_a_foreign_proved_module_is_contamination(tmp_path):
    """Another task's proved theorem is not this attempt's dependency."""
    session = build_attempt(tmp_path, tier=1, proved_module="TokenRingProved.lean")
    assert audit_attempt(session)["verdict"] == "contaminated"


def test_tier2_read_of_the_proved_module_is_contamination(tmp_path):
    """A tier-2 attempt declares nothing: the prior proof must not be in its tree at all."""
    session = build_attempt(tmp_path, tier=2, proved_module="PaxosProved.lean")
    assert audit_attempt(session)["verdict"] == "contaminated"


def test_attempt_without_a_row_declares_nothing(tmp_path):
    """No row, no declaration: the exception is never assumed."""
    session = build_attempt(tmp_path, tier=1, proved_module="PaxosProved.lean", with_row=False)
    assert audit_attempt(session)["verdict"] == "contaminated"
