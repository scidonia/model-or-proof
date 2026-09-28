"""Scenario 5 of tests/audit-boundary-contract.md: the declared-dependency exception.

A tier-1 arm is *given* its task's proved theorem by the preparer (the receipt lists it under
`included`), so reading it is the design. Every other `*Proved*` read is contamination, and an attempt
with no row declares nothing.
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import scripts.audit_attempts as audit_attempts
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


def build_sibling_jsonl_read(tmp_path, *, transcript):
    """An attempt whose only artifact-touching call reads a .jsonl belonging to another attempt."""
    stem = "PaxosN6Pilot"
    attempt = tmp_path / "results" / "attempt-001"
    package = tmp_path / "workspaces" / "attempt-001" / "paxos"
    package.mkdir(parents=True)
    (package / f"{stem}.lean").write_text("theorem t : True := by\n  sorry\n")
    (package / "PaxosProved.lean").write_text("theorem proven : True := by trivial\n")
    sibling = tmp_path / "results" / "attempt-000"
    if transcript:
        sibling = sibling / "omp" / f"{stem}-20260928T000000-r1" / "file"
        sibling.mkdir(parents=True)
        target = sibling / "2026-09-28T20-34-41-298Z_01a0e9ba-1412-76ee-8702-95016d4cbed4.jsonl"
    else:
        sibling.mkdir(parents=True)
        target = sibling / "proof.jsonl"
    target.write_text('{"tier": 1}\n')
    session = attempt / "omp" / f"{stem}-20260928T000001-r1"
    (session / "file").mkdir(parents=True)
    record = {
        "type": "message",
        "message": {
            "content": [
                {
                    "type": "toolCall",
                    "name": "Bash",
                    "arguments": {"command": f"cat {target}", "cwd": None},
                }
            ]
        },
    }
    (session / "file" / "20260928T000001_cccc.jsonl").write_text(json.dumps(record) + "\n")
    (attempt / "proof.jsonl").write_text(
        json.dumps(
            {
                "tier": 1,
                "task": "paxos",
                "artifacts": {"baseline": {"seed": str(package / f"{stem}.lean")}},
            }
        )
        + "\n"
    )
    return session


def test_a_prior_attempts_row_is_metadata_not_a_transcript(tmp_path):
    """A row is the run's record, not its reasoning: reading it is not proof reuse."""
    session = build_sibling_jsonl_read(tmp_path, transcript=False)
    report = audit_attempt(session)
    assert report["verdict"] == "clean", report
    assert [hit for hit in report["hits"] if hit["class"] == "other-transcript"] == []


def test_a_prior_attempts_transcript_still_contaminates(tmp_path):
    """The guard-rail: the exception is about the file kind, not about dropping the class."""
    session = build_sibling_jsonl_read(tmp_path, transcript=True)
    assert audit_attempt(session)["verdict"] == "contaminated"


def build_working_copy_read(tmp_path, *, foreign, with_row=True):
    """An attempt whose only artifact-touching call reads a `<stem>-r1.lean` working copy.

    The reader is attempt-002 at repetition 1; the file it reads is either its own package's or a sibling's,
    and the sibling's has the same stem and the same repetition number — which is the collision, since every
    attempt and every cell starts at `r1`.
    """
    stem = "Paxos"
    mine = tmp_path / "workspaces" / "attempt-002" / "paxos"
    theirs = tmp_path / "workspaces" / "attempt-001" / "paxos"
    for package in (mine, theirs):
        (package / ".runs").mkdir(parents=True, exist_ok=True)
        (package / f"{stem}.lean").write_text("theorem t : True := by\n  sorry\n")
    (mine / ".runs" / f"{stem}-r1.lean").write_text("-- own\n")
    (theirs / ".runs" / f"{stem}-r1.lean").write_text("-- sibling\n")
    target = (theirs if foreign else mine) / ".runs" / f"{stem}-r1.lean"
    attempt = tmp_path / "results" / "attempt-002"
    session = attempt / "omp" / f"{stem}-20260928T000002-r1"
    (session / "file").mkdir(parents=True)
    record = {
        "type": "message",
        "message": {
            "content": [
                {
                    "type": "toolCall",
                    "name": "Bash",
                    "arguments": {"command": f"cat {target}", "cwd": None},
                }
            ]
        },
    }
    (session / "file" / "20260928T000002_dddd.jsonl").write_text(json.dumps(record) + "\n")
    if with_row:
        (attempt / "proof.jsonl").write_text(
            json.dumps(
                {
                    "tier": 1,
                    "task": "paxos",
                    "artifacts": {"baseline": {"seed": str(mine / f"{stem}.lean")}},
                }
            )
            + "\n"
        )
    return session


def test_reading_its_own_working_copy_is_clean(tmp_path, monkeypatch):
    """The normal case: an attempt reading its own `.runs/` file is ordinary, not a violation."""
    monkeypatch.setattr(audit_attempts, "REPO", tmp_path)
    session = build_working_copy_read(tmp_path, foreign=False)
    assert audit_attempt(session)["verdict"] == "clean"


def test_reading_a_siblings_identically_named_working_copy_contaminates(tmp_path, monkeypatch):
    """Same name, same repetition, different package: the name cannot tell them apart, the path can."""
    monkeypatch.setattr(audit_attempts, "REPO", tmp_path)
    session = build_working_copy_read(tmp_path, foreign=True)
    report = audit_attempt(session)
    assert report["verdict"] == "contaminated", report
    assert any(hit["class"] == "foreign-copy" for hit in report["offenders"]), report["offenders"]


def test_the_harnesss_own_echo_of_the_working_file_is_clean(tmp_path, monkeypatch):
    """An attempt reading the copy the harness wrote into its own results tree is still reading its own."""
    monkeypatch.setattr(audit_attempts, "REPO", tmp_path)
    stem = "Paxos"
    mine = tmp_path / "workspaces" / "attempt-002" / "paxos"
    mine.mkdir(parents=True)
    (mine / f"{stem}.lean").write_text("theorem t : True := by\n  sorry\n")
    attempt = tmp_path / "results" / "attempt-002"
    session = attempt / "omp" / f"{stem}-20260928T000002-r1"
    (session / "file").mkdir(parents=True)
    echoed = session / f"{stem}-r1.lean"  # the runner's copy, inside the attempt's own results tree
    echoed.write_text("-- echo of the working file\n")
    record = {
        "type": "message",
        "message": {
            "content": [
                {
                    "type": "toolCall",
                    "name": "Bash",
                    "arguments": {"command": f"cat {echoed}", "cwd": None},
                }
            ]
        },
    }
    (session / "file" / "20260928T000002_eeee.jsonl").write_text(json.dumps(record) + "\n")
    (attempt / "proof.jsonl").write_text(
        json.dumps(
            {"tier": 1, "task": "paxos", "artifacts": {"baseline": {"seed": str(mine / f"{stem}.lean")}}}
        )
        + "\n"
    )
    assert audit_attempt(session)["verdict"] == "clean"


def test_without_a_row_the_working_copy_rule_falls_back(tmp_path, monkeypatch):
    """No row, no package: keep the name rule rather than flag every attempt's own read."""
    monkeypatch.setattr(audit_attempts, "REPO", tmp_path)
    session = build_working_copy_read(tmp_path, foreign=True, with_row=False)
    report = audit_attempt(session)
    assert report["verdict"] == "clean"
    assert any(hit["class"] == "own-copy" for hit in report["hits"]), report["hits"]
