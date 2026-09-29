"""Scenarios 1-4 of tests/isolation-escape-contract.md.

The escape is measured, not hypothetical: a tier-2 arm attempt read another task's proved module by
absolute path, and a tier-1 pilot attempt read its own killed predecessor's working file, also by absolute
path. Scenario 1 is the layout half — with a control that fails on the current layout — Scenarios 2-3 are
the detection half, and Scenario 4 is the control that stops the detector firing on legitimate reads.
"""

import json
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import scripts.audit_attempts as audit_attempts  # noqa: E402
from scripts.audit_attempts import audit_attempt  # noqa: E402


def walk_up_for_proved(package: Path, task: str) -> Path | None:
    """The repository's template module as an upward walk from `package` would reach it, or None."""
    stem = "".join(part.title() for part in task.split("-"))
    for parent in [package, *package.parents]:
        candidate = parent / "proofs" / "lean" / task / f"{stem}Proved.lean"
        if candidate.exists():
            return candidate
    return None


def test_a_relative_walk_reaches_the_repository_in_the_current_layout():
    """Scenario 1, first half: the escape is real, so the layout half of this test can fail."""
    assert walk_up_for_proved(Path("harness"), "paxos") is not None


def test_the_same_walk_reaches_nothing_from_outside_the_repository(tmp_path):
    """Scenario 1, second half: a cell root outside the repository buys exactly this much."""
    outside = tmp_path / "cells" / "attempt-001" / "paxos"
    outside.mkdir(parents=True)
    assert walk_up_for_proved(outside, "paxos") is None


def build_attempt(tmp_path, *, siblings=(), command):
    """One attempt with a row and one transcript carrying a single tool call.

    ``command`` is called with the attempt's package path, so a fixture can name its own files without a
    placeholder pass.
    """
    stem = "Paxos"
    root = tmp_path / "cells" / "attempt-002"
    package = root / "workspaces" / "attempt-002" / "paxos"
    (package / ".runs").mkdir(parents=True)
    (package / f"{stem}.lean").write_text("theorem t : True := by\n  sorry\n")
    for name in siblings:
        (package / ".runs" / name).write_text("-- this attempt's own working copy\n")
    attempt = root / "results" / "attempt-002"
    session = attempt / "omp" / f"{stem}-20260928T000002-r1"
    (session / "file").mkdir(parents=True)
    record = {
        "type": "message",
        "message": {
            "content": [
                {
                    "type": "toolCall",
                    "name": "Bash",
                    "arguments": {"command": command(package), "cwd": None},
                }
            ]
        },
    }
    (session / "file" / "20260928T000002_ffff.jsonl").write_text(json.dumps(record) + "\n")
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
    return session, package


def test_an_absolute_read_of_another_tasks_proved_module_is_contaminated(tmp_path, monkeypatch):
    """Scenario 2: the measured leak, in the shape it arrived in."""
    monkeypatch.setattr(audit_attempts, "REPO", tmp_path)
    victim = tmp_path / "cells" / "attempt-001" / "workspaces" / "attempt-001" / "token-ring"
    victim.mkdir(parents=True)
    leaked = victim / "TokenRingProved.lean"
    leaked.write_text("theorem proven : True := by trivial\n")
    session, _ = build_attempt(tmp_path, command=lambda pkg: f"cat {leaked}")
    report = audit_attempt(session)
    assert report["verdict"] == "contaminated", report
    assert any(hit["class"] == "promoted-proof" for hit in report["offenders"]), report["offenders"]


def test_a_same_named_working_copy_in_another_cell_is_contaminated(tmp_path, monkeypatch):
    """Scenario 3: the name collision, which the name rule could not see and the path rule can."""
    monkeypatch.setattr(audit_attempts, "REPO", tmp_path)
    other = tmp_path / "cells" / "attempt-001" / "workspaces" / "attempt-001" / "paxos" / ".runs"
    other.mkdir(parents=True)
    prior = other / "Paxos-r1.lean"
    prior.write_text("-- a prior cell's working copy: same stem, same r1\n")
    session, _ = build_attempt(
        tmp_path, siblings=["Paxos-r1.lean"], command=lambda pkg: f"cat {prior}"
    )
    report = audit_attempt(session)
    assert report["verdict"] == "contaminated", report
    assert any(hit["class"] == "foreign-copy" for hit in report["offenders"]), report["offenders"]


def test_the_control_legitimate_reads_do_not_fire(tmp_path, monkeypatch):
    """Scenario 4: its own working copy and its declared dependency are the design, not reuse."""
    monkeypatch.setattr(audit_attempts, "REPO", tmp_path)
    # The declaration is read from the task's own registry, so the patched repository needs one: without
    # it the dependency read has nothing to be declared by and the control would fire for the wrong reason.
    registry = tmp_path / "proofs" / "lean" / "paxos"
    registry.mkdir(parents=True)
    (registry / "seeds.json").write_text(json.dumps({"Paxos.lean": "x", "PaxosProved.lean": "y"}) + "\n")

    def command(package):
        (package / "PaxosProved.lean").write_text("theorem proven : True := by trivial\n")
        return f"cat {package}/.runs/Paxos-r1.lean {package}/PaxosProved.lean"

    session, _ = build_attempt(tmp_path, siblings=["Paxos-r1.lean"], command=command)
    assert audit_attempt(session)["verdict"] == "clean"


# Scenario 5: the container half. The probe is identical in both cases and only the mount list differs,
# which is what makes the control meaningful: the boundary must hide the repository, and the fixture must
# still be looking when the repository is mounted at its real path.

PROBE = (
    "echo package: $(ls /work | tr '\\n' ' '); "
    "echo abs: $(ls {repo} 2>&1 | head -1); "
    "echo via-symlink: $(ls /work/.lake/packages 2>&1 | head -1); "
    "echo root: $(ls / | tr '\\n' ' ')"
)


def docker_probe(mounts):
    repo = Path(audit_attempts.REPO)
    return subprocess.run(
        ["docker", "run", "--rm", "--read-only", *mounts, "-w", "/work", "alpine",
         "sh", "-c", PROBE.format(repo=repo)],
        capture_output=True,
        text=True,
    )


def package_with_symlink(tmp_path):
    """A package whose `.lake/packages` symlink points at a real repository path, as the preparer's does."""
    package = tmp_path / "attempt" / "paxos"
    (package / ".lake").mkdir(parents=True)
    (package / ".runs").mkdir()
    (package / "Paxos.lean").write_text("theorem t : True := by\n  sorry\n")
    (package / ".lake" / "packages").symlink_to(Path(audit_attempts.REPO) / "proofs")
    return package


def test_docker_is_present_because_a_skipped_boundary_test_is_the_blindness_it_removes():
    """The container half asserts its own availability; skipping it would restore what it exists to remove."""
    assert shutil.which("docker") is not None, "no docker: the boundary half cannot be exercised"


def test_the_package_alone_leaves_the_repository_unreachable(tmp_path):
    """Scenario 5, first half: only the package is mounted."""
    package = package_with_symlink(tmp_path)
    probe = docker_probe(["-v", f"{package}:/work"])
    assert probe.returncode == 0, probe.stderr
    assert "Paxos.lean" in probe.stdout, probe.stdout  # the package itself is readable
    assert "No such file or directory" in probe.stdout, probe.stdout  # the repository absolute path is not
    # The error message names the path, so the discriminator is the repository's *content*, not its name.
    assert "docs" not in probe.stdout, probe.stdout
    assert "AGENTS.md" not in probe.stdout, probe.stdout


def test_the_control_with_the_repository_mounted_it_is_reachable(tmp_path):
    """Scenario 5, control: the same probe, with the repository mounted at its real path."""
    package = package_with_symlink(tmp_path)
    repo = Path(audit_attempts.REPO)
    probe = docker_probe(["-v", f"{package}:/work", "-v", f"{repo}:{repo}:ro"])
    assert probe.returncode == 0, probe.stderr
    # The discriminator is the error's *absence*: with the repository mounted, the same absolute path and
    # the same symlink resolve, so nothing reports "No such file or directory". Asserting on a specific
    # entry of the repository's listing would only pin the listing's order.
    assert "No such file or directory" not in probe.stdout, probe.stdout
    assert "package: Paxos.lean" in probe.stdout, probe.stdout
