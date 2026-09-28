"""Structural contracts for independent Paxos attempt preparation (see matching .md)."""

import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[1]
OLD_PROOF = "PRIOR_ATTEMPT_PROOF_MUST_NOT_BE_VISIBLE"
SEED = "import Mathlib\nnamespace Paxos\ntheorem agreement : True := by\n  sorry\nend Paxos\n"


def template_package(tmp_path):
    package = tmp_path / "template"
    (package / "baseline").mkdir(parents=True)
    (package / ".lake" / "packages" / "mathlib").mkdir(parents=True)
    (package / ".lake" / "packages" / "mathlib" / "Mathlib.lean").write_text("-- cache marker\n")
    (package / "Paxos.lean").write_text(SEED)
    (package / "baseline" / "Paxos.lean").write_text(SEED)
    (package / "seeds.json").write_text(json.dumps({"Paxos.lean": hashlib.sha256(SEED.encode()).hexdigest()}))
    (package / "lean-toolchain").write_text("leanprover/lean4:v4.35.0-rc3\n")
    (package / "lakefile.toml").write_text('name = "paxos"\n')
    (package / "lake-manifest.json").write_text("{}\n")
    (package / "PaxosProved.lean").write_text(OLD_PROOF)
    (package / ".runs").mkdir()
    (package / ".runs" / "Paxos-r1.lean").write_text(OLD_PROOF)
    (package / ".runs" / "proof_body.txt").write_text(OLD_PROOF)
    (package / "results" / "closures").mkdir(parents=True)
    (package / "results" / "closures" / "old.lean").write_text(OLD_PROOF)
    return package


def prepare(tmp_path, template, attempt, *extra):
    env = dict(os.environ, PYTHONPATH=str(REPO))
    return subprocess.run(
        [
            sys.executable, "-m", "harness.attempt_workspace", "prepare",
            "--template", str(template), "--seed", "Paxos.lean", "--attempt", str(attempt),
            *extra,
            "--workspace-root", str(tmp_path / "workspaces"),
            "--results-root", str(tmp_path / "results"),
        ],
        cwd=REPO, env=env, capture_output=True, text=True, timeout=30,
    )


def assert_clean_package(package):
    assert not (package / "PaxosProved.lean").exists()
    assert not (package / "results").exists()
    runs = package / ".runs"
    assert not runs.exists() or not any(runs.iterdir())
    assert OLD_PROOF not in "\n".join(
        path.read_text() for path in package.rglob("*") if path.is_file() and not path.is_symlink()
    )


def test_first_attempt_excludes_old_proof_and_reuses_dependency_cache(tmp_path):
    template = template_package(tmp_path)
    proc = prepare(tmp_path, template, 1)
    assert proc.returncode == 0, proc.stderr
    receipt = json.loads(proc.stdout)
    package = Path(receipt["package"])
    results = Path(receipt["results"])
    assert package.is_absolute() and results.is_absolute()
    assert Path(receipt["seed"]).is_absolute()
    assert receipt["attempt"] == 1
    assert package.name == "paxos"
    assert package.parent.name == "attempt-001"
    assert Path(receipt["seed"]) == package / "Paxos.lean"
    assert receipt["seed_sha256"] == hashlib.sha256(SEED.encode()).hexdigest()
    assert (package / "Paxos.lean").read_text() == SEED
    assert (package / "baseline" / "Paxos.lean").read_text() == SEED
    assert json.loads((package / "seeds.json").read_text())["Paxos.lean"] == receipt["seed_sha256"]
    assert (package / ".lake" / "packages").is_symlink()
    assert (package / ".lake" / "packages").resolve() == (template / ".lake" / "packages").resolve()
    assert not results.is_relative_to(package)
    assert_clean_package(package)


def test_next_attempt_starts_clean_without_deleting_prior_evidence(tmp_path):
    template = template_package(tmp_path)
    first = prepare(tmp_path, template, 1)
    assert first.returncode == 0, first.stderr
    first_receipt = json.loads(first.stdout)
    first_package = Path(first_receipt["package"])
    first_results = Path(first_receipt["results"])
    (first_package / ".runs").mkdir(exist_ok=True)
    (first_package / ".runs" / "Paxos-r1.lean").write_text(OLD_PROOF)
    (first_package / ".runs" / "proof_body.txt").write_text(OLD_PROOF)
    (first_results / "closures").mkdir(parents=True)
    (first_results / "closures" / "Paxos-r1.lean").write_text(OLD_PROOF)

    second = prepare(tmp_path, template, 2)
    assert second.returncode == 0, second.stderr
    second_receipt = json.loads(second.stdout)
    second_package = Path(second_receipt["package"])
    second_results = Path(second_receipt["results"])
    assert second_package != first_package
    assert second_results != first_results
    assert second_receipt["attempt"] == 2
    assert second_receipt["seed_sha256"] == first_receipt["seed_sha256"]
    assert_clean_package(second_package)
    assert not second_results.is_relative_to(second_package)
    assert not second_results.exists() or not any(second_results.iterdir())
    assert (first_package / ".runs" / "Paxos-r1.lean").read_text() == OLD_PROOF
    assert (first_results / "closures" / "Paxos-r1.lean").read_text() == OLD_PROOF

    duplicate = prepare(tmp_path, template, 2)
    assert duplicate.returncode != 0
    assert (second_package / "Paxos.lean").read_text() == SEED


@pytest.mark.parametrize(
    ("pinned", "mode"),
    [
        ("lean-toolchain", "missing"),
        ("lake-manifest.json", "missing"),
        ("lakefile.toml", "missing"),
        ("lean-toolchain", "directory"),
        ("lake-manifest.json", "directory"),
        ("lakefile.toml", "directory"),
    ],
)
def test_incomplete_pinned_package_metadata_refuses_cleanly(tmp_path, pinned, mode):
    template = template_package(tmp_path)
    (template / pinned).unlink()
    if mode == "directory":
        (template / pinned).mkdir()

    proc = prepare(tmp_path, template, 1)

    assert proc.returncode == 2, proc.stderr
    assert pinned in proc.stderr
    assert not (tmp_path / "workspaces" / "attempt-001").exists()
    assert not (tmp_path / "results" / "attempt-001").exists()


PROVED = "namespace Paxos\ntheorem agreement : True := by\n  trivial\nend Paxos\n"


def promoted_template_package(tmp_path):
    """A template as promotion leaves one: seeds.json registers a Proved module carrying a completed
    proof of the attempted statement, while baseline/ holds only the attempted seed's pristine text —
    promotion never re-pins a baseline for the proved module.
    """
    package = template_package(tmp_path)
    (package / "PaxosProved.lean").write_text(PROVED)
    record = json.loads((package / "seeds.json").read_text())
    record["PaxosProved.lean"] = hashlib.sha256(PROVED.encode()).hexdigest()
    (package / "seeds.json").write_text(json.dumps(record))
    (package / "lakefile.toml").write_text(
        'name = "paxos"\n'
        'defaultTargets = ["Paxos", "PaxosProved"]\n\n'
        '[[lean_lib]]\nname = "Paxos"\n\n'
        '[[lean_lib]]\nname = "PaxosProved"\n\n'
        '[[require]]\nname = "mathlib"\ngit = "https://example.invalid/mathlib4"\nrev = "v4.35.0-rc3"\n'
    )
    return package


def test_tier2_package_withholds_an_undeclared_registered_proof_seed(tmp_path):
    """Scenario 4: a tier-2 attempt's tree must not offer a completed proof of its own theorem."""
    template = promoted_template_package(tmp_path)

    proc = prepare(tmp_path, template, 1)

    assert proc.returncode == 0, proc.stderr
    receipt = json.loads(proc.stdout)
    package = Path(receipt["package"])
    assert (package / "Paxos.lean").is_file()
    assert (package / "baseline" / "Paxos.lean").is_file()
    assert not (package / "PaxosProved.lean").exists()
    assert not (package / "baseline" / "PaxosProved.lean").exists()
    assert "PaxosProved" not in (package / "lakefile.toml").read_text()
    assert set(receipt["modules"]["included"]) == {"Paxos.lean"}
    assert set(receipt["modules"]["withheld"]) == {"PaxosProved.lean"}


def test_tier1_package_copies_the_declared_dependency_without_a_baseline(tmp_path):
    """Scenario 4: the same module is the tier-1 arm's intended dependency, declared rather than absent."""
    template = promoted_template_package(tmp_path)

    proc = prepare(tmp_path, template, 1, "--dependency", "PaxosProved.lean")

    assert proc.returncode == 0, proc.stderr
    receipt = json.loads(proc.stdout)
    package = Path(receipt["package"])
    assert (package / "PaxosProved.lean").read_text() == PROVED
    assert not (package / "baseline" / "PaxosProved.lean").exists()
    assert 'name = "PaxosProved"' in (package / "lakefile.toml").read_text()
    assert set(receipt["modules"]["included"]) == {"Paxos.lean", "PaxosProved.lean"}
    assert set(receipt["modules"]["withheld"]) == set()
