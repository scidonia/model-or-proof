"""Behavior scenarios for the file-mode closure oracle (tests/closure-oracle-contract.md)."""

import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO))

from harness.closure_oracle import check  # noqa: E402  (module location pinned by the coder)

SEED = REPO / "proofs" / "lean" / "token-ring" / "TokenRing.lean"
POSITIVE = REPO / "proofs" / "lean" / "token-ring" / "reference" / "SeedWithReferenceProof.lean"
PACKAGE = REPO / "proofs" / "lean" / "token-ring"
THEOREM = "TokenRing.mutex"

CORE_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def test_positive_fixture_demonstrates_closure():
    """Scenario 1: the positive fixture passes all three checks."""
    result = check(POSITIVE.read_text(), pristine=SEED.read_text(), package=PACKAGE, theorem=THEOREM)
    assert result["integrity"] is True, result
    assert result["elaborates"] is True, result
    assert result["closed"] is True, result
    assert result["axioms"] <= CORE_AXIOMS, result


def test_sorry_seed_compiles_but_is_not_closed():
    """Scenario 2: the untouched seed compiles but fails the axiom check (`sorryAx`)."""
    result = check(SEED.read_text(), pristine=SEED.read_text(), package=PACKAGE, theorem=THEOREM)
    assert result["integrity"] is True, result
    assert result["elaborates"] is True, result
    assert result["closed"] is False, result
    assert "sorryAx" in result["axioms"], result


def test_altered_prefix_fails_integrity():
    """Scenario 3: a candidate whose prefix differs from the seed fails integrity."""
    seed_text = SEED.read_text()
    altered = "theorem fake : True := by trivial\n" + seed_text
    result = check(altered, pristine=seed_text, package=PACKAGE, theorem=THEOREM)
    assert result["integrity"] is False, result
