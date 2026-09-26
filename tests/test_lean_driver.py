"""Behavior scenarios for the Lean prover driver (tests/lean-driver-contract.md)."""

import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO))

from harness.lean_repl import LeanReplProver, count_unclosed  # noqa: E402


def test_unclosed_assertion_counts_every_spelling():
    """Scenario 1: count_unclosed flags every Lean spelling of an unclosed goal."""
    for token in ("sorry", "sorryAx", "admit", "Admitted", "axiom"):
        assert count_unclosed(token) > 0, token
    assert count_unclosed("theorem t : True := by\n  trivial\n") == 0


def test_unclosed_ignores_comments_and_strings():
    """A `sorry` mentioned only in a comment or string literal counts zero."""
    assert count_unclosed("-- the sorry below is the seed's placeholder\ntheorem t : True := by trivial") == 0
    assert count_unclosed("/- a sorry in a block comment -/\ntheorem t : True := by trivial") == 0
    assert count_unclosed('theorem t : True := by\n  exact "sorry"\n') == 0


def test_unclosed_handles_comment_and_identifier_edge_cases():
    """Nested/doc comments, metavariables, identifier boundaries, and unterminated literals."""
    assert count_unclosed("/- outer /- sorry -/ -/") == 0  # nested block comment
    assert count_unclosed("/-- sorry -/") == 0  # doc comment
    assert count_unclosed("/-! sorry -/") == 0  # doc comment
    assert count_unclosed("theorem t : True := by\n  exact ?h\n") > 0  # a metavariable is a hole
    assert count_unclosed("def sorryful : Nat := 1") == 0  # a longer identifier is not the word
    assert count_unclosed("theorem t : True := by\n  sorry\n/- unterminated") > 0  # unterminated comment must not hide a real sorry


def _responder(response):
    """A scripted repl responder returning one fixed response dict per command."""
    return lambda cmd: response


def test_driver_parses_open_goals():
    """Scenario 2: the driver reads goals from the responder and reports them open."""
    prover = LeanReplProver(
        Path("x.lean"),
        ["repl"],
        responder=_responder({"proofStatus": "Incomplete", "goals": ["⊢ 0 < 1", "⊢ 1 < 2"]}),
    )
    prover.start()
    assert prover.goals() == ["⊢ 0 < 1", "⊢ 1 < 2"]
    assert prover.unclosed() == 2


def test_driver_detects_closure_on_completed():
    """Scenario 3: goals=[] with a completed status is closure."""
    prover = LeanReplProver(
        Path("x.lean"),
        ["repl"],
        responder=_responder({"proofStatus": "Completed", "goals": []}),
    )
    prover.start()
    assert prover.unclosed() == 0


def test_driver_rejects_the_sorry_shape():
    """Scenario 4: goals=[] with 'Incomplete: contains sorry' is NOT closure."""
    prover = LeanReplProver(
        Path("x.lean"),
        ["repl"],
        responder=_responder({"proofStatus": "Incomplete: contains sorry", "goals": []}),
    )
    prover.start()
    assert prover.unclosed() > 0


def test_driver_does_not_treat_a_missing_goals_key_as_closed():
    """Scenario 5: a malformed response with no goals key is not silently treated as closed."""
    prover = LeanReplProver(
        Path("x.lean"),
        ["repl"],
        responder=_responder({"proofStatus": "Completed"}),
    )
    prover.start()
    assert prover.unclosed() > 0  # never "closed" on a response the driver could not read


def test_unreadable_completion_status_is_a_transport_refusal():
    """Scenario 6: no readable proofStatus -> a transport refusal, not a Lean one."""
    prover = LeanReplProver(
        Path("x.lean"),
        ["repl"],
        responder=_responder({"goals": [], "proofState": 1}),  # no `proofStatus` field
    )
    prover.start()
    assert [f["kind"] for f in prover.failures] == ["transport"], prover.failures
    assert "status" in prover.failures[0]["message"].lower(), prover.failures


def test_unrecognised_status_string_is_a_transport_refusal():
    """Scenario 6: a proofStatus that is not Completed/Incomplete is the same transport refusal."""
    prover = LeanReplProver(
        Path("x.lean"),
        ["repl"],
        responder=_responder({"goals": [], "proofStatus": "Weird"}),
    )
    prover.start()
    assert [f["kind"] for f in prover.failures] == ["transport"], prover.failures


def test_contains_sorry_judgment_is_a_lean_refusal():
    """Scenario 7: a recognised 'contains sorry' judgment is a lean refusal, not transport."""
    prover = LeanReplProver(
        Path("x.lean"),
        ["repl"],
        responder=_responder({"goals": [], "proofStatus": "Incomplete: contains sorry"}),
    )
    prover.start()
    assert [f["kind"] for f in prover.failures] == ["lean"], prover.failures
    assert "sorry" in prover.failures[0]["message"].lower(), prover.failures


def _capturing_responder(seen, response):
    """A responder that records the payload it is handed, then answers with the fixed response."""
    def responder(cmd):
        seen.append(cmd)
        return response
    return responder


def test_semicolon_sequence_is_handed_over_parenthesised():
    """Scenario 8: a `;`-sequence reaches the repl parenthesised (Lean's `tactic` category has no `;`)."""
    seen = []
    prover = LeanReplProver(
        Path("x.lean"),
        ["repl"],
        responder=_capturing_responder(seen, {"proofStatus": "Incomplete", "goals": ["⊢ True"], "proofState": 0}),
    )
    prover.start()
    seen.clear()
    prover.apply("skip; skip")
    assert seen[-1]["tactic"] == "(skip; skip)", seen[-1]


def test_plain_and_exact_by_tactics_are_handed_over_unchanged():
    """Scenario 8: non-`;` tactics (a plain tactic, an `exact by` block) are handed over byte-exact."""
    seen = []
    prover = LeanReplProver(
        Path("x.lean"),
        ["repl"],
        responder=_capturing_responder(seen, {"proofStatus": "Incomplete", "goals": ["⊢ True"], "proofState": 0}),
    )
    prover.start()
    seen.clear()
    prover.apply("skip")
    prover.apply("exact by\n  omega")
    assert [c["tactic"] for c in seen] == ["skip", "exact by\n  omega"], seen
