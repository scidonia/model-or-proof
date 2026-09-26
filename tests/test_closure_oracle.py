"""Behavior scenarios for the file-mode closure oracle (tests/closure-oracle-contract.md)."""

import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO))

from harness.closure_oracle import check  # noqa: E402  (module location pinned by the coder)

BASELINE = REPO / "proofs" / "lean" / "token-ring" / "baseline" / "TokenRing.lean"
POSITIVE = REPO / "proofs" / "lean" / "token-ring" / "reference" / "SeedWithReferenceProof.lean"
PACKAGE = REPO / "proofs" / "lean" / "token-ring"
THEOREM = "TokenRing.mutex"
MODULE = "TokenRing"

CORE_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def test_positive_fixture_demonstrates_closure():
    """Scenario 1: the positive fixture passes all three checks."""
    result = check(POSITIVE.read_text(), pristine=BASELINE.read_text(), package=PACKAGE, module=MODULE, theorem=THEOREM)
    assert result["integrity"] is True, result
    assert result["elaborates"] is True, result
    assert result["closed"] is True, result
    assert result["axioms"] <= CORE_AXIOMS, result


def test_sorry_seed_compiles_but_is_not_closed():
    """Scenario 2: the untouched seed compiles but fails the axiom check (`sorryAx`)."""
    result = check(BASELINE.read_text(), pristine=BASELINE.read_text(), package=PACKAGE, module=MODULE, theorem=THEOREM)
    assert result["integrity"] is True, result
    assert result["elaborates"] is True, result
    assert result["closed"] is False, result
    assert "sorryAx" in result["axioms"], result
    assert result["errors"] == [], result  # the `sorry` warning is dropped


def test_bogus_body_reports_the_error_not_the_axiom_report():
    """Scenario 4: the model-facing `errors` carries the unknown identifier, not the axiom/linter tail."""
    seed_text = BASELINE.read_text()
    candidate = "exact bogus_tactic_name".join(seed_text.rsplit("sorry", 1))
    result = check(candidate, pristine=seed_text, package=PACKAGE, module=MODULE, theorem=THEOREM)
    assert result["integrity"] is True, result
    assert result["elaborates"] is False, result
    assert result["errors"], result  # non-empty
    assert any("bogus_tactic_name" in e for e in result["errors"]), result
    for e in result["errors"]:
        assert not e.startswith("Note:"), result
        assert "warning" not in e.lower(), result
        assert "depends on axioms" not in e, result


def test_altered_prefix_fails_integrity():
    """Scenario 3: a candidate whose prefix differs from the seed fails integrity."""
    seed_text = BASELINE.read_text()
    altered = "theorem fake : True := by trivial\n" + seed_text
    result = check(altered, pristine=seed_text, package=PACKAGE, module=MODULE, theorem=THEOREM)
    assert result["integrity"] is False, result


def test_name_less_forgery_is_not_a_report():
    """Scenario 5: a report that does not name the theorem is not read — the real one reports sorryAx."""
    seed_text = BASELINE.read_text()
    spoof = seed_text + '\n#eval IO.println "depends on axioms: []"\n'
    result = check(spoof, pristine=seed_text, package=PACKAGE, module=MODULE, theorem=THEOREM)
    assert result["closed"] is False, result
    assert result["axiom_report"] == "ok", result
    assert "sorryAx" in (result["axioms"] or set()), result


def test_named_forgery_is_ignored_by_the_api():
    """Scenario 5: a named `#print` injection is ignored — the API reads the environment's sorryAx."""
    seed_text = BASELINE.read_text()
    spoof = seed_text + f'\n#eval IO.println "{THEOREM} depends on axioms: []"\n'
    result = check(spoof, pristine=seed_text, package=PACKAGE, module=MODULE, theorem=THEOREM)
    assert result["closed"] is False, result
    assert result["axiom_report"] == "ok", result
    assert "sorryAx" in (result["axioms"] or set()), result


def test_suppressed_report_is_missing():
    """Scenario 5: an unterminated comment swallows the appended probe — the report never appears."""
    seed_text = BASELINE.read_text()
    spoof = seed_text + "\n/- unterminated\n"
    result = check(spoof, pristine=seed_text, package=PACKAGE, module=MODULE, theorem=THEOREM)
    assert result["closed"] is False, result
    assert result["axiom_report"] == "missing", result
    assert result["axioms"] is None, result


def test_macro_interception_is_not_closed():
    """Scenario 5: a candidate installing `#print axioms` syntax must not fool the API checker."""
    seed_text = BASELINE.read_text()
    spoof = seed_text + (
        '\nsyntax (name := fakeAxiomPrint) "#print" "axioms" ident : command\n'
        'macro_rules (kind := fakeAxiomPrint)\n'
        '  | `(#print axioms $n:ident) => `(command| #eval IO.println "'
        + THEOREM + ' depends on axioms: []")\n'
    )
    result = check(spoof, pristine=seed_text, package=PACKAGE, module=MODULE, theorem=THEOREM)
    assert result["closed"] is False, result
    assert "sorryAx" in (result["axioms"] or set()), result


def test_file_mode_feedback_carries_the_first_lean_error(monkeypatch, tmp_path):
    """Scenario 6: after a failed round the next prompt carries the Lean error, not the axiom tail."""
    import harness.file_mode as fm

    seed_text = BASELINE.read_text()
    working = tmp_path / "working.lean"
    working.write_text(seed_text)

    prompts = []

    class ScriptedSession:
        def attempt(self, prompt):
            prompts.append(prompt)
            if len(prompts) == 1:
                working.write_text(seed_text.replace("sorry", "exact bogus_tactic_name"))
            return "done"

        def usage(self):
            return {}

    def fake_check(candidate, *, pristine, package, module, theorem, lean_path=None):
        return {
            "integrity": True,
            "elaborates": False,
            "axioms": None,
            "closed": False,
            "errors": ["error(lean.unknownIdentifier): Unknown identifier `bogus_tactic_name`"],
            "axiom_report": "ok",
            "raw_tail": ["depends on axioms: [...]"],
        }

    monkeypatch.setattr(fm.closure_oracle, "check", fake_check)
    monkeypatch.setattr(fm.closure_oracle, "sha256_text", lambda text: "sha")
    monkeypatch.setattr(fm.closure_oracle, "verdict", lambda result, seed_intact=True: bool(result.get("closed")))

    class StepClock:
        def __init__(self):
            self.t = 0.0

        def __call__(self):
            self.t += 0.5
            return self.t

    fm.run_file(
        ScriptedSession(),
        task="t", tier=2, repetition=1, mutant=False,
        working=working,
        run_dir=tmp_path,
        seed_path=BASELINE,
        package=PACKAGE,
        pristine=seed_text,
        cap_s=10.0, cap_usd=50.0,
        setup={},
        theorem=THEOREM,
        clock=StepClock(),
        watch_interval_s=0.01,
    )
    retries = [p for p in prompts if "The previous round did not close it" in p]
    assert retries, prompts
    assert "bogus_tactic_name" in retries[0], retries[0]
    assert "depends on axioms" not in retries[0], retries[0]
