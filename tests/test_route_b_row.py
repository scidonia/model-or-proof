"""Behavior scenarios for the extended Route B row (tests/route-b-row-contract.md)."""

import hashlib
import json
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO))

from harness import file_mode, model  # noqa: E402
from harness import route_b  # noqa: E402
from harness.closure import AUTOMATION_TACTICS, ProviderError, ProverError, detect_assisted, run_loop  # noqa: E402


class ManualClock:
    """A clock the prover can advance by a controlled amount (no auto-advance)."""

    def __init__(self):
        self.t = 0.0

    def __call__(self):
        return self.t

    def advance(self, dt):
        self.t += dt


class StepClock:
    """A clock that advances one second per reading."""

    def __init__(self):
        self.t = 0.0

    def __call__(self):
        self.t += 1.0
        return self.t


class NoopModel:
    def propose(self, goals, history):
        return "trivial"

    def usage(self):
        return {"input": 0, "output": 0, "cost_usd": 0.0}


# --- Scenario 1: startup_s is pinned against an independently controlled ready time ---


class SlowStartProver:
    """A prover whose start() advances the clock by a controlled ready duration."""

    def __init__(self, clock, ready_s):
        self._clock = clock
        self._ready = ready_s

    def start(self):
        self._clock.advance(self._ready)

    def goals(self):
        return []

    def apply(self, tactic):
        pass

    def unclosed(self):
        return 0


def test_startup_is_the_controlled_ready_duration():
    """Scenario 1: startup_s equals the prover's controlled ready time, not a definitional split."""
    clock = ManualClock()
    row = run_loop(SlowStartProver(clock, 3.0), NoopModel(), clock=clock)
    assert row["outcome"] == "success", row
    assert row["startup_s"] == 3.0, row  # the prover's ready time, independently known
    assert row["proof_s"] == row["wall_clock_s"] - 3.0, row


# --- Scenario 2: assisted is detected by a full-body declaration diff ---

SEED_SORRY = "theorem mutex : ∀ n : ℕ, True := by\n  sorry\n"
ARTIFACT_SCRIPT = "theorem mutex : ∀ n : ℕ, True := by\n  trivial\n"


def test_faithful_sorry_replacement_is_not_assisted():
    assert detect_assisted(SEED_SORRY, ARTIFACT_SCRIPT)["assisted"] is False


def test_meaning_rewrite_is_assisted():
    """A changed def value (not an extra declaration) is a rewrite, hence assisted."""
    assert detect_assisted("def Mutex : Prop := False", "def Mutex : Prop := True")["assisted"] is True


def test_extra_declarations_are_assisted_across_spellings():
    """Modifiers, attributes, and the wider keyword set are all caught as extra declarations."""
    extras = (
        "lemma inv : ∀ n : ℕ, True := by\n  trivial\n",
        "private lemma inv : ∀ n : ℕ, True := by\n  trivial\n",
        "@[simp] lemma inv : ∀ n : ℕ, True := by\n  trivial\n",
        "opaque aux : Prop",
        "inductive Foo",
    )
    for extra in extras:
        assert detect_assisted(SEED_SORRY, SEED_SORRY + "\n" + extra)["assisted"] is True, extra


def test_indented_and_any_kind_declarations_are_assisted():
    """Indentation is styling, not a boundary; every declaration kind is caught, not just theorem/lemma."""
    assert detect_assisted(SEED_SORRY, SEED_SORRY + "\n  lemma helper : True := by trivial\n")["assisted"] is True
    for extra in (
        "def Inv (s : Prop) : Prop := True",
        "notation a ~ b => True",
        "abbrev N := 23",
        "instance : Fintype Nat := inferInstance",
    ):
        assert detect_assisted(SEED_SORRY, SEED_SORRY + "\n" + extra)["assisted"] is True, extra


# --- Scenario 3: the fallback flag is OR'd, never overwritten ---


class TwoTacticProver:
    """Closes after two applied tactics."""

    def __init__(self):
        self.n = 0

    def start(self):
        pass

    def goals(self):
        return [] if self.n >= 2 else ["⊢ Mutex"]

    def apply(self, tactic):
        if tactic in AUTOMATION_TACTICS:
            return
        self.n += 1

    def unclosed(self):
        return 0 if self.n >= 2 else 1


class FirstTurnFallback(NoopModel):
    """Reports a fallback resolution on the first turn, primary afterwards."""

    def __init__(self):
        self._calls = 0

    def usage(self):
        self._calls += 1
        fb = self._calls == 1
        return {
            "input": 0,
            "output": 0,
            "cost_usd": 0.0,
            "resolved_model": "fallback" if fb else "primary",
            "is_fallback": fb,
        }


def test_fallback_flag_is_or_d_across_turns():
    """Scenario 3: one fallback turn flags the run even if later turns are primary."""
    row = run_loop(TwoTacticProver(), FirstTurnFallback(), clock=StepClock())
    assert row["outcome"] == "success", row
    assert row["resolvedModelIsFallback"] is True, row  # OR'd, not overwritten by the primary turn


# --- Scenario 4: empty-content is consumed and re-asked; the counter resets on a real tactic ---


class OneTacticProver:
    """Closed only after one non-empty tactic is applied."""

    def __init__(self):
        self.closed = False

    def start(self):
        pass

    def goals(self):
        return [] if self.closed else ["⊢ Mutex"]

    def apply(self, tactic):
        if tactic in AUTOMATION_TACTICS:
            return
        if tactic:
            self.closed = True

    def unclosed(self):
        return 0 if self.closed else 1


class NeverClosesProver:
    """Never closes, so the loop keeps proposing."""

    def start(self):
        pass

    def goals(self):
        return ["⊢ Mutex"]

    def apply(self, tactic):
        pass

    def unclosed(self):
        return 1


class PatternModel(NoopModel):
    """Replays a fixed tactic pattern, cycling."""

    def __init__(self, pattern):
        self._pattern = list(pattern)
        self._i = 0

    def propose(self, goals, history):
        tactic = self._pattern[self._i % len(self._pattern)]
        self._i += 1
        return tactic


def test_empty_content_is_consumed_and_reasked():
    ok = run_loop(OneTacticProver(), PatternModel(["", "", "simp"]), clock=StepClock())
    assert ok["outcome"] == "success", ok
    assert ok["proof"]["turns"] == 3, ok  # two empty turns + one real tactic


def test_always_empty_times_out_on_budget_not_an_abort():
    """Empty content is re-asked until the budget binds — the budget, not a 3-empty abort, terminates.

    The cap is deliberately large so the wall-clock binds only after many turns: under a
    consecutive-empty abort this row would be ``error`` (the abort fires at ~3 turns), so ``timeout``
    here is what pins "no abort". """
    row = run_loop(OneTacticProver(), PatternModel([""]), cap_s=100, clock=StepClock())
    assert row["outcome"] == "timeout", row
    assert row["budget_exceeded"] == "wall_clock", row
    assert row["proof"]["turns"] >= 1, row  # empty turns are consumed, then the budget binds


# --- Scenario 5: a mid-run provider failure lands an error row ---


class FailingModel(NoopModel):
    """Returns a real tactic fail_after_turns times, then raises ProviderError."""

    def __init__(self, fail_after_turns, status, message):
        self._left = fail_after_turns
        self._status = status
        self._message = message

    def propose(self, goals, history):
        if self._left > 0:
            self._left -= 1
            return "simp"
        raise ProviderError(self._status, self._message)


class DeadlineModel(NoopModel):
    """A model that raises the per-turn deadline failure on its first propose."""

    def propose(self, goals, history):
        raise ProviderError(0, "the turn did not finish within 360.0s", deadline=360.0)


def test_turn_deadline_is_distinguished_from_provider_failure():
    """Scenario 20: a per-turn deadline cut is a budget event, not a rig fault."""
    row = run_loop(NeverClosesProver(), DeadlineModel(), clock=StepClock())
    assert row["outcome"] == "error", row
    assert row["error"]["kind"] == "turn_deadline", row
    assert row["error"]["kind"] != "provider_failure", row


def test_provider_failure_lands_an_error_row():
    """Scenario 5: a mid-run provider failure lands an error row naming the failure."""
    row = run_loop(
        NeverClosesProver(), FailingModel(2, 402, "credit_balance_exhausted"), clock=StepClock()
    )
    assert row["outcome"] == "error", row
    assert row["error"] == {
        "kind": "provider_failure",
        "status": 402,
        "message": "credit_balance_exhausted",
    }, row
    assert row["proof"]["turns"] == 2, row  # the two consumed turns, not the failed call


# --- Scenario 6: a prover-side failure lands an error row ---


class RaisingProver:
    """Raises ProverError from start() or apply()."""

    def __init__(self, raise_on_start=False, message="step timed out"):
        self._raise_start = raise_on_start
        self._message = message

    def start(self):
        if self._raise_start:
            raise ProverError(self._message)

    def goals(self):
        return ["⊢ Mutex"]

    def apply(self, tactic):
        if tactic in AUTOMATION_TACTICS:
            return
        raise ProverError(self._message)

    def unclosed(self):
        return 1


def test_prover_failure_lands_an_error_row():
    """Scenario 6: a prover-side failure (start or apply) lands an error row, not a lost run."""
    from_start = run_loop(
        RaisingProver(raise_on_start=True, message="seed failed to load"),
        PatternModel(["simp"]),
        clock=StepClock(),
    )
    assert from_start["outcome"] == "error", from_start
    assert from_start["error"] == {"kind": "prover_failure", "message": "seed failed to load"}, from_start
    assert from_start["proof"]["turns"] == 0, from_start  # failed before any tactic

    from_apply = run_loop(RaisingProver(message="step timed out"), PatternModel(["simp"]), clock=StepClock())
    assert from_apply["outcome"] == "error", from_apply
    assert from_apply["error"] == {"kind": "prover_failure", "message": "step timed out"}, from_apply
    assert from_apply["proof"]["turns"] == 1, from_apply  # one tactic proposed, then the step failed


# --- Scenario 7: a mutant that closes is a rig-broken error ---


def test_mutant_that_closes_is_an_error_row():
    """Scenario 7: a mutant run that closes is recorded as a rig-broken error, never success."""
    row = run_loop(OneTacticProver(), PatternModel(["simp"]), mutant=True, clock=StepClock())
    assert row["outcome"] == "error", row
    assert row["error"]["kind"] == "mutant_closed", row
    assert row["mutant"] == "closed", row


# --- Scenario 8: an unreadable artifact is an error, with assisted unknown ---


def test_unreadable_artifact_is_an_error_row():
    """Scenario 8: a post-run artifact read failure lands an error row with assisted unknown."""
    row = run_loop(
        OneTacticProver(),
        PatternModel(["simp"]),
        seed_text="theorem mutex : ∀ n : ℕ, True := by\n  sorry\n",
        artifact_path="/nonexistent/artifact.lean",
        clock=StepClock(),
    )
    assert row["outcome"] == "error", row
    assert row["error"]["kind"] == "artifact_unreadable", row
    assert row["assisted"] is None, row  # no evidence must not read as unassisted


# --- Scenarios 9-11: the refutation arm, exercised without a real prover or model ---


class RefutingProver:
    """A prover whose cmd() machine-checks a refutation: it accepts one command as a witness."""

    def __init__(self, accept_command):
        self._accept = accept_command
        self._closed = False

    def start(self):
        pass

    def goals(self):
        return [] if self._closed else ["⊢ Mutex"]

    def apply(self, tactic):
        pass  # the proof arm never closes this stub

    def cmd(self, command):
        if command == self._accept:
            return {"refuted": True, "witness": "pc = (0 :> \"crit\" @@ 1 :> \"crit\")"}
        return {"refuted": False}

    def unclosed(self):
        return 0 if self._closed else 1


class RefutationModel(NoopModel):
    """Proof arm proposes a no-op tactic; refutation arm proposes a fixed command."""

    def __init__(self, command):
        self._command = command

    def refute(self, goals, history):
        return self._command


def test_machine_checked_refutation_is_accepted_on_the_mutant():
    """Scenario 9: a refutation the prover machine-checks is `refuted`, not a model claim."""
    row = run_loop(
        RefutingProver("#eval witness"),
        RefutationModel("#eval witness"),
        arms="proof+refutation",
        mutant=True,
        clock=StepClock(),
    )
    assert row["outcome"] == "refuted", row


def test_rejected_refutation_does_not_count():
    """Scenario 10: a refutation the prover rejects is not accepted — the race runs to the budget."""
    row = run_loop(
        RefutingProver("#eval witness"),
        RefutationModel("#eval rejected"),
        arms="proof+refutation",
        mutant=True,
        cap_s=3,
        clock=StepClock(),
    )
    assert row["outcome"] == "timeout", row
    assert row["budget_exceeded"] == "wall_clock", row


def test_refutation_against_a_statement_tlc_says_holds_is_a_rig_defect():
    """Scenario 11: a witness on the positive statement is a rig defect, not a result."""
    row = run_loop(
        RefutingProver("#eval witness"),
        RefutationModel("#eval witness"),
        arms="proof+refutation",
        mutant=False,
        clock=StepClock(),
    )
    assert row["outcome"] == "error", row
    assert row["error"]["kind"] == "rig_refutation", row


# --- Scenario 16: the refutation arm must not win by proving the statement; hopelessness is recorded ---


class HopelessRefutationModel(NoopModel):
    """Proof arm closes; refutation arm declares it cannot find a counterexample."""

    def propose(self, goals, history):
        return "simp"

    def refute(self, goals, history):
        return "no_witness"


class RejectAllProver:
    """A prover whose cmd() rejects every refutation (the negation-wrap never closes)."""

    def start(self):
        pass

    def goals(self):
        return ["⊢ Mutex"]

    def apply(self, tactic):
        pass

    def cmd(self, command):
        return {"refuted": False, "messages": ["the negation does not close"]}

    def unclosed(self):
        return 1


class ProofOfStatementModel(NoopModel):
    """Proof arm closes; refutation arm proposes a proof of the statement, not a refutation."""

    def propose(self, goals, history):
        return "simp"

    def refute(self, goals, history):
        return "induction n with | zero => simp | succ n => simp"


def test_hopelessness_terminates_the_arm_and_is_recorded():
    row = run_loop(TwoTacticProver(), HopelessRefutationModel(), arms="proof+refutation", clock=StepClock())
    assert row["outcome"] == "success", row
    assert row["refutation"] == "no_witness", row


def test_proof_of_the_statement_is_not_a_refutation():
    """A proposal that proves P is wrapped in ¬P and rejected — the arm cannot win by proving P."""
    row = run_loop(TwoTacticProver(), ProofOfStatementModel(), arms="proof+refutation", clock=StepClock())
    assert row["outcome"] != "refuted", row


# --- Scenario 17: the OMP session directory is absolute, under the run's session root ---


def test_session_dir_is_absolute_under_the_session_root():
    """The --session-dir we hand OMP is absolute (OMP resolves a relative one against --cwd)."""
    from harness.model import omp_command

    cmd = omp_command(session_root="results/omp/run1", role="proof")
    assert "--session-dir" in cmd, cmd
    value = cmd[cmd.index("--session-dir") + 1]
    assert Path(value).is_absolute(), value
    assert value == str((REPO / "results" / "omp" / "run1" / "proof").resolve()), value


# --- Scenario 18: the reply is applied whole; a bare `by` is wrapped as `exact by` ---


def test_whole_reply_kept_and_bare_by_wrapped_as_exact():
    from harness.model import extract_tactic

    # A fenced proof with prose around it: fence and prose stripped, the multi-line block kept whole,
    # and the bare `by` wrapped as `exact by` (a bare `by` is not a standalone tactic).
    reply = "Here is the proof:\n```lean\nby\n  omega\n```\nThat closes it."
    assert extract_tactic(reply) == "exact by\n  omega"


def test_single_tactic_and_exact_by_pass_through_unchanged():
    from harness.model import extract_tactic

    assert extract_tactic("induction hs") == "induction hs"
    assert extract_tactic("exact by\n  omega") == "exact by\n  omega"


# --- Scenario 19: the refutation command is not rewritten by the proof-arm wrap ---


def test_refutation_command_is_not_rewritten():
    from harness.model import extract_command, extract_tactic

    reply = "by\n  decide"
    assert extract_command(reply) == "by\n  decide"  # the refutation arm stays byte-exact (D16)
    assert extract_tactic(reply) == "exact by\n  decide"  # only the proof arm normalises


def test_refutation_command_passes_no_witness_and_example_unchanged():
    from harness.model import extract_command

    assert extract_command("no_witness") == "no_witness"
    example = "example : ¬ (n + 0 ≠ n) := by decide"
    assert extract_command(example) == example


# --- Scenario 12: the planning turn (recorded verbatim; empty plan is consumed + re-asked) ---


class PlanningModel(NoopModel):
    """A model with a plan() turn returning the given per-arm plan, recording every arm it is asked."""

    def __init__(self, plans):
        self._plans = dict(plans)
        self._asked = []

    def plan(self, arm, goals, history):
        self._asked.append(arm)
        return self._plans.get(arm, "")


def test_planning_turn_is_recorded_verbatim():
    model = PlanningModel({"proof": "induct then finish"})
    row = run_loop(OneTacticProver(), model, arms="proof+refutation", clock=StepClock())
    assert row["plan"]["proof"] == "induct then finish", row
    assert row["plan"]["refutation"] is None, row
    assert row["plan"]["refutation_reason"], row
    assert "refutation" not in model._asked, model._asked  # no refutation plan turn


class RetryPlanModel(PlanningModel):
    """Returns an empty plan once, then the real plan — the empty plan must be re-asked."""

    def plan(self, arm, goals, history):
        self._asked.append(arm)
        if self._asked.count(arm) == 1:
            return ""  # empty plan: consumed turn, re-asked with the nudge
        return self._plans.get(arm, "")


def test_empty_plan_is_consumed_and_reasked():
    model = RetryPlanModel({"proof": "induct"})
    row = run_loop(OneTacticProver(), model, arms="proof+refutation", clock=StepClock())
    assert row["plan"]["proof"] == "induct", row
    assert row["plan"]["refutation"] is None, row


# --- Scenario 13: the automation pass is tried first and recorded when it closes ---


class AutoClosingProver:
    """A prover whose apply() closes the goal only for the automation tactic 'aesop'."""

    def __init__(self):
        self._closed = False

    def start(self):
        pass

    def goals(self):
        return [] if self._closed else ["⊢ Mutex"]

    def apply(self, tactic):
        if tactic == "aesop":
            self._closed = True

    def unclosed(self):
        return 0 if self._closed else 1


def test_automation_pass_is_recorded_when_it_closes():
    row = run_loop(AutoClosingProver(), NoopModel(), arms="proof", clock=StepClock())
    assert row["outcome"] == "success", row
    assert row["proof"]["automation_closed"] == "aesop", row  # §5's vacuousness guard reads this


# --- Scenario 14: the few-shot examples carry no forbidden hint (a data check) ---

FORBIDDEN_HINTS = ["holds the token", "critical node", "TokenRing", "Reachable", "ringSucc", "nodeZero"]


def _few_shot_text():
    p = REPO / "proofs" / "lean" / "token-ring" / "prompt_examples.lean"
    return p.read_text()  # FileNotFoundError before the examples are committed (the expected red run)


def test_few_shot_examples_carry_no_forbidden_hint():
    text = _few_shot_text()
    for hint in FORBIDDEN_HINTS:
        assert hint not in text, f"forbidden hint {hint!r} in the few-shot examples"


# --- Scenario 15: invited-guess labelling (model-guessed vs human-supplied) ---

SEED_GOAL = "theorem mutex : ∀ n : ℕ, True := by\n  sorry\n"


def test_model_guessed_helper_is_not_assisted():
    """A helper the loop added (provenance model) is the loop's own work: assisted False."""
    diff = detect_assisted(SEED_GOAL, SEED_GOAL + "\nlemma inv : True := by trivial\n", human=False)
    assert diff["assisted"] is False, diff
    assert diff["auxiliary_invariants"] == ["inv"], diff


def test_human_supplied_helper_is_assisted():
    """A helper in the seed beyond the goal (provenance human) marks the run assisted."""
    diff = detect_assisted("theorem mutex : ∀ n : ℕ, True := by\n  sorry\n",
                           "theorem mutex : ∀ n : ℕ, True := by\n  sorry\n\nlemma inv : True := by trivial\n",
                           human=True)
    assert diff["assisted"] is True, diff
    assert diff["auxiliary_invariants"] == ["inv"], diff


# --- file-mode rows: the seed as loaded, and the configuration that produced the row -----------------

SEED = "import Mathlib\nnamespace Paxos\ntheorem agreement : True := by\n  sorry\nend Paxos\n"
EDITED = SEED.replace("\nnamespace Paxos\n", "\n-- edited before the run\nnamespace Paxos\n")


def file_mode_package(tmp_path):
    """The minimal package a file-mode row needs: seed, baseline, config, manifest, working copy.

    Measured cost of one stub-driven row: about 0.08 s, because `run_file`'s whole session surface is
    `usage()` and `attempt()` — no model, no network, no elaboration.
    """
    package = tmp_path / "paxos"
    (package / "baseline").mkdir(parents=True)
    (package / "Paxos.lean").write_text(SEED)
    (package / "baseline" / "Paxos.lean").write_text(SEED)
    (package / "seeds.json").write_text(json.dumps({"Paxos.lean": hashlib.sha256(SEED.encode()).hexdigest()}))
    (package / "lakefile.toml").write_text('name = "paxos"\n')
    (package / "lean-toolchain").write_text("leanprover/lean4:v4.35.0-rc3\n")
    (package / "lake-manifest.json").write_text(json.dumps({"packages": []}))
    working = package / ".runs" / "Paxos-r1.lean"
    working.parent.mkdir()
    working.write_text(SEED)
    return package, working


class RepairingSession:
    """A file-mode session that restores the committed seed mid-run, as the row-58 model did."""

    def __init__(self, seed_path, pristine):
        self.seed_path = seed_path
        self.pristine = pristine
        self.seen = False

    def usage(self):
        if not self.seen:
            self.seed_path.write_text(self.pristine)
            self.seen = True
        return {"cost_usd": 0.0}

    def attempt(self, prompt):
        raise AssertionError("no round should run at cap_s=0")


def test_file_mode_row_records_the_seed_as_loaded_not_only_as_left(tmp_path):
    """Scenario 21: a run that began off-pristine and was repaired must be able to say both."""
    package, working = file_mode_package(tmp_path)
    seed_path = package / "Paxos.lean"
    seed_path.write_text(EDITED)

    row = file_mode.run_file(
        RepairingSession(seed_path, SEED),
        task="paxos", tier=2, repetition=1, mutant=False,
        working=working, run_dir=tmp_path / "session", seed_path=seed_path, package=package,
        pristine=SEED, cap_s=0.0, cap_usd=50.0, setup={"mode": "file"}, statement="",
    )

    assert row["artifacts"]["baseline"]["matches"] is False, "the run did not start from pristine text"
    assert row["closure"]["seed_intact"] is True, "and it left pristine text behind"


class StubFileSession:
    """A file-mode session with no transport: `attempt` is never reached at cap_s=0."""

    def __init__(self, **_kwargs):
        pass

    def usage(self):
        return {"cost_usd": 0.0}

    def attempt(self, prompt):
        raise AssertionError("no round should run at cap_s=0")

    def close(self):
        pass


@pytest.mark.parametrize(("arms", "marking"), [("proof+refutation", False), ("proof", True)])
def test_file_mode_row_carries_its_configuration_and_revision(tmp_path, monkeypatch, arms, marking):
    """Scenario 22: the row must say which configuration produced it, and the revision must be real."""
    package, _ = file_mode_package(tmp_path)
    seed_path = package / "Paxos.lean"
    baseline = route_b.load_baseline(seed_path)
    results = tmp_path / "results"
    results.mkdir()

    monkeypatch.setattr(model, "OmpFileModel", StubFileSession)
    args = SimpleNamespace(reps=1, mutant=False, tier=2, arms=arms, exploratory=False)
    route_b.run_file_mode(
        args, task="paxos", results_dir=results, seed=seed_path, baseline=baseline,
        cap_s=0.0, cap_usd=50.0,
    )

    row = next(json.loads(line) for line in (results / "proof.jsonl").read_text().splitlines() if line.strip())
    assert row["arms"] == arms
    assert row["exploratory"] is marking
    assert row["setup"]["harness_revision"]["digest"] == route_b.harness_revision(seed_path, baseline)["digest"]
