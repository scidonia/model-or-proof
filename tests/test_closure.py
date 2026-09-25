"""Behavior scenarios for the AI closure loop (tests/closure-contract.md)."""

import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO))

from harness.closure import run_loop  # noqa: E402


class StubProver:
    """A prover port whose goal state is scripted: after each applied tactic the next scripted
    entry says whether a goal remains (True) or the proof is closed (False)."""

    def __init__(self, remaining):
        self.queue = list(remaining)
        self.applied = []
        self.current = True

    def start(self):
        pass

    def goals(self):
        return ["⊢ Mutex"] if self.current else []

    def apply(self, tactic):
        self.applied.append(tactic)
        self.current = self.queue.pop(0) if self.queue else True

    def unclosed(self):
        return 1 if self.current else 0


class ScriptedModel:
    """A model port with fixed tactics and fixed per-turn usage."""

    def __init__(self, tactics, usage):
        self.tactics = list(tactics)
        self.per_turn = dict(usage)
        self.turns = 0
        self._total = {"input": 0, "output": 0, "cost_usd": 0.0}

    def propose(self, goals, history):
        tactic = self.tactics[min(self.turns, len(self.tactics) - 1)]
        self.turns += 1
        for key in self._total:
            self._total[key] += self.per_turn.get(key, 0.0)
        return tactic

    def usage(self):
        return dict(self._total)


class AdvancingClock:
    """A monotonic clock that jumps by a fixed step on every reading."""

    def __init__(self, step):
        self.step = step
        self.t = 0.0

    def __call__(self):
        self.t += self.step
        return self.t


def test_success_only_from_the_prover_not_the_model(tmp_path):
    """Scenario 1: success is asserted from the artifact, not from the transcript."""
    prover = StubProver([True])  # one goal, and it never closes
    model = ScriptedModel(["simp"], {"input": 100, "output": 10, "cost_usd": 0.001})

    row = run_loop(prover, model, cap_s=60, clock=AdvancingClock(step=3600))

    assert row["outcome"] == "timeout"
    assert row["proof"]["unclosed_goals"] == 1
    assert row["proof"]["turns"] == len(prover.applied)


def test_closed_proof_counts_tokens_and_dollars(tmp_path):
    """Scenario 2: a closed proof yields a success row with counted tokens and dollars."""
    prover = StubProver([True, False])
    model = ScriptedModel(
        ["simp", "omega"], {"input": 1000, "output": 200, "cost_usd": 0.25}
    )

    row = run_loop(prover, model, cap_s=7200, clock=AdvancingClock(step=1))

    assert row["outcome"] == "success"
    assert row["proof"]["turns"] == 2
    assert row["proof"]["unclosed_goals"] == 0
    assert row["proof"]["input_tokens"] == 2000
    assert row["proof"]["output_tokens"] == 400
    assert row["cost_usd"] == 0.5
    assert prover.applied == ["simp", "omega"]


def test_token_budget_stops_a_stuck_loop():
    """Scenario 3: a model that repeats itself is stopped by the budget."""
    prover = StubProver([])  # one goal, never closes
    model = ScriptedModel(["simp"], {"input": 1000, "output": 200, "cost_usd": 0.01})

    row = run_loop(prover, model, cap_s=7200, cap_tokens=1500, clock=AdvancingClock(step=1))

    assert row["outcome"] == "timeout"
    assert row["budget_exceeded"] == "tokens"
    assert row["proof"]["turns"] == 2  # stops once the second turn's usage crosses the cap
    assert row["proof"]["input_tokens"] + row["proof"]["output_tokens"] > 1500
