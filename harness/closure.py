"""Route B: the AI closure loop (docs/protocol.md §8).

The loop alternates between a prover's goal state and a model's proposed tactic, under a wall-clock,
token and dollar budget. Two invariants hold whatever the model does:

* success is asserted from the prover reporting no unclosed goals, never from what the model said;
* running out of budget is reported as ``timeout`` with the binding budget named.
"""

from __future__ import annotations

import sys
import time
from pathlib import Path
from typing import Protocol, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from harness.result import COST_BASIS, compute_cost_usd  # noqa: E402


class Prover(Protocol):
    """The prover's observable surface: start it, read goals, apply a tactic, ask what is left."""

    def start(self) -> None: ...

    def goals(self) -> Sequence[str]: ...

    def apply(self, tactic: str) -> None: ...

    def unclosed(self) -> int: ...


class Model(Protocol):
    """A model that proposes one tactic for the current goals and reports cumulative usage."""

    def propose(self, goals: Sequence[str], history: Sequence[tuple[str, Sequence[str]]]) -> str: ...

    def usage(self) -> dict: ...


def run_loop(
    prover: Prover,
    model: Model,
    *,
    task: str = "",
    cap_s: float = 7200.0,
    cap_usd: float = 50.0,
    cap_tokens: int | None = None,
    clock=time.monotonic,
) -> dict:
    """Run the closure loop until the proof closes or a budget binds."""
    started = clock()
    prover.start()
    history: list[tuple[str, Sequence[str]]] = []
    turns = 0
    budget_exceeded: str | None = None
    outcome = "error"

    while True:
        unclosed = prover.unclosed()
        if unclosed == 0:
            outcome = "success"
            break

        usage = model.usage()
        if clock() - started > cap_s:
            budget_exceeded = "wall_clock"
            break
        if usage.get("cost_usd", 0.0) > cap_usd:
            budget_exceeded = "usd"
            break
        if cap_tokens is not None and usage.get("input", 0) + usage.get("output", 0) > cap_tokens:
            budget_exceeded = "tokens"
            break

        tactic = model.propose(prover.goals(), history)
        prover.apply(tactic)
        history.append((tactic, prover.goals()))
        turns += 1

    wall_clock_s = round(clock() - started, 3)
    usage = model.usage()
    if budget_exceeded is not None:
        outcome = "timeout"

    return {
        "task": task,
        "route": "proof",
        "outcome": outcome,
        "budget_exceeded": budget_exceeded,
        "wall_clock_s": wall_clock_s,
        "tier": 2,
        "cost_usd": usage.get("cost_usd", 0.0),
        "cost_basis": COST_BASIS,
        "proof": {
            "turns": turns,
            "unclosed_goals": prover.unclosed(),
            "input_tokens": usage.get("input", 0),
            "output_tokens": usage.get("output", 0),
            "model": usage.get("model"),
            "tactics": [tactic for tactic, _ in history],
        },
        "artifacts": {},
    }
