# Contract: the AI closure loop

Subject: `harness/closure.py` — driving a prover towards a closed proof between a model and the
prover's goal state, and emitting a result row. Owner: planner. Implemented by: coder.

The loop is the measuring instrument for Route B. Two things must hold whatever the model does: it
never reports a proof as closed while an unclosed goal remains, and a run that ran out of budget says
so instead of guessing. The prover is reached through a port so the loop can be exercised without a
Lean installation and without any model call.

## Scenario 1 — success is asserted from the artifact, not from the transcript

- **Actor**: the researcher running the closure harness.
- **Boundary**: `harness.closure.run_loop`, called with a stub prover and a scripted model.
- **Given**: a stub prover that reports one outstanding goal, and a scripted model whose next tactic
  never closes it, with a wall-clock budget already exhausted (a clock stub that advances past the cap).
- **When**: the loop runs.
- **Then**: the row's `outcome` is `"timeout"`, `proof.unclosed_goals` is 1, and no `"success"` outcome
  is produced; `proof.turns` equals the number of tactics the model proposed.
- **Why**: the failure mode this guards is a loop that reports success because the model *said* it was
  done. Success may only come from the prover reporting no unclosed goals.

## Scenario 2 — a closed proof yields a success row with counted tokens and dollars

- **Actor**: the researcher.
- **Boundary**: the same entry point.
- **Given**: a stub prover whose first `apply` leaves one goal and whose second leaves none, and a
  scripted model returning two tactics with scripted usage `{"input": 1000, "output": 200}` and a cost
  function of the caller's choosing.
- **When**: the loop runs.
- **Then**: `outcome` is `"success"`, `proof.turns` is 2, `proof.unclosed_goals` is 0,
  `proof.input_tokens` is 2000 and `proof.output_tokens` is 400 (summed over turns), and `cost_usd` is
  the summed scripted cost — never a value the loop invented.
- **Why**: the dollar figure is half the experiment's dependent variable; it must be a sum of recorded
  usage, not an estimate.

## Scenario 3 — a model that repeats itself is stopped by the budget, not by hope

- **Actor**: the researcher.
- **Boundary**: the same entry point, with a token budget.
- **Given**: a stub prover that never closes, and a scripted model that returns the same tactic every
  time with scripted usage, under a token cap of 1500 tokens.
- **When**: the loop runs.
- **Then**: the loop stops at or before the cap, the row records `budget_exceeded: "tokens"`, and
  `proof.turns` is finite.
- **Why**: budgets are the only thing standing between a stuck loop and unbounded spend (§11 decision 3).

## Expected failure before implementation

Unresolved import (`harness.closure` does not exist) for all three scenarios.
