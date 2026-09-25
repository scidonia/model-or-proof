# model-or-proof

Experiment repository: is it feasible to replace TLA+ model checking with theorem-prover verification,
and what are the wall-clock and cost differentials. Read `docs/protocol.md` before changing anything —
it is the contract of the experiment.

## Test policy

- Tests use `pytest`, live in `tests/`, and run as `nix develop -c pytest`. No new test dependency is
  added without saying so in the plan.
- Behavior contracts are the planner's: scenario text lives in `tests/*-contract.md` and the executable
  scenario in the matching `tests/test_*.py`. The coder never edits a scenario file; a scenario that
  looks wrong goes back to the planner.
- A scenario never reaches the network or a model. The closure loop is exercised against a stub prover
  and a scripted model; whether a real model picks good tactics is an eval, not a scenario.
- TLC is a local tool and may be invoked by a scenario (specs at `N=3` run in about a second).
- Every new or changed scenario is observed failing before the code that satisfies it; the failure is
  reported, not asserted from memory.

## Layout

| Path | Purpose |
| --- | --- |
| `docs/protocol.md` | The experiment protocol: hypotheses, metrics, controls, statistics, decisions |
| `plans/` | Plan of attack, phase by phase |
| `specs/tla/<task>/` | TLA+ modules, `.cfg` per instance, and each task's mutant |
| `proofs/lean/<task>/` | Lean 4 models and theorems for Route B |
| `harness/` | Both runners: TLC invocation and parsing, the AI closure loop, result rows |
| `tasks/` | Task manifests: property, `N₀`, budgets, mutants, artifacts |
| `tests/` | Behavior contracts and their executable scenarios |
| `results/` | `*.jsonl` result rows and run logs |
| `wiki/` | Narrative documentation, updated as the work lands |
