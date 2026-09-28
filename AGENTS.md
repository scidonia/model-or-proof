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
- TLC is local but a scenario may invoke it only after its **exact task/config** was timed and found
  fast enough for the full suite (token-ring at `N=3`: measured 0.656–0.669 s in
  `wiki/comparison-matrix.md` §3). An untimed instance is ineligible for pytest; `N=3` alone says
  nothing about Paxos's runtime.
- Every new or changed scenario is observed failing before the code that satisfies it; the failure is
  reported, not asserted from memory.
- A command whose **exit status carries meaning** is read with its output captured or left unmodified.
  A pipeline's status belongs to its last stage, and `| head`/`| tail` can also turn the writer's own
  zero into a nonzero through a broken pipe — so `… | tail -3` shows what ran, never whether it passed.
  This applies wherever a status is evidence: a test run, a gate such as `scripts/audit_attempts.py`
  whose `0`/`1`/`2` mean different things, or a measurement whose outcome is decided by the runner's
  own code.
- Resource-heavy TLC calibration, diagnostic reachability witnesses, and live AI cells are explicit
  measured acceptance runs, not full-suite fixtures. Keep pytest fast and deterministic with
  structural contract checks; preserve the real result rows, trace logs, and provenance separately.

## Commits

- A commit message **body** goes through `git commit -F <file>`, never `git commit -m`, whenever it
  contains backticks, `$`, or anything else the shell expands. With `-m` the shell substitutes first, so
  the recorded message silently loses the segment and `git log` reads plausibly while the reasoning is
  gone — a message that was never written cannot be recovered from a message that looks fine. `-F` also
  keeps a long body legible, which the entries here are.

## Layout

| Path | Purpose |
| --- | --- |
| `docs/protocol.md` | The experiment protocol: hypotheses, metrics, controls, statistics, decisions |
| `plans/` | Plan of attack, phase by phase |
| `specs/tla/<task>/` | TLA+ modules, `.cfg` per instance, and each task's mutant |
| `proofs/lean/<task>/` | Lean 4 models and theorems for Route B |
| `harness/` | Both runners: TLC invocation and parsing, the AI closure loop, result rows |
| `scripts/` | Standalone analysis/verification scripts that produce no result row (e.g. the token-ring state-graph enumerator behind the equivalence audit's §6) |
| `tasks/` | Task manifests: property, `N₀`, budgets, mutants, artifacts |
| `tests/` | Behavior contracts and their executable scenarios |
| `results/` | `*.jsonl` result rows and run logs |
| `wiki/` | Narrative documentation, updated as the work lands |
