# Plan: model-or-proof — bootstrap, then the comparison

Goal: settle, with measured numbers, whether proof (closed by an AI loop) can replace model checking
for concurrent-system verification, and at what wall-clock and dollar differential.

Non-goals: proving anything about real deployed systems; claiming a general superiority of either
route outside the task set; human-interactive proof engineering effort.

The method is fixed in `docs/protocol.md`. This plan is the order of work, its acceptance checks, and
what is blocked.

## Where the work stands (evidence, 2026-09-25)

- Dev shell builds from cache: `tlaplus-1.7.4` (TLC 2.19, OpenJDK 8), `python3`, `jq`, `z3`.
- `specs/tla/token-ring/TokenRing.tla` + `.cfg`: TLC proves `Mutex` — 36 distinct states at `N=3`,
  depth 11.
- `TokenRingMutant.tla` (drops the token guard): TLC reports the violation with a trace — the
  negative control for the whole rig.
- Cost curve measured at `N = 3…17` (README table): distinct states ≈`2.2^N`, wall-clock doubling
  roughly every +2 nodes; `N=17` takes 33.4 s. JVM start ≈0.6 s of every run.
- Prover landscape checked: nixpkgs has `elan-4.2.4`, `coq-9.1.1`, `isabelle-2025-2`, `dafny-4.11.0`,
  `fstar`, `z3`, `cvc5`. AI-closure interfaces for Lean 4: `lean-repl` (JSON goal/tactic protocol),
  Pantograph (goal RPC, used by LeanDojo-v2), Kimina Lean Server. No Lean or Rocq embedding of TLA+
  semantics exists; Isabelle has one (TLAPS's Isabelle/TLA object logic, HOL-TLA session).
- Pushed to `github.com/scidonia/model-or-proof`; the §11 and §12 decisions are settled (Lean 4 +
  Mathlib, general-tier headline verdict, 2 h/$50 per-run caps, human statements but no human tactics,
  safety before liveness, EWD998 as the externally calibrated task).

## P1 — Harness and calibration (next)

Deliverables:

1. `harness/tlc_run.py` — invoke TLC through the dev shell, time it, parse the **final** summary
   (`N states generated, M distinct states found, K states left on queue`, search depth), emit one
   result row per §6 of the protocol. Progress lines must never be mistaken for the summary.
2. `harness/result.py` — the row schema, the cost ledger, `results/*.jsonl` append, session-id capture.
3. `harness/closure.py` — the AI closure loop skeleton with the prover interface behind a port, so the
   loop can be exercised against a stub prover without any model call.
4. `tasks/token-ring.json` — the manifest: property, `N₀`, budgets, mutant, artifacts.
5. `docs/equivalence-token-ring.md` — the line-correspondence audit between the TLA+ module and the
   prover model (written once the prover exists).
6. Behavior contracts and scenarios under `tests/`, per the repository's contract policy.

Acceptance checks:

- `nix develop -c pytest` (or the shell's chosen runner) is green, and each scenario was observed
  failing before the code that satisfies it.
- A five-repetition cell of Route A for token-ring produces five rows that agree on distinct states
  and depth (determinism), with `startup_s` separated from `search_s`.
- The mutant task produces `outcome: violation` **with a trace path recorded**, never `success`.
- A forced timeout produces `outcome: timeout` with states reached, and does not mark the property
  refuted or established.
- No scenario reaches the network or a model: the loop is exercised against the stub prover only.

## P2 — Prover, model, and closure loop (blocked on §12 decision)

1. Pin the toolchain in the dev shell (for Lean: `elan` + `lake`, project pinned to Mathlib's
   `lean-toolchain`, `lake exe cache get` for oleans; the nixpkgs `lean4-4.30.0` is behind Mathlib's
   pin, so the toolchain comes from elan, not nixpkgs).
2. Port the token-ring model and `Mutex` to the prover: general theorem, plus the `N₀` corollary.
3. Drive the closure loop through `lean-repl`/Pantograph, one tactic at a time, with the goal state fed
   back to the model; assert at the end that the artifact contains no `sorry`/`Admitted` and that the
   statement is unchanged from the planner's.
4. Record tokens and dollars per run from the session records; flag fallback-model turns.

Acceptance checks:

- The positive theorem closes within budget in at least one repetition, the artifact compiles with
  zero unclosed goals, and the row's cost equals the summed session usage.
- The mutant fails to close inside budget, and the row says which way it failed.
- Re-running the same cell twice produces different token counts (stochastic side is visible in the
  data) while the artifact check stays objective.

## P3 — Task set

Add two-phase commit (or Paxos agreement), LCR leader election, cache coherence, and — if liveness is
in scope — one fairness-dependent property. Each with: TLA+ module, `.cfg` per instance, mutant,
prover model, equivalence audit, `N₀` fixed by calibration against the TLC budget.

## P4 — Analysis and write-up

Cost curves per route, the ratio distribution per task, pass rates across repetitions, and the verdict
against each reading of "replacement" in protocol §3 (`K`, `B`, coverage). Output lives in `wiki/`;
whether it becomes a paper or post is open question 8.

## Risks

| Risk | Handling |
| --- | --- |
| Translation bias (prover model written by the same hands as the spec) | committed equivalence audit; mutants checked on both routes; TLAPS as spec-constant control if bias turns out dominant |
| Tier asymmetry (instances vs theorems) | the two-tier framing is mandatory in every report; never pool tiers |
| Closure loop is stochastic | `R ≥ 5` per cell, pass rates and distributions, budgets fixed in advance |
| Toolchain drift | versions pinned in the flake and recorded per row; Lean toolchain pinned by `lean-toolchain` |
| TLC timeout mistaken for a result | `timeout` is a first-class outcome; states reached are reported |
| Cost attribution disputes | both components (compute, tokens) reported separately with their basis stated |
| Blocked on credentials | Route A and the harness proceed without any; Route B needs provider access; pushing needs a GitHub token |

## Open decisions and blockers

Decisions: settled — see `docs/protocol.md` §11 and §12.

Blockers: a Route B model provider with working credentials (DeepSeek and Groq authenticate here; the
OpenAI and Anthropic keys on this host are rejected). Repository creation is no longer a blocker.
