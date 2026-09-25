# model-or-proof

An experiment on one question: **for the same concurrent system, is it feasible to replace model
checking with proof — and what does each actually cost in wall-clock time and dollars?**

Model checking a TLA+ specification with TLC is push-button, exhaustive over a *bounded* instance,
and its cost grows exponentially in the instance parameter. A proof in a theorem prover yields the
*general* theorem, and used to cost a specialist weeks. AI-driven proof closure changed the second
half of that sentence, so the comparison is worth redoing with money and time attached.

## Method in one screen

For each task (one system, one property, one instance parameter `N`, one mutant) both routes run:

| | Route A — model checking | Route B — proof |
| --- | --- | --- |
| Tool | TLA+ / TLC | proof assistant + library, proof closed by an AI loop |
| What it establishes | the property for all executions with `N ≤ N₀`, exhaustively | the general theorem for all `N`; `N₀` instances follow by instantiation |
| Cost measured | wall-clock, CPU, peak RSS, distinct states; dollars = compute × host rate | wall-clock, model tokens and dollars, turns, artifact size |
| Falsification | mutant spec must yield a violation *with a trace* | mutant must fail to close, or yield a disproof |

Result rows land in `results/*.jsonl`; the schema, the fairness controls, the negative controls, the
statistics (`R ≥ 5` repetitions per cell, pass rates, not single numbers), and the threats to validity
are fixed in **[docs/protocol.md](docs/protocol.md)** *before* numbers are collected.

### Decision pending: prover and library

`docs/protocol.md` §12 lays out the options with evidence. Recommendation: **Lean 4 + Mathlib**,
because the experiment's independent variable is AI proof closure and Lean is where that tooling and
the trained prover models are. Dafny is the cheap auto-active (SMT) control; TLAPS is the only route
that proofs the *same* TLA+ text, at the cost of weak automation. No Lean or Rocq embedding of TLA+
semantics exists — only Isabelle has one (TLAPS's Isabelle/TLA object logic, and the HOL-TLA session),
so Route B will state idiomatic models plus a committed equivalence audit against the TLA+ module.

## Status

| Piece | State |
| --- | --- |
| Repository bootstrap, nix dev shell | done |
| TLA+ side: `TokenRing` spec, mutant, measured cost curve | done |
| Harness (both routes) + behavior contracts | next — see [plans/2026-09-25-bootstrap.md](plans/2026-09-25-bootstrap.md) |
| Prover model + AI closure loop | blocked on the §12 decision |
| P2 task set (consensus, election, coherence) | planned |
| Results, analysis, write-up | not started |

The repository is not yet pushed to `github.com/scidonia/model-or-proof` (no credentials on this host).

## The TLA+ side, already measured

Run through the dev shell, single worker for determinism:

```bash
nix develop -c bash -c 'cd specs/tla/token-ring && tlc -workers 1 -config TokenRing.cfg TokenRing.tla'
```

`TokenRing` (x86_64, one worker, includes the ≈0.6 s JVM start):

| N | wall-clock | generated | distinct | depth |
| --- | --- | --- | --- | --- |
| 3 | 0.63 s | 73 | 36 | 11 |
| 5 | 0.64 s | 721 | 240 | 11 |
| 7 | 0.68 s | 5 377 | 1 344 | 13 |
| 9 | 0.73 s | 34 561 | 6 912 | 15 |
| 11 | 1.01 s | 202 753 | 33 792 | 17 |
| 13 | 1.99 s | 1 118 209 | 159 744 | 19 |
| 15 | 7.2 s | — | ≈3.4·10⁵ | — |
| 17 | 33.4 s | — | ≈3.2·10⁶ | — |

Distinct states grow ≈`2.2^N`; wall-clock doubles about every second node. That exponential is what
Route B is being measured against, and it is why `N₀` is fixed per task by calibration rather than
guessed.

The mutant — `TokenRingMutant.tla`, which drops the token-holding guard on `Enter` — is caught by TLC
as required, with the counterexample trace:

```
State 5: <Enter line 26, col 5 to line 28, col 22 of module TokenRingMutant>
/\ token = 0
/\ pc = (0 :> "crit" @@ 1 :> "crit" @@ 2 :> "idle")
```

## Layout

| Path | Purpose |
| --- | --- |
| `docs/protocol.md` | The experiment protocol: hypotheses, metrics, controls, statistics, threats |
| `plans/` | Plan of attack, phase by phase |
| `specs/tla/<task>/` | TLA+ modules, `.cfg` per instance, and each task's mutant |
| `proofs/<prover>/<task>/` | Prover models and proofs for Route B |
| `harness/` | Both runners: TLC invocation and parsing, AI closure loop, result rows |
| `tests/` | Behavior contracts for the harness, with executable scenarios |
| `results/` | `*.jsonl` result rows, logs, cost ledger |
| `wiki/` | Narrative documentation, updated as the work lands |

## Requirements

- Nix with flakes — the dev shell pins TLC 1.7.4 (TLC 2.19) and the harness's Python.
- Route B additionally needs the prover toolchain (§12) and provider credentials for the closure model.
- No shell activation is required: every command runs as `nix develop -c <command>`.

## Open protocol questions

The questions that must be answered before runs start — replacement criterion and its factor `K` and
budget `B`, model matrix, budgets, whether liveness is in scope, the human role in supplying an
inductive invariant, task-set composition, cost basis, and the output format — are listed in
`docs/protocol.md` §11 and tracked in the plan.
