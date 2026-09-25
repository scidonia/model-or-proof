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

## Why this is not already answered

The comparison has been made before, but only with *human* proof effort, and never with money attached:

- **TLC vs Apalache vs TLAPS on one specification** (EWD998, Safra's termination detection) — Konnov,
  Kuppe, Merz, ISoLA 2022: TLC finds 1.3M distinct states in 42 s at `N=3`, 219M in about 50 minutes at
  `N=4`, and is hopeless beyond; Apalache checks an inductive invariant at `N=100` in 20 s; the TLAPS
  invariance proof took **one person-day and about 230 lines**.
- **TLC vs TLAPS on Pastry** (Lu, Merz, Weidenbach, FORTE 2011): TLC spent *more than a month* over
  1.95 billion states without a counterexample; the proofs followed, and the paper's conclusion is that
  interactive proof effort "is too high to scale to more complete P2P protocols".
- Industrial baselines: 10 AWS systems, specifications of 102–939 lines, 2–3 weeks of tool learning,
  0–3 bugs each; seL4 at ≈20 person-years and ≈480k lines of proof.

What has changed is the price of proof search. **No published work prices an AI-driven proof loop
against TLC's runtime for the same specification** — that is the gap this repository fills, and EWD998
is in the task set precisely because published TLC/TLAPS numbers exist for it and calibrate the rig
against external data.

### Decisions settled 2026-09-25

| Decision | Choice |
| --- | --- |
| Prover + library | **Lean 4 + Mathlib** — where AI proof-closure tooling (lean-repl, Pantograph, Kimina server) and prover-trained models are. No Lean embedding of TLA+ semantics exists, so Route B states idiomatic Lean models plus a committed equivalence audit per task. |
| Headline verdict | **The general theorem within budget** — the claim that would justify replacement, since TLC cannot answer at any budget. Bounded-tier cost ratio and budgeted coverage are reported as secondary. |
| Budgets | 2 h wall-clock and $50 of model spend per Route B run, whichever binds first; the same 2 h cap per TLC run; `R ≥ 5` repetitions per cell. |
| Human role | Specification and lemma *statements* are human; **every proof tactic comes from the loop**. Supplying the inductive invariant marks the run `assisted`. |
| Liveness | Out of P1–P2 (safety only); at most one fairness-dependent liveness task in P3. |
| Cost basis | Tokens at list price (from the session's recorded usage) and compute at a stated host rate, reported separately, never merged. |

One caveat fixed by evidence rather than choice: the loop runs on a **general model**, not a
Lean-specialised prover model — none is reachable from this host's providers.

## Status

| Piece | State |
| --- | --- |
| Repository bootstrap, nix dev shell, push to `scidonia/model-or-proof` | done |
| TLA+ side: `TokenRing` spec, mutant, measured cost curve | done |
| Prover, library, headline criterion, budgets, human role, liveness scope | decided (above) |
| Harness (both routes) + behavior contracts | next — see [plans/2026-09-25-bootstrap.md](plans/2026-09-25-bootstrap.md) |
| Lean 4 + Mathlib provisioning (elan, Mathlib oleans) and the closure loop | P2 |
| P2 task set: EWD998, two-phase commit/Paxos, LCR election, cache coherence | planned |
| Results, analysis, write-up in `wiki/` | not started |

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

## Protocol decisions

The protocol's open questions were settled on 2026-09-25 and are recorded in `docs/protocol.md` §11
(replacement criterion, model policy, budgets, liveness scope, human role, task set, cost basis,
output) and §12 (prover and library choice).
