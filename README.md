# model-or-proof

An experiment on one question: **for the same concurrent system, is it feasible to replace model
checking with proof — and what does each actually cost in wall-clock time and dollars?**

Model checking a TLA+ specification with TLC is push-button, exhaustive over a *bounded* instance,
and its cost grows exponentially in the instance parameter. A proof in a theorem prover yields the
*general* theorem, and used to cost a specialist weeks. AI-driven proof closure changed the second
half of that sentence, so the comparison is worth redoing with money and time attached.

**Results so far:** token-ring and Bakery both have their Route B cells complete — the general
theorem closed at `R ≥ 5` on one seed digest per task, with a negative control that holds. The
three-way comparison (TLC / AI closure loop / published human) lives in
`wiki/token-ring-route-a-vs-route-b.md`, with Bakery in its §9; LCR follows. Cost varies by task:
Bakery's median is about 4× token-ring's on a theorem of comparable shape, so medians are quoted
with their ranges rather than as a single price.

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

That prior art is now committed here at pinned provenance, so it can be checked offline: the EWD998
specification, the paper's `N = 3` config and both TLAPS proofs (`tlaplus/Examples` @ `3dfe0087…`, MIT,
with the four MIT CommunityModules modules TLC needs to parse it vendored beside them), and the
IJCAR 2010 Peterson/Bakery/Paxos modules (`tlaplus/tlapm` @ `7824dab5…`, BSD-2-Clause). The published
human-effort figures are carried as cited data in `results/human.jsonl` — a separate artifact that no
measurement path writes and that is never pooled with Route A or Route B — with the attribution, the
partiality and person-day caveats, and the published-versus-artifact disagreements in
[docs/human-baseline.md](docs/human-baseline.md). The imported proofs are **not** machine-checked here
(`tlapm` is not in the dev shell and is never invoked), which the data states explicitly.

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
| Published human-proof baseline: pinned EWD998 + IJCAR 2010 import, cited figures in `results/human.jsonl` | done — see [docs/human-baseline.md](docs/human-baseline.md) |
| EWD998: import (pinned branch head + publication-era revision), TLC calibration reproducing the published figures | done — measured numbers and the drift at the pin are in [docs/human-baseline.md](docs/human-baseline.md) |
| Harness (both routes) + behavior contracts | **built** — both runners, the closure oracle, the mutant controls, guard 53 green; see [plans/](plans/) |
| Lean 4 + Mathlib provisioning (elan, Mathlib oleans) and the closure loop | **working** — Route B closes general theorems on three tasks |
| **P2 task set**: two-phase commit/Paxos, LCR election, cache coherence (EWD998 imported and calibrated above) | **LCR built** — spec, Lean model, both mutants, audit, and `n₀` = 10 calibrated; two-phase commit/Paxos and cache coherence planned |
| Results, analysis, write-up in `wiki/` | **in progress** — `wiki/token-ring-route-a-vs-route-b.md`, sections 1–9; EWD998's Lean port outstanding |

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
| 17 | 33.4 s | — | 3 342 336 | — |
| 23 | 6 748.6 s | 3 472 883 713 | 289 406 976 | 91 |

Distinct states grow ≈`2.2^N` (N=17→23 is ×86.6 against `2.2^6 ≈ ×113`); wall-clock tracks the state
curve, not a flat doubling every second node — N=17→23 is ×202.6 in time against ×86.6 in states, ≈×2.3
per state. That growth is what Route B is being measured against, and it is why `N₀` is fixed per task by
calibration rather than guessed.

The mutant — `TokenRingMutant.tla`, which drops the token-holding guard on `Enter` — is caught by TLC
as required, with the counterexample trace:

```
State 5: <Enter line 26, col 5 to line 28, col 22 of module TokenRingMutant>
/\ token = 0
/\ pc = (0 :> "crit" @@ 1 :> "crit" @@ 2 :> "idle")
```

### EWD998, the externally calibrated task

EWD998 (Safra's termination detection) is the one task with published numbers to calibrate against
(protocol §11 decision 6). Two revisions are committed, both byte-for-byte at pinned provenance: the
**pinned branch head** (`specs/tla/ewd998/`, `3dfe0087…`, with both configs, both TLAPS proofs and the
four CommunityModules modules TLC needs) and the **publication-era revision**
(`specs/tla/ewd998-paper/`, `75f2a7a7369d`) — see each directory's `PROVENANCE.md` and
[docs/human-baseline.md](docs/human-baseline.md).

Both run the paper's `N = 3` instance through the harness — the same instrument as every other Route A
row, with the vendored modules resolved from the spec's own directory and no library-path plumbing:

```bash
nix develop -c python -m harness.tlc_run --task tasks/ewd998-paper.json --results results --reps 1
nix develop -c python -m harness.tlc_run --task tasks/ewd998.json --results results --reps 1
```

| | distinct states | states generated | depth | wall-clock |
| --- | --- | --- | --- | --- |
| Published — the artifact's own table, measured 01/2021 | 1.3m | 10.1m | 60 | 42 s |
| Publication-era revision `75f2a7a7369d` — reproduces it | **1 384 582** | 10 150 343 | **60** | 32.1 s |
| Pinned branch head `3dfe0087…` — has drifted | **1 520 618** | 11 238 019 | **59** | 35.5 s |

The publication-era revision reproduces the published figures (1.3 million distinct states, 10.1m
generated, and the diameter exactly at 60); the pinned branch head does not, and the cause is upstream:
commit `dafe1e5c8a74` (2023-07-28) widened one line of `Init` so the token may start at any node,
*after* the table's figures were recorded in `2589f6465cc5` (2021-01-21). All three rows are recorded
and none is reconciled: the pinned spec is not edited back to the 2021 `Init`, the paper-era revision is
a separate directory rather than a modification of the pin, and no flag is tuned to move the numbers.
Details in [docs/human-baseline.md](docs/human-baseline.md).

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
