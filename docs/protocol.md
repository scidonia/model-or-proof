# Experiment protocol

**Question.** For one and the same concurrent or distributed system, and one and the same
property, what is the differential in **wall-clock time** and **monetary cost** between

- **Route A — model checking:** a TLA+ specification checked by TLC over a bounded instance, and
- **Route B — proof:** the same system and property as a theorem in a proof assistant, with the
  proof **closed by an AI loop** that iterates on failing proof states and pays model tokens?

Sub-question: **is it feasible to replace model checking with proof** for such systems, and under
what conditions?

This document fixes the method before any number is collected, so that the numbers mean something.
It is the contract of the experiment, not a plan of work; the plan of attack is in `plans/`.

---

## 1. Hypotheses

| # | Hypothesis | How it would be refuted |
| --- | --- | --- |
| H1 | For instances TLC completes, AI proof closure costs *more* wall-clock and dollars per task than TLC. | Any task where Route B closes within the Route A wall-clock time at comparable or lower cost. |
| H2 | TLC's cost grows exponentially in the instance parameter `N`; the proof route's cost is close to flat in `N`, because the theorem proved is general and instantiation is free. | Measured TLC growth slower than exponential, or proof cost scaling with `N`. |
| H3 | A prover route can deliver the **general** statement (all `N`) at a bounded cost for at least a subset of the task set — the qualitative advantage that model checking cannot buy at any budget. | No task in the set reaches the general statement within the budget. |

Explicit non-goals: no claim about human interactive proof engineering effort; no claim about bugs
found in real deployed systems; no claim that either route is generally superior outside this task set.

## 2. What exactly is compared

One **task** = one system, one property, one instance parameter `N`, one mutant (see §5).

- **Route A.** TLA+ module + `.cfg` in `specs/tla/<task>/`, run as
  `tlc -workers 1 -config <task>.cfg <Task>.tla`, breadth-first, exhaustive over the bounded instance.
  Recorded: generated/left-on-queue states, distinct states, search depth, wall-clock, peak RSS.
- **Route B.** A model of the same transition system and the same property in the chosen prover and
  library (`proofs/<prover>/<task>/`), stated as a general theorem, closed by the AI loop (§8) under a
  wall-clock and token budget. Recorded: model, turns, tokens, dollars, wall-clock, artifact diff.

Both routes answer in **two tiers**:

| Tier | Statement | Route A | Route B |
| --- | --- | --- | --- |
| 1 — bounded | "the property holds for every execution with `N ≤ N₀`" | exhaustive search at `N₀` | instantiate the general theorem at `N₀` (one tactic); if the general theorem is out of reach, prove the bounded claim directly |
| 2 — general | "the property holds for all `N`" | not obtainable; the answer is the extrapolated cost curve | the theorem itself |

A run is **settled** only when the property is established *and* the mutant fails as predicted (§5).
Anything else is an outcome, not a result.

## 3. What "replacing model checking with proof" is taken to mean

Three candidate readings, all reported rather than one being chosen for the reader:

1. **Cost parity at the bounded tier** — Route B settles the Tier-1 question at a cost within a factor
   `K` of Route A. `K = 1` is the strict reading ("as cheap as model checking").
2. **Bounded budget for the general tier** — Route B proves the Tier-2 theorem within budget `B`
   where Route A cannot answer at any cost. This is replacement of the *question*, not of the runtime.
3. **Coverage under a fixed budget** — for a fixed budget, how many tasks of the set does each route
   settle. Route A's answer stops at `N ≤ N₀`; Route B's covers all `N` or fails.

`K` and `B` are open decisions (§11).

## 4. Fairness controls

1. **One property, one system.** The TLA+ module is the reference semantics. The prover model is
   audited against it statement by statement; the audit is committed as `docs/equivalence-<task>.md`
   with a line correspondence table. The prover model may be idiomatic — it may not strengthen the
   assumptions or weaken the goal.
2. **Instance agreement.** For each task, `N₀` is fixed before the runs: the largest `N` for which
   Route A completes inside the time budget in a calibration run. Both tiers are evaluated at that `N₀`.
3. **Both routes are falsifiable on the same mutant** (§5). If they disagree on a mutant, the task is
   mis-specified and its numbers are discarded until fixed.
4. **Fixed machine and versions.** Single host, no concurrent load; tools pinned by the repo's nix
   flake (prover and TLC versions recorded per row). TLC flags fixed: `-workers 1` for determinism,
   explicit heap, `-fp`/`-seed` pinned where supported and recorded.
5. **Fixed model for the AI loop.** One model selector per run condition, thinking level recorded,
   temperature fixed by the harness. A turn served by a fallback model is recorded (`resolvedModelIsFallback`)
   and the run is flagged; fallback runs are reported separately, not pooled.
6. **Startup cost separated.** TLC's JVM start (measured ≈0.6 s) and the prover's environment/olean
   load are reported as `startup_s` distinct from `search_s` / `proof_s`.
7. **Stochastic side gets repetitions.** The AI loop is a sampling process. Every (task, route, tier)
   cell runs `R` repetitions (`R ≥ 5` per cell, fixed budget); results are reported as pass rate
   (`pass@1` and `pass@R`) plus the distribution of wall-clock and cost, never as a single number.
8. **Human intervention is off for the proof**, except for the model↔spec translation and the lemma
   *statements* (not their proofs). Any human tactic inserted into a proof is logged and marks the run
   `assisted`.
9. **Auxiliary invariants are data, not noise.** If Route B needs an inductive invariant that the TLA+
   spec states only implicitly, that is recorded as `auxiliary_invariants` with its size — it is part
   of the real cost of the proof route.

## 5. Negative controls (mandatory, per task)

Each task ships a **mutant**: the same system with the property made false (e.g.
`specs/tla/token-ring/TokenRingMutant.tla` drops the token-holding guard on `Enter`).

- Route A must report an invariant violation *with a trace*.
- Route B must fail to close within budget, or produce a disproof/countermodel — the report says which.
- A rig that reports success on a mutant is broken: its numbers are discarded and the harness contract
  is re-checked before any other run.
- **Vacuousness guard:** the prover's theorem must be non-trivial — a run in which the statement can be
  closed by `decide`-style automation with no induction, on a system where the TLA+ mutant is caught, is
  investigated before its numbers are used.

## 6. Metrics and the result row

Every run appends one JSON object to `results/<route>.jsonl`:

```json
{
  "task": "token-ring",
  "route": "tlc",
  "tool": {"name": "tlaplus", "version": "1.7.4", "jvm": "1.8.0_504"},
  "param_N": 13,
  "tier": 1,
  "repetition": 2,
  "outcome": "success",
  "wall_clock_s": 1.99,
  "startup_s": 0.61,
  "cpu_s": 1.94,
  "peak_rss_mb": 320,
  "cost_usd": 0.000401,
  "cost_basis": "compute@0.20 USD/h",
  "tlc": {"generated": 1118209, "distinct": 159744, "left": 0, "depth": 27, "workers": 1, "fp": "p9", "seed": "auto"},
  "proof": null,
  "artifacts": {"spec": "specs/tla/token-ring/TokenRing.tla", "log": "results/logs/…"},
  "negative_control": {"mutant": "TokenRingMutant.tla", "expected": "violation", "observed": "violation"}
}
```

- **Route A cost** is compute only: `wall_clock_s × host_rate`. The host rate is stated once, in the
  README, with the measurement basis; dollars are otherwise zero for this route.
- **Route B cost** is `usage.cost.total` summed over the loop's session records (tokens at list price,
  per the provider's published rates) plus compute. Both components are reported.
- **Per-property normalisation**: results are also reported per property per task, since tasks differ
  in state-space size and proof length.

## 7. Route A measurement procedure

- Invocation and parsing are implemented once, in `harness/`, and pinned by a behavior contract
  (`tests/`, per the repository's contract policy).
- The **final** summary is authoritative:
  `<G> states generated, <D> distinct states found, <L> states left on queue` plus
  `The depth of the complete state graph search is <depth>`. TLC also emits periodic `Progress(…)`
  lines that contain the same phrases; the parser must take the last summary after the run ends, never
  a progress line. This is an observed hazard, and a scenario covers it.
- Determinism: with `-workers 1`, generated/distinct/depth repeat exactly across runs. The fingerprint
  seed printed in the banner varies between runs; it is recorded, and pinned with `-fp`/`-seed` where
  TLC accepts it.
- Timeout policy: on timeout the run is recorded as `timeout` with states reached so far, and the
  property is *not* reported as refuted or established.
- Measured reference curve (TokenRing, x86_64, 1 worker, includes JVM start) — recorded to show the
  shape Route B is compared against:

  | N | wall-clock | distinct states |
  | --- | --- | --- |
  | 3 | 0.63 s | 36 |
  | 5 | 0.64 s | 240 |
  | 7 | 0.68 s | 1 344 |
  | 9 | 0.73 s | 6 912 |
  | 11 | 1.01 s | 33 792 |
  | 13 | 1.99 s | 159 744 |
  | 15 | 7.2 s | ≈3.4·10⁵ |
  | 17 | 33.4 s | ≈3.2·10⁶ |

  Growth is ≈`2.2^N` distinct states: doubling the wall-clock roughly every +2 nodes. This is H2's
  subject, and it is why `N₀` must be fixed per task by calibration.

## 8. Route B measurement procedure

**Prover and library: decision pending — see §12.** Once fixed, the procedure is:

- The loop is an OMP session with a fixed prompt and a fixed tool set: read the proof file, apply a
  tactic, compile (`lake build` / prover equivalent), read the resulting goal state, repeat. The
  session terminates when the artifact compiles with no unclosed goal (`sorry`/`Admitted`/`axiom`
  count is asserted zero by the harness, not trusted from the transcript).
- Budget: wall-clock cap and token cap per run, both recorded. A run that exceeds either is
  `timeout`, with the partial artifact and the last goal state kept.
- Cost: summed `usage.cost.total` from the session records in `~/.omp/agent/sessions/`, keyed to the
  run's session id; the harness writes the session id into the row.
- The proof may introduce helper lemmas. Their statements are the researcher's (translation work,
  like writing the spec); their proofs must be the loop's. Any hand-written tactic marks the run
  `assisted`.

## 9. Task set

| Phase | Tasks | Property | Purpose |
| --- | --- | --- | --- |
| P1 calibration | TokenRing (done), Bakery, independent counter + termination detection | safety invariants | fixes `N₀`, validates both rigs and both mutants end to end |
| P2 systems | Two-phase commit / Paxos agreement, leader election (LCR), cache coherence, Raft log matching | safety; liveness only where fairness assumptions are standard | the real comparison |
| P3 (optional) | One task with an *unbounded* state per node (queue contents, log length) | safety | where TLC needs an abstraction that the proof does not |

Each task contributes: a TLA+ module, a config per instance, a mutant, a prover model, an equivalence
audit, and a manifest entry (`tasks/<task>.json`: property, `N₀`, budgets, mutants).

## 10. Threats to validity

- **Translation bias.** The prover model is written by the same hands that wrote the spec. Mitigation:
  the equivalence audit is a committed artifact, and mutants are checked on both routes.
- **Tier asymmetry.** Route A proves instances, Route B proves theorems. Tiering (§2) is the honest
  way to compare; pooling the tiers hides the whole point.
- **Automation asymmetry of a different kind.** Model checking is push-button; proof is search over a
  tactic space. The AI loop changes that cost but does not remove induction-invariant invention (§4.9).
- **One model, one harness.** Results are conditional on the chosen model, thinking level, and prompt.
  Absolute numbers will not transfer; the *ratio* between routes is the durable output.
- **Version drift.** Provers and their libraries change fast; TLC and the prover versions are pinned
  per row so a re-run can be attributed.
- **Machine variance.** Wall-clock is host-specific; CPU seconds and state counts are reported alongside.

## 11. Open questions to settle before runs (protocol questions)

1. **Replacement criterion** — which of §3's three readings is the headline, and what are `K` and `B`?
2. **Model matrix** — one frontier model, or a small matrix (cheap/expensive) to separate "proof is
   expensive" from "this model is expensive"?
3. **Budgets** — per-task wall-clock cap and token/dollar cap for Route B; TLC's per-run cap.
4. **Liveness** — out of P1, in P2? Liveness needs fairness assumptions on both sides, which is extra
   translation work and another place for the comparison to go unfair.
5. **Human role** — may a human repair the spec mid-run, and may a human supply the inductive invariant
   (arguably the intellectual core of proof work)? Default in this protocol: spec yes, invariant no;
   supplying it marks the run `assisted`.
6. **Task-set composition** — which P2 systems are in, and is a "wall-clock hour where TLC dies"
   instance required (i.e. do we need one instance where model checking genuinely fails)?
7. **Cost basis** — list price for tokens (assumed in §6), and which host rate for compute, including
   whether the researcher's own time is costed at all.
8. **Output** — results stay in-repo, or a written report/paper is the deliverable?

## 12. Decision: prover and library

The choice is constrained by the experiment's own subject — **AI-driven proof closure** — so the
deciding criterion is tooling for machine-closed proofs, not only library coverage:

| Option | Library | Strongest argument | Weakest point |
| --- | --- | --- | --- |
| **Lean 4 + Mathlib** | Mathlib (`Finset`, `Multiset`, relations), Std | by far the widest AI-closure tooling and benchmark ecosystem (LeanDojo/REPL, prover models trained on Lean goals); nix-provisionable (`elan-4.2.4`, `lean4-4.30.0`) | untyped TLA+ semantics must be encoded; well-foundedness/induction must be supplied explicitly |
| Rocq/Coq + MathComp | MathComp, stdlib | mature, precise, strong for finite structures and protocols | thinner AI-closure tooling; more manual proof engineering |
| Isabelle/HOL + AFP | AFP | strongest *classical* automation (Sledgehammer + Z3/CVC5), good protocol material | heaviest provisioning; LLM tooling least developed |
| Dafny 4.11 (SMT) | built-in | auto-active: invariants + SMT; measures verification time natively; cheapest route to a real comparison | closes by solver, not by AI proof search — it answers "is SMT-based verification cheaper than model checking", a different question |
| TLAPS | TLA+ proof system | same specification language as Route A — removes translation bias entirely | laborious, weakly automated, little AI tooling; likely too slow to be a fair cost comparison |

**Recommendation: Lean 4 + Mathlib as the primary prover**, with **Dafny** as an optional cheap
auto-active control in P3 and **TLAPS** as an optional spec-constant control if translation bias turns
out to be the dominant threat. Rationale: the experiment's independent variable is AI closure, and
Lean is where that tooling exists; it is also provisionable from nixpkgs on this host, which keeps the
environment reproducible.

**Open sub-question:** whether to formalise TLA+ *inside* Lean (a semantics embedding, so both routes
share the spec text) or write idiomatic Lean models plus the equivalence audit (§4.1). An embedding
would remove translation bias and add the semantics proof as a cost on Route B; an idiomatic model is
cheaper and more comparable to what practitioners actually do.
