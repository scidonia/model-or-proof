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

## 1a. Prior art, and the gap this experiment fills

Comparisons of TLC against proof for *one and the same* specification exist — all of them with **human**
proof effort, none with a priced AI loop:

- **Konnov, Kuppe, Merz, "Specification and Verification With the TLA+ Trifecta: TLC, Apalache, and TLAPS"
  (ISoLA 2022)** — <https://members.loria.fr/SMerz/papers/2022-isola.pdf>. "This is the first paper that
  applies all three tools to a common specification" (EWD998, Safra's termination detection). Numbers:
  "fixing N = 3, K = C = 3 and Q = 9, tlc finds 1.3 million distinct states and requires 42 seconds…
  For N = 4 … 219 million distinct states, and tlc requires about 50 minutes"; larger values are
  "hopeless" for TLC. Apalache checks the inductive invariant at `N = 100` in 20 s. The TLAPS invariance
  proof "was written in one person-day and required about 230 lines"; safety plus refinement "about 110
  lines … half a person-day"; liveness "245 lines … less than one person-day".
- **Lu, Merz, Weidenbach, "Towards Verification of the Pastry Protocol using TLA+" (FORTE 2011)** —
  <https://members.loria.fr/SMerz/papers/forte2011pastry.pdf>. TLC spent "more than a month" over
  1 952 882 411 states without a counterexample, then the proofs were done in TLAPS; model building took
  "about 3 months"; the conclusion drawn is that "the effort currently required by interactive proofs is
  too high to scale to more complete P2P protocols".
- **Chaudhuri, Doligez, Lamport, Merz, "Verifying Safety Properties With the TLA+ Proof System"
  (IJCAR 2010)** — <https://members.loria.fr/SMerz/papers/ijcar2010.pdf>. TLAPS proof sizes: Peterson
  mutual exclusion "about 130 lines"; Bakery "800 lines"; Paxos "550 lines … somewhat over 1000".
- **Industrial effort reports**: Newcombe et al. 2015 (10 AWS systems, specifications of 102–939 lines,
  2–3 weeks of tool learning, 0–3 bugs per system); Bornholt et al. 2021 (ShardStore, 16 issues
  prevented). s2n's published verification is Cryptol/SAW/Coq, not TLA+.
- **Proof-effort metrics for scale**: seL4 ≈20 person-years and ≈480k lines of proof; the de Bruijn
  factor ≈4 (proof lines per program line); CompCert ≈87% specification and proof.
- The bounded-instance-versus-general-theorem tradeoff itself is stated in Clarke & Wing 1996 and in the
  seL4 SOSP 2009 paper: model checking settles instances, proof settles the theorem.

**The gap.** No published work compares an AI-driven proof loop's wall-clock **and dollar** cost against
TLC's runtime for the same specification. The Trifecta paper supplies the human-effort baseline for
TLAPS ("one person-day" for an invariance proof); this experiment replaces that person-day with a
measured loop, prices it in dollars, and runs it on specifications TLC already handles — so the
comparison is anchored to published numbers rather than to a new benchmark of our own invention.

**The prior art is committed here, at pinned provenance.** The specifications and proof artifacts the
figures above are taken from are imported byte-for-byte, so every claim about them is checkable offline:

- `specs/tla/ewd998/` — `tlaplus/Examples` @ `3dfe0087a36ccfc6f8aae7de6621c68e06fab955` (`ISoLA2022`,
  MIT): the spec, both configs (`EWD998Small.cfg` is the paper's N = 3 instance, `EWD998.cfg` the
  branch's N = 4), the asynchronous termination-detection spec it instantiates, and both TLAPS proofs;
  plus four CommunityModules modules (`SequencesExt`, `FiniteSetsExt`, `Folds`, `Functions`) vendored
  from `tlaplus/CommunityModules` @ `9aae8ea1318b3ded4629abdccec2c4754b528d70` (MIT), which TLC needs
  on the parse path to read EWD998 at all.
- `specs/tla/ijcar2010/` — `tlaplus/tlapm` @ `7824dab55e0c346e913404d59d0bbdeebce73cc1`
  (BSD-2-Clause): Peterson, Bakery, and Paxos with the trivial consensus spec it instantiates.
- `specs/tla/ewd998-paper/` — the **publication-era** revision of EWD998 (`tlaplus/Examples`
  @ `75f2a7a7369d`, the last revision before the 2023-07-28 `Init` widening), committed so the published
  figures can be *reproduced* rather than only cited. It is explicitly not the pin.

Per-file repositories, commits, upstream paths, licenses, byte/line counts and license notices are in
each directory's `PROVENANCE.md`. **The imported proofs are not machine-checked here**: `tlapm` is not
in the dev shell and is invoked nowhere in this repository, so the proofs are text with provenance
(`machine_checked: false`). The published effort figures are carried as cited data in
`results/human.jsonl` and documented in `docs/human-baseline.md` (§6a). Two disagreements are recorded
there and never reconciled:

- **Published proof lines versus the committed artifacts** — Peterson "about 130" vs 199 lines, Bakery
  "800" vs 383, EWD998's 230 + 110 + 245 vs the artifacts' 863 + 123.
- **Published EWD998 TLC figures against two re-runs** — published distinct 1.3 M / generated 10.1 M /
  depth 60 / 42 s. The **publication-era revision** `75f2a7a7369d` *reproduces* them: 1,384,582 /
  10,150,343 / **60** / 32.1 s. The **pinned branch head** does not: 1,520,618 / 11,238,019 / 59 /
  35.5 s. The drift is one line — `dafe1e5c8a74` (2023-07-28) widened `Init`
  (`token \in [pos: {0}, …]` → `token \in [pos: Node, …]`) *after* the embedded 2021 table was recorded.
  All three rows are measured and stated, never reconciled; the pinned spec is not edited back.

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
2. **Instance agreement.** For each task, `N₀` is fixed before the headline runs: normally the largest
   `N` for which Route A completes inside the time budget in calibration. Both tiers are evaluated at
   that `N₀`. **Paxos agreement is the pre-registered crossover exception:** its `N₀` is chosen by the
   adjacent under-cap, witnessed TLC/Route-B same-claim crossing rule in
   `plans/2026-09-27-paxos-agreement.md` §D3. Its measured cap boundary is recorded separately as
   `n_cap` (or `null` if not established); a timed-out row cannot be the crossing. The exception and
   ballot bound appear in `tasks/paxos.json` so they can be read without reconstructing this decision.
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
10. **Bounded non-vacuity witness.** When a finite projection or bound could make an invariant true by
    preventing the behavior under test, preserve a reachable-behavior counterexample to a separate
    diagnostic predicate for every compared instance. State the instance, property, parameter bounds,
    input config, and actual trace path beside the witness. The diagnostic rows/trace are kept separate
    from the measured Route A/B cells and **do not replace** the mutant, which tests a different failure.
    Without the witness, the positive invariant row is not accepted as a meaningful comparison.
11. **Feasibility checkpoints are not terminal acceptance.** Contracts for later stages are authored
    before implementation and may remain red at a TLC-only calibration checkpoint if the promised Lean
    model and two-layer audit do not exist yet. Record the expected failure and the checkpoint's measured
    rows; neither a placeholder artifact nor a skipped test makes this a successful full task. Before a
    terminal accepted result, the applicable scenarios and full suite must pass. If calibration proves
    the task nonviable, only the planner may replace impossible later-stage scenarios with contracts for
    the actual one-layer audit and explicit nonviability finding, observing the changed scenarios fail
    first. Eligibility for a fast live TLC scenario is not an obligation to duplicate an existing
    measured calibration row in the test suite.

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
- **Route B cost** is the summed provider `usage` (tokens at list price, per the provider's published
  rates) plus compute at the stated host rate. Both components are reported separately.
- **Per-property normalisation**: results are also reported per property per task, since tasks differ
  in state-space size and proof length.

### 6a. The published human baseline is data, not a route

Prior-art human effort is **not** a third `route` value in the schema above, and never appears in
`results/tlc.jsonl` or `results/proof.jsonl`. It is a separate file, `results/human.jsonl`, whose records
carry `kind: "human_prior_art"`, `machine_checked: false`, publication and pinned-source provenance, a
verbatim `quote` for every figure, and `never_pooled_with: ["route_a_measured", "route_b_measured"]` —
and **no** measured field (`route`, `tool`, `wall_clock_s`, `startup_s`, `peak_rss_mb`, `states_reached`,
`cost_usd`, `cost_basis`, `tlc`, `proof`, `outcome`, `repetition`, `tier`, `negative_control`).

The name is the **published human-proof baseline** ("human prior art"); it is never a route and never an
arm. It may be cited and charted *alongside* Route A and Route B, but must never be pooled into their
distribution, ratio, or cost statistic. The caveats that keep that honest — person-days exist only for
EWD998, no person-day is invented for the IJCAR 2010 papers, the Paxos second refinement is incomplete,
and published line counts disagree with the committed artifacts — are in `docs/human-baseline.md` and
are asserted by `tests/human-baseline-contract.md`.

## 7. Route A measurement procedure

- Invocation and parsing are implemented once, in `harness/`, and pinned by a behavior contract
  (`tests/`, per the repository's contract policy).
- The **final** summary is authoritative:
  `<G> states generated, <D> distinct states found, <L> states left on queue` plus
  `The depth of the complete state graph search is <depth>`. TLC also emits periodic `Progress(…)`
  lines that contain the same phrases; the parser must take the last summary after the run ends, never
  a progress line. This is an observed hazard, and a scenario covers it.
- Determinism: with `-workers 1`, generated/distinct/depth repeat exactly across runs. The fingerprint
  polynomial index and seed printed in the banner vary between runs; both are recorded, and pinned with
  `-fp`/`-seed` where
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
  | 17 | 33.4 s | 3 342 336 |
  | 23 | 6 748.6 s | 289 406 976 |

  Distinct states grow ≈`2.2^N` (N=17→23 is ×86.6 against `2.2^6 ≈ ×113`). Wall-clock tracks the state
  curve, not a flat ×2 per +2 nodes: N=17→23 is ×202.6 in time against ×86.6 in states — ≈×2.3 per state,
  a mild extra per-state slowdown at the top end. This is H2's subject, and it is why `N₀` must be fixed
  per task by calibration.

## 8. Route B measurement procedure

**Chosen: Lean 4 + Mathlib**, driven through `lean-repl` (Pantograph is the recorded fallback if
goal-state fidelity proves insufficient). The instrument is `harness/route_b.py` → `harness/closure.py`
→ `harness/lean_repl.py` (the `LeanReplProver` port) and `harness/model.py` (the model client). The
procedure:

- The loop reads the proof file, sends the model the specification — the seed's definitions and
  theorem statement, plus (for a tier-1 corollary) its project-local import's definitions and theorem
  statement *types* — together with the statement under test, the tactic history, and the repl's
  per-turn refusal reason (never a proof body, an invariant, or a helper lemma; the row records the
  prompt's composition). It then receives a tactic, applies it to the repl's in-memory proof state, and
  repeats — there is **no per-turn `lake build`** (the repl
  applies tactics directly; the artifact is written back in place only on closure). The session
  terminates when the repl reports the proof completed **and** the artifact's `sorry`/`sorryAx`/`admit`/
  `Admitted`/`axiom` count is asserted zero by the harness — never trusted from the transcript.
- Budget: 2 h wall-clock and $50 of model spend per run, whichever binds first; both recorded. A run
  that exceeds either is `timeout`, with the partial tactics and the last goal state kept in the row.
- Cost: OMP's recorded `usage.cost` (tokens priced by OMP, §11 decision 7) plus compute at the stated
  host rate; the two components are reported separately, never merged. A mid-run provider failure
  (402/429/5xx) lands a recorded `error` row naming the failure, never a silently lost budget.
- The prompt may **invite** the model to guess an auxiliary invariant or a strengthened hypothesis, but
  never supplies one (D19): a model-guessed helper is the loop's own work — recorded in
  `auxiliary_invariants` with its size and `assisted: false`, and the row shows how it was obtained. A
  **human**-supplied invariant marks the run `assisted: true` (a full-body declaration diff against the
  seed), never by discipline.

## 9. Task set

| Phase | Tasks | Property | Purpose |
| --- | --- | --- | --- |
| P1 calibration | TokenRing (done), Bakery, independent counter + termination detection | safety invariants | fixes `N₀`, validates both rigs and both mutants end to end |
| P2 systems | Two-phase commit / Paxos agreement, leader election (LCR), cache coherence, Raft log matching | safety; liveness only where fairness assumptions are standard | the real comparison |
| P3 (optional) | One task with an *unbounded* state per node (queue contents, log length) | safety | where TLC needs an abstraction that the proof does not |

Each task contributes: a TLA+ module, a config per instance, a mutant, a prover model, an equivalence
audit, and a manifest entry (`tasks/<task>.json`: property, `N₀`, budgets, mutants).

**EWD998 is the externally calibrated task** (decision 6). Its specification, the paper's N = 3 instance
and its TLAPS proofs are imported at pinned provenance, and so is the **publication-era revision** of the
same system (`specs/tla/ewd998-paper/`, `75f2a7a7369d`), because the pinned branch head no longer
reproduces the published figures. Both revisions are run through the same rig (`tasks/ewd998.json`,
`tasks/ewd998-paper.json`), both rows are measured, and all three rows are recorded in
`docs/human-baseline.md`: published 1.3 M distinct / 10.1 M generated / depth 60 / 42 s; publication-era
**1,384,582 / 10,150,343 / 60 / 32.1 s** (a reproduction); pinned branch head
**1,520,618 / 11,238,019 / 59 / 35.5 s** (drifted by upstream's one-line `Init` widening in
`dafe1e5c8a74`, 2023-07-28). Each manifest's instance is `EWD998Small.cfg` (`N = 3`, 2 h budget) and
neither ships a mutant in this phase — the negative control is a P2 task. TLC resolves the vendored
CommunityModules modules from the spec's own directory, with no library-path plumbing.

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

## 11. Decisions (settled 2026-09-25; Paxos exception preregistered 2026-09-27)

| # | Question | Decision |
| --- | --- | --- |
| 1 | Headline reading of "replacement" | **Tier 2: the general theorem within budget `B`**, where TLC cannot answer at any budget. The bounded-tier ratio `K` and the coverage reading are also reported, as secondary. `B` = the per-run cap in row 3; the headline claim is stated per task *and* per task family. |
| 2 | Model matrix | **One model** for the closure loop, one selector for the whole experiment, thinking level fixed by the harness and recorded per row. A matrix is a follow-up experiment, not this one. |
| 3 | Budgets | Route B per run: **2 h wall-clock and $50 of model spend**, whichever binds first. Route A per run: the same 2 h wall-clock cap. `N₀` per task normally = the largest `N` whose TLC run completes inside that cap in calibration. **Paxos agreement exception (§4.2):** select its witnessed, under-cap `N₀` at the measured wall-clock crossover on the theorem-plus-corollary total by the predeclared rule in `plans/2026-09-27-paxos-agreement.md` §D3; record the largest completed cap value separately as measured `n_cap` or `null` if not established. If the crossing is unreachable under the cap, report nonviability instead of substituting a budget-edge `N₀`. |
| 4 | Liveness | **Out of P1–P2.** Safety invariants only until P3, then at most one fairness-dependent liveness task, with the fairness assumption stated on both sides. |
| 5 | Human role | **Specification and lemma *statements* are human; every proof tactic comes from the loop.** Supplying the inductive invariant is out: a run that receives it is `assisted` and reported separately. |
| 6 | Task-set composition | **EWD998 (Safra termination detection) is a must-have**, because published TLC, Apalache and TLAPS numbers exist for it (§1a) and it therefore calibrates our rig against external data. It joins the P2 set alongside two-phase commit/Paxos agreement, LCR leader election, and cache coherence. One instance where TLC genuinely dies (no completion inside 2 h) is required. |
| 7 | Cost basis | Tokens at the provider's **list price** (as recorded in the session's `usage.cost`), compute at a **stated host rate**, researcher time **not** costed. Both components reported separately, never merged into one number. |
| 8 | Output | **In-repo**: `results/` rows plus `wiki/` analysis, with the verdict stated against decision 1. A paper or post is a later, separate decision. |
| 9 | Human prior art | **Published human-proof effort is cited data, never a measured arm.** It lives in its own `results/human.jsonl` as `kind: "human_prior_art"` / `machine_checked: false` records that carry no measured field and are `never_pooled_with` Route A or Route B (§1a, §6a, `docs/human-baseline.md`). No human arm is run. |

One decision is deferred by evidence rather than choice: the closure loop runs on a **general model**,
not a Lean-specialised prover model (no such model is reachable from this host's providers). Every
claim is therefore about a general model driving Lean, and is labelled that way in the write-up.

## 12. Decision: prover and library (settled: Lean 4 + Mathlib)

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
