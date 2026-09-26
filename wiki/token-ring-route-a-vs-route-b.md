# Token-ring mutual exclusion: three routes, side by side

**Status:** first results, 2026-09-26. Working tree at commit `ea2f50b` plus the file-mode fixes.
Every number below traces to a row or artifact named in *Provenance*; nothing here is estimated
except where it says so.

**The property, on all three routes:** `Mutex` — *at most one node is in its critical section at any
time*. TLC checks it as an invariant of `specs/tla/token-ring/TokenRing.tla`; the Lean port states it
as `TokenRing.mutex` in `proofs/lean/token-ring/TokenRing.lean`. The port's correspondence to the
TLA+ reference is a statement-by-statement audit in `docs/equivalence-token-ring.md`, pinned by a
test — an **audit**, not a machine-checked equivalence.

---

**The three results, at a glance** (the same safety property, `Mutex`; details and provenance below):

| # | Route | Result | Wall-clock | Dollar cost | Evidence |
|---|---|---|---|---|---|
| 1 | **A — TLC** (machine, TLA+) | `Mutex` at the bounded instance N=23 | **837.9 s** (13 m 58 s, eight workers) | **$0.04655** | 289,406,976 distinct states enumerated |
| 2 | **B — AI closure loop** (Lean) | `Mutex` for **arbitrary N** | **104.8 s** (cell median; six closures, 62.9–1021.8 s) | **$0.00033** | `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`; statement and definitions byte-identical |
| 3 | **Human — published** (TLAPS/TLA+) | invariance / mutual exclusion | **1 person-day** (EWD998 invariance; IJCAR papers report lines only) | not published | the published proofs, imported with quotes and provenance |

Rows 1 and 2 are not the same claim — bounded instance versus general theorem — and row 3 is *cited
data*, never a measured arm. See §4 for which task each human figure attaches to, and §5 for what is
still pending.

---

## 1. The three routes in full

| | **Route A — TLC** | **Route B — AI closure loop** | **Human — published prior art** |
|---|---|---|---|
| What was done | enumerated reachable states of the TLA+ spec | proved the Lean theorem | wrote proofs by hand |
| Claim established | `Mutex` at the bounded instance **N=23** | `Mutex` for **arbitrary N** | `Mutex`/invariance, per paper |
| Distinct states | **289,406,976** (3,472,883,713 generated, depth 91) | — (no enumeration) | — |
| Wall-clock | **837.9 s** (13 m 58 s), eight workers | **104.8 s** (cell median, six closures), **1 round / 1 turn** each | EWD998 invariance: **1 person-day**; IJCAR trio: lines only |
| Cost | **$0.04655** (compute @ $0.2/h + tokens, eight workers) | **$0.000326** (provider usage, cell median) | not published in dollars |
| Peak memory | **8,724 MB** | ~9 GB (prover's Lean repl, Mathlib loaded) | — |
| Evidence of success | the enumeration completes | `#print axioms TokenRing.mutex` ⊆ `{propext, Classical.choice, Quot.sound}`; statement + all definitions byte-identical to the seed | the published proof |
| Toolchain | TLC 2.19, `workers: 8` | `omp` 18.3.1 session, `deepseek-v4-pro` (thinking high), Lean 4 `v4.35.0-rc3` | TLAPS / TLA+ proof language |

**Same-claim pair, now measured.** Route A's N=23 row and Route B's tier-1 corollary
(`TokenRingN0.lean`, "N=23 instantiated") are the *same claim*, and both are now measured:

| | Route A — TLC (8 workers) | Route B — the corollary |
|---|---|---|
| claim | `Mutex` at N=23 | `Mutex` at N=23 |
| wall-clock | 837.938 s | **26.362 s** |
| cost | $0.04655211 | **$0.000197** (cell median) |
| distinct states | 289,406,976 | — (no enumeration) |
| turns | one deterministic run | 1 |
| closures | one deterministic run | **5**, 25.1–48.5 s |

A single-worker TLC row for the same instance also exists — 6,748.604 s and $0.37492244 — but quoting it against Route B would handicap one side: the fairness ruling is that each route runs at its best configuration with the row naming it, and eight workers scales near-linearly here (8.05× on an identical state count, measured at N=23 itself rather than inferred from N=17). Read the pair with the marginal-cost caveat in §7: the corollary's proof is the trivial instantiation of the general theorem, so Route B's honest total for this claim is the general proof plus this instantiation — **the two cells' medians, 104.8 s and 26.4 s, so about 131 s and $0.00052** — against 837.9 s and $0.04655 for Route A: **~6.4× faster and ~89× cheaper as the costs are recorded**. Both cells are now at `R≥5` (six closures for the theorem, five for the corollary, each cell a single seed digest), and both are wide: the theorem's six ran 62.9–1021.8 s, so its median rather than its mean is the figure — and the slowest run closed *because* ruling (a) removed the per-turn cut that would have killed it. The wall-clock ratio is unambiguous; the dollar ratio depends on the billing model, since the harness charges compute per wall-clock hour, not per vCPU-hour. The general theorem in the table above is a strictly stronger result TLC cannot express at all, so that table compares a capability on Route B's side and a cost on Route A's.

## 2. The same three results, at the calibration instance

| | Route A — TLC at N=3 | Route B — the closure loop | Human |
|---|---|---|---|
| States | 36 distinct (73 generated, depth 11) | — | — |
| Wall-clock | **0.66 s** (5 runs: 0.656–0.669 s) | **130.6 s** at tier 2 (the general theorem) | — |
| Negative control | the mutant **violates** `Mutex` (23 distinct, depth 5) | the mutant seed is closed only by a *false* statement, and the harness refuses `sorry` | — |

The calibration instance exists to show the rig works, and it does: TLC finds 36 states at N=3 in
under a second, and the mutant is refuted with a trace.

## 3. Human effort, as the literature reports it

From `results/human.jsonl`, imported with quotes and provenance (protocol §1a). **Two of the three
sources report no human time at all, and the repository does not invent one.**

| Source | Proof | Reports | Figure |
|---|---|---|---|
| EWD998 (ISoLA 2022) | invariance | **person-days** | **1 person-day**, ~230 lines |
| EWD998 (ISoLA 2022) | safety + refinement | **person-days** | **0.5 person-day**, ~110 lines |
| EWD998 (ISoLA 2022) | liveness | **person-days** | **< 1 person-day**, 245 lines |
| IJCAR 2010 (TLAPS) | mutual exclusion | lines only | ~130 lines |
| IJCAR 2010 (TLAPS) | mutual exclusion (2nd system) | lines only | 800 lines |
| IJCAR 2010 (TLAPS) | first refinement safety | lines only | 550 lines |
| IJCAR 2010 (TLAPS) | second refinement | lines only, **incomplete** | "somewhat over 1000" (published as "most of the proof") |

Repository note, verbatim: *"the IJCAR 2010 paper reports TLAPS proof-line counts only; it reports no
person-day figure, and none is invented for it."*

For reference, the machine figures the ISoLA 2022 paper reports for its own TLC run:
**1.3 M distinct states, 42 s** at `N=3, K=C=3, Q=9` — a *machine* number, not a human one.

### Our own human and tooling numbers, labelled as what they are

| What | Effort | Notes |
|---|---|---|
| Host reference proof of `TokenRing.mutex` | 67 lines, one write + two elaboration fixes | `proofs/lean/token-ring/reference/HostReference.lean`; a *control*, not the loop's work |
| The harness that made the autonomous closure possible | ~2 h 10 m end to end (08:07 → 10:16 on 2026-09-26) | of which the file mode itself, from the directive to the first closure, was ~12 minutes; this is **tooling effort**, not proof effort |
| The loop's proof effort | 1 round, 1 turn, 130.6 s, $0.00043 | the number that matters for Route B |

## 4. Who the human comparator actually is, per task

The human baseline exists, but as **published data, not a measured arm** (protocol §6a: "data, not a
route"), with a verbatim quote and pinned-source provenance for every figure, `machine_checked: false`,
and `never_pooled_with: ["route_a_measured", "route_b_measured"]`.

**Both comparators are TLA+.** The machine comparator (Route A) is TLC running our spec; the human
comparator is **TLAPS proofs** — TLAPS being the TLA+ proof system. There is no non-TLA+ comparator in
this report, and **no measured human arm at all**: the protocol makes human interactive proof
engineering an explicit non-goal, so the human column is always cited, never run here. Every human
figure is TLAPS, and the figures attach to specific tasks, which is the point:

| our task | human comparator | figure | source |
|---|---|---|---|
| `ewd998` | TLAPS invariance proof | **1 person-day**, 230 lines | ISoLA 2022 |
| `ewd998` | TLAPS safety + refinement | **half a person-day**, 110 lines | ISoLA 2022 |
| `ewd998` | TLAPS liveness | **< 1 person-day**, 245 lines | ISoLA 2022 |
| `ijcar2010-peterson` | TLAPS proof, mutual exclusion | ~130 lines | IJCAR 2010 |
| `ijcar2010-bakery` | TLAPS proof, mutual exclusion | 800 lines | IJCAR 2010 |
| `ijcar2010-paxos` | first / second refinement | 550 / >1000 lines (**incomplete**) | IJCAR 2010 |
| **`token-ring`** | **none published** | — | — |

So: **the only task with a published *person-day* figure is `ewd998`**, and `bakery`'s comparator is a
*line count* — no time. The token-ring result above, the only closure so far, has **no human comparator
at all**: it is our own bootstrapping model, chosen because TLC handles it, not because the literature
proved it. That is why the plan calls it "one hard case, not the flagship", and why the comparison the
experiment exists for is anchored on EWD998 and the IJCAR trio rather than on this first result.

Three limits recorded and never papered over: **person-days exist only for EWD998** (no figure is
invented for the IJCAR papers), the Paxos second refinement is **incomplete**, and published line counts
**disagree with the committed artifacts** (Peterson "about 130" vs 199 lines; Bakery "800" vs 383;
EWD998's 585 vs 863 + 123). Those disagreements are in `docs/human-baseline.md` and asserted by
`tests/human-baseline-contract.md`.

The protocol's own statement of the gap this closes: *"No published work compares an AI-driven proof
loop's wall-clock and dollar cost against TLC's runtime for the same specification. The Trifecta paper
supplies the human-effort baseline for TLAPS ('one person-day' for an invariance proof); this experiment
replaces that person-day with a measured loop, prices it in dollars, and runs it on specifications TLC
already handles."*

## 5. What is measured, what is pending

- **Measured:** Route A at N=3 (5 runs) and N=23 (1 run, deterministic tool); Route B tier 2 (the
  general theorem, 1 closure) and **tier 1** — the same-claim corollary, closed **five times, the pinned
  seed digest every time**: 25.086, 25.712, 26.362, 38.534 and 48.497 s, median **26.4 s** (the last two
  taken with five runs in flight, which is the likeliest reason they are the slow ones); the negative
  controls on both sides.
- **Pending:** **R≥5** for Route B's *tier-2* cell, which is stochastic (Route A is deterministic, so one
  row is its protocol); the tier-1 cell is complete at five. Wall-clock and cost are not interchangeable
  even within one cell — the fastest tier-1 run was among the most expensive — so any ratio quoted here is
  a ratio of one sample of each. The multi-worker TLC re-run has been taken: 837.9 s at eight workers on
  an identical state count, the figure §1 uses. And Bakery is running under ruling (a), having twice been
  cut by our own bounds before the model proposed a proof.

## 6. Where each route wins, and where this claim stops

The general theorem is a **strictly stronger claim** at far lower **marginal** cost. It is not uniformly
better, and the difference matters:

- **Small instances: TLC wins outright.** 0.66 s at N=3, push-button — no port, no statements, no audit.
  The proof costs 130.6 s *plus* the port, the statements and the audit, i.e. the human side. The proof
  only wins past a **crossover**, and the crossover moves with Route A's configuration. At TLC's best
  configuration measured here — eight workers — it sits near **N≈20** for token-ring (8.0 s at N=17,
  837.9 s at N=23) and near **N≈8–9** for Bakery (2.4 s at N=6, rising to the N=10 cap). Single-worker,
  both crossovers move lower, and 6,748.6 s at N=23 is the one-worker datum, not the comparison.
- **TLC checks the specification's semantics directly.** The Lean route proves a *port*, and
  port-equivalence to the TLA+ is a **hand audit** — the single largest caveat in this report. A
  modelling slip would make the theorem true about the wrong thing.
- **TLC produces a counterexample trace on failure** — the main debugging artifact for a broken design.
  A failed proof yields a goal state, not a trace.
- **The theorem is about a model, not code**, on either route: no refinement to an implementation.
- **`N ≥ 2`, not `N ≥ 1`** — small, but a real loss of generality in the statement (the statement is
  the human's, per plan D5).
- **Safety only.** `Mutex`. Liveness is untouched, and that is where the published EWD998 figures split
  (1 person-day invariance, <1 person-day liveness).

The correct one-line comparison: **Route B answers a question TLC cannot ask — "for all N" — for the
price of a coffee; it is not the same question, not the same artifact, and not free of translation risk.**

## 7. Caveats that belong with these numbers

1. **Different claims.** Route A's row is a bounded instance; Route B's row is arbitrary `N`. The
   cost race needs the tier-1 corollary, which is pending.
2. **Lines are not person-days.** The TLAPS papers report proof lines; only EWD998 reports days.
   Nothing here converts one into the other.
3. **Model, not code.** Both routes prove a property of a *model*, not of running software.
4. **The equivalence is audited, not proved.** Lean-model ≡ TLA+-semantics is a hand audit.
5. **R=1 on Route B.** One closure is an existence proof, not a distribution; a range needs R≥5.
6. **The artifact's durability is handled — but only just.** The closure was copied to
   `results/closures/token-ring/TokenRing-20260926T101642-r1.lean` (digest `9c992250…`) with a sidecar,
   so the result no longer lives only in a gitignored `.runs/` directory that the next sweep deletes.
   A reviewer then showed the sidecar could be bound to bytes the oracle never checked — a swap between
   the check and the digest — which is being fixed by hashing a single immutable snapshot.
7. **Our own verification tooling is days old, and this is the caveat that most changes the reading.**
   The closure oracle — the thing that decides whether a file counts as proved — has had **two soundness
   holes found in a single day**, both by an independent reviewer rather than by the loop, and both now
   failing closed: one let a candidate print a fake axiom report; the other let a candidate *redefine*
   `#print axioms` in its own syntax so the check never ran, which no parser-based check survives. As
   with the hand audit, what is being compared is not only a proof against an enumeration but a
   twenty-five-year-old push-button tool against a young one — and neither hole was visible in a
   passing test suite, which is the argument for the reviewer step existing at all.

8. **Almost every defect found today was one species: a plausible value where an observation was
   needed.** Refusals that could not be told apart (`lean` versus `transport`); a transcript count
   reading `0` when it meant *not yet written*; an axiom report able to say `ok` while meaning *not
   found*; a boundary watcher that could report silence before it had started; a per-turn cut sharing a
   kind with a rig failure; and a hard-coded `"mutex"` standing in for the seed's own theorem name. Each
   is "I saw nothing" reported as "I could not see", or a default reported as a reading. The rule the
   harness converged on, stated once: **a failure must be distinguishable from a silence, and a value
   must be read rather than assumed.** Two mechanisms enforce it — a `kind` on every recorded refusal,
   and an axiom check that reads Lean's elaborated environment instead of parsing text — and they are
   what closed both P0s.

9. **The tier-1 corollary's 26.362 s is a marginal cost, not a from-scratch one.** Its proof is the
   trivial instantiation of the general theorem, which cost 130.6 s and $0.00043 to prove. Any
   comparison quoting 26 s without the general proof is quoting a plausible number in place of the real
   one — the same error class as the hard-coded theorem name. The honest pair is **~157 s and ~$0.00058**
   against Route A *at its best configuration*: **837.9 s and $0.04655** with eight workers, on an
   identical state count. Both ratios move with the configuration and the billing model — the
   single-worker TLC row (6,748.6 s, $0.37492) is a valid datum and not the comparison, and the harness
   charges compute per wall-clock hour rather than per vCPU-hour.

## Provenance

| Number | Where it comes from |
|---|---|
| Route A, N=23 | `results/tlc.jsonl` — `task=token-ring, param_N=23, tier=1`, log `results/logs/token-ring-20260925T184838-r1.log` |
| Route A, N=3 (5 runs) and the mutant | `results/tlc.jsonl`, `param_N=3` |
| Route B, tier 2 | `results/proof.jsonl` — `mode=file, task=token-ring, tier=2, outcome=closed`; closure object carries the axioms, the pristine digest `e1d65f1a…` and `rounds: 1` |
| The closed proof | artifact `proofs/lean/token-ring/.runs/TokenRing-r1.lean` (7,387 bytes, 172 lines; the proof is 70 of them), sha256 `9c992250…` |
| The loop's session | `results/omp/TokenRing-20260926T101642-r1/` (plan/refutation/file transcripts) |
| Human prior art | `results/human.jsonl`, quotes sourced to `docs/protocol.md` §1a |
| The reference proof | `proofs/lean/token-ring/reference/HostReference.lean`; fixtures beside it |
| The audit | `docs/equivalence-token-ring.md`, pinned by `tests/test_equivalence_token_ring.py` |
