# Can an AI proof loop replace model checking?

**Gavin Mendel-Gleason and Maren Roos**

*A measured comparison of TLC against machine-closed Lean proofs on concurrent-system
verification, with wall-clock and dollar costs.*

---

## Abstract

Model checking a TLA+ specification with TLC is push-button and exhaustive, but only over a *bounded*
instance: it answers "no violation up to N". A proof answers "for all N", and until recently the cost of
getting one was human-weeks. We asked whether an AI proof loop — a model driving Lean 4 through a shell
until a closure oracle accepts the artifact — can close that gap, and what it costs.

Across four concurrent algorithms (token-ring mutual exclusion, Lamport's Bakery, LCR leader election,
and EWD998 termination detection) the loop closed every task's general theorem, each with a negative
control proving the rig detects a weakened model. **The headline claim is supported on 4 of 4 tasks: the
loop proves the general theorem inside a 2 h / $50 budget, by a margin of two to three orders of
magnitude, where TLC cannot answer at any budget.** The same-claim cost comparison is 2–2 and turns on
where each instance falls relative to its own crossover, not on the methods: TLC is faster on two tasks,
the loop on two, and cost totals favour the loop on three of four. Every closure cost under a millicent,
and every proof total — general theorem plus corollary — under 1.5 millidollars.

We report the method, the four tasks, the measured matrix, and — at length — what the result does not
establish.

## 1. The question

TLC decides a bounded instance by enumeration. That is the right tool for a design under development,
and its limitation is structural rather than a matter of speed: it cannot prove an invariance for
arbitrary `N`, and its cost grows exponentially in the instance. Theorem provers answer the general
question, but the published human effort is substantial — the TLA+ Trifecta paper (ISoLA 2022) reports
**one person-day** for an invariance proof of EWD998, and the IJCAR 2010 TLAPS papers report proof-line
counts in the hundreds with no time figure at all.

Three developments make the question worth asking now: reasoning models that can plan proof steps, Lean 4
with Mathlib as a target whose kernel is small and whose libraries are broad, and — the part we
emphasise — the ability to *verify* a candidate proof mechanically rather than trust the model that
produced it.

So: **can a loop close general theorems for concurrent systems, at what wall-clock and dollar cost, and
how does that compare with what TLC costs on the same claim?**

## 2. Method

### 2.1 Two routes, two tiers

**Route A** is TLC 2.19 enumerating a TLA+ specification at a bounded instance. **Route B** is a Lean 4
theorem closed by an AI proof loop.

Each task has two Route B tiers. **Tier 2** is the general theorem: the property for arbitrary `N`.
**Tier 1** is that theorem's corollary, instantiated at the calibrated instance `N₀`. Only tier 1 is
comparable with Route A, because only tier 1 proves the same claim.

`N₀` is fixed by a stated rule: **the largest `N` whose TLC run completes inside the 2 h per-run cap.**
That definition matters later.

### 2.2 The closure criterion

A "closed" verdict comes from three checks run by code the candidate cannot reach:

1. **Integrity** — the candidate is byte-identical to the seed up to and including the theorem's `:=`.
   This pins every definition and the statement; only the proof body is free.
2. **Elaboration** — the candidate is handed to `lean` directly, with no `lake` in the invocation. The
   candidate has a shell and can reach the package's lakefile, so a lake-built environment would be
   *the candidate's*, not the harness's.
3. **Closure** — a prebuilt checker imports the elaborated olean and reads the declaration's axiom set
   out of Lean's **API**, against `{propext, Classical.choice, Quot.sound}`.

The third is load-bearing and its implementation matters. `#print axioms` is *syntax*, syntax is an
environment extension a candidate can install, and it crosses imports — in testing, a candidate rewrote
the command into text of its own and the real report never ran. An API query cannot be reached that way.

Around those three: the bytes checked are one immutable snapshot taken once per round and never
re-read, so the verdict, the row digest and the durable closure copy all derive from the same bytes; the
elaboration environment is captured before the session opens; the seed's digest is re-checked on every
exit path.

### 2.3 Why a rate, not a run

Closure is stochastic. The unit of evidence is therefore a **cell** of R ≥ 5 runs sharing one seed
digest, never pooled across configurations. The complement is the **negative control**: the loop runs
against the task's *mutant* — a weakened model — and must *fail* to close it. Without that, a working
prover and a broken rig are indistinguishable.

### 2.4 Measurement

Wall-clock, peak RSS, dollar cost from provider usage at list price, and distinct states enumerated.
Route A runs at its best measured configuration with the row naming it, and worker count is reported
because it moves wall-clock and not state counts.

## 3. The task set

| Task | Property | Source |
|---|---|---|
| token-ring | mutual exclusion | our bootstrap model |
| Bakery | mutual exclusion | Lamport's algorithm |
| LCR | at most one leader | Le Lann–Chang–Roberts |
| EWD998 | termination detection, invariance | Dijkstra; imported with the ISoLA 2022 proofs |

EWD998 is the externally calibrated task: both the specification and the published TLAPS proofs are
imported at pinned provenance, and the human-effort figures attach to it.

## 4. Results

### 4.1 The matrix

| | **token-ring** | **bakery** | **lcr** | **ewd998** |
|---|---|---|---|---|
| Route A `n₀` | 23 | 9 | 10 | 3 |
| Route A wall-clock | **837.9 s** (8 workers) | **4,847.7 s** | **2.7 s** | **36.4 s** |
| Route A cost | **$0.04655** | **$0.26932** | **$0.00015** | **$0.00202** |
| Route A distinct states | 289,406,976 | 238,803,200 | 177,147 | 1,520,618 |
| **tier 2** (general `N`) | **closed** 104.8 s | **closed** 444.4 s | **closed** 216.0 s | **closed** 1009.5 s |
| tier-2 cost | $0.00033 | $0.00062 | $0.00044 | $0.00081 |
| **tier 1** (corollary) | **closed** 38.5 s | **closed** 76.6 s | **closed** 101.0 s | **closed** 101.2 s |
| tier-1 cost | $0.00023 | $0.00048 | $0.00042 | $0.00062 |
| **negative control** | TLC `violation` | `fail_to_close` | `fail_to_close` | `fail_to_close` |

tier 2 figures are cell medians (n = 6, 5, 5, 1 respectively); ranges are wide — token-ring's spans
62.9–1021.8 s — so no figure is quoted without its range.

### 4.2 Same-claim cost, counted honestly

A corollary is the trivial instantiation of its theorem, so the corollary's cost alone answers "what
does instantiation cost given the theorem". The question asked is what *settling the claim* costs, which
is theorem plus corollary:

| Task | Route A | theorem | corollary | **proof total** | **`K`** | favours |
|---|---|---|---|---|---|---|
| token-ring (N=23) | 837.938 s | 104.8 s | 38.5 s | **143.4 s** | **0.171** | proof, 5.8× |
| bakery (N=9) | 4,847.749 s | 444.4 s | 76.6 s | **521.0 s** | **0.107** | proof, 9.3× |
| ewd998 (N=3) | 36.4 s | 1009.5 s | 101.2 s | **1,110.8 s** | **30.5** | **TLC, 30.5×** |
| lcr (N=10) | 2.670 s | 216.0 s | 101.0 s | **317.0 s** | **118.7** | **TLC, 118.7×** |

`K` = proof ÷ TLC. **The split is 2–2.** On cost the totals are kinder to the proof — cheaper on three
of four; only lcr favours TLC on both resources.

### 4.3 Against published human effort

| Our task | Human comparator | Reported |
|---|---|---|
| `ewd998` | TLAPS invariance | **1 person-day**, ~230 lines |
| `ewd998` | TLAPS safety + refinement | **0.5 person-day**, ~110 lines |
| `ewd998` | TLAPS liveness | **< 1 person-day**, 245 lines |
| `ijcar2010-*` | TLAPS proofs | lines only — **no time reported** |
| token-ring, bakery, lcr | **none published** | — |

Only EWD998 has a published person-day figure, so the human comparison is one number against one
number: a person-day against **143–1111 seconds** of loop time and **under 1.5 millidollars**. The
IJCAR papers report lines and we do not convert lines into days.

### 4.4 The verdict, against each reading of "replacement"

| Reading | Result |
|---|---|
| **The general theorem inside budget `B`** | **Supported, 4 of 4.** Worst case 1009.5 s = **14.0%** of the 2 h cap and $0.00081 = **0.0016%** of the $50 cap. TLC's coverage of this tier is 0 of 4 at any budget. |
| **Cost parity at the bounded tier (`K`)** | **2–2**, `K` = 0.171 / 0.107 / 30.5 / 118.7. |
| **Coverage under a fixed budget** | Counts equal at 4 of 4, claims not equal: the loop settles four *general* theorems, TLC settles four *bounded* instances and zero of the general tier. |

## 5. What we learned that we did not set out to learn

**A harness flag cost us a wrong calibration, and the way we found it is the more useful result.**

EWD998's instance search kept failing at N=4–6 while other tasks completed at far larger state counts.
We formed four hypotheses and three died on evidence:

- *The failure is deterministic.* False: the two N=4 attempts died at **43,634,504** and **75,753,775**
  distinct states — different counts.
- *Our flag is the whole cause.* Half-true, and the surviving half mattered: every failing invocation
  carried TLC's `-cleanup`, which deletes the state pool mid-enumeration. Without it **N=4 completes** —
  248,006,200 distinct states, depth 104, 2 h 36 min, exit 0 — where the flagged runs died. But bakery
  completed at 238,803,200 states and token-ring at 289,406,976 *with* the flag in place, so the flag is
  **necessary but not sufficient**: it kills this specification's runs and not others'.
- *A deep frontier breaks the disk queue.* False: bakery held **234,890,583** states on queue and ran to
  its cap without error.

The discipline that separated them is worth stating plainly: **the surviving hypothesis was the one
checked against the other tasks' logs before being believed.** The three that died were each asserted
from a single observation — one run compared against its own log, one failure mode generalised from one
task, one intuition about queue depth. In a measurement programme, a claim that has not been checked
against an independent arm is a hypothesis, not a result.

**And the calibration value did not change.** `n₀ = 3` stands — but for a different reason than it was
first set. The flag made it an artifact of our invocation; the 2 h cap makes it a property of the stated
rule, since N=4 needs 2 h 36 min. The number is the same and the ground is now sound. We report it that
way rather than as a confirmation.

**Rigour about our own tooling.** Our closure oracle — the thing that decides whether a file counts as
proved — had **two soundness holes found in a single day**, both by an independent reviewer rather than
by the loop, both now failing closed: one let a candidate print a fake axiom report; the other let a
candidate redefine `#print axioms` in its own syntax so the check never ran. Neither was visible to a
passing test suite. A verification loop is a piece of software, and it earns trust the same way the
proofs do.

## 6. Limitations

These bound the claims and we would rather state them than have them found.

1. **Different claims per row.** Route A's row proves a bounded instance; Route B's tier 2 proves
   arbitrary `N`. Only the same-claim pairs (§4.2) compare like with like.
2. **The equivalence is audited, not proved.** Lean model ≡ TLA+ semantics is a hand audit per task. A
   modelling slip would make the theorem true about the wrong thing.
3. **Model, not code.** Both routes prove properties of models; neither refines to an implementation.
4. **Safety only.** Liveness is out of scope. The published EWD998 figures split on exactly that line
   (1 person-day invariance, <1 person-day liveness).
5. **No pair was measured at a crossover.** Every `N₀` was chosen by the loop's budget, not by where the
   two routes trade places — which is *why* §4.2 splits. The cost shape ("TLC exponential, proof flat")
   is measured; the crossover is extrapolated.
6. **Small task set.** Four algorithms, eight settled cells. Not a sampled population.
7. **Different precision across tasks.** Three tasks have R ≥ 5 cells; EWD998's are single runs, so its
   figures are existence proofs. Since EWD998 anchors the human comparison, that matters.
8. **Stochastic costs.** Each row is one sample; verdicts are deterministic given an artifact, costs are
   distributions. Medians carry ranges for that reason.
9. **Cost basis.** Tokens at list price, compute at a stated host rate, researcher time not costed.
10. **Our own tooling is young** (§5).

## 7. Related work

The TLA+ Trifecta paper (Konnov, Kuppe, Merz; ISoLA 2022) supplies the human-effort baseline for TLAPS
that §4.3 cites, and reports machine figures for its own TLC runs. The IJCAR 2010 TLAPS papers
(Chaudhuri, Doligez, Lamport, Merz) provide the line-count comparators, with their second Paxos
refinement published as incomplete. On the AI side, DeepSeek-Prover-V2, Kimina-Prover and
Goedel-Prover-SFT report pass rates on mathematical benchmarks (miniF2F, PutnamBench, CombiBench),
and DafnyBench and the vericoding benchmark report on program verification. Those measure *can a model
prove this*, usually at pass@k with large k. This work measures something different: **what does a
closed theorem cost in wall-clock and dollars, against the model checker it would replace on the same
specification**, which to our knowledge has not been reported.

## 8. Reproducing this

Every figure recomputes from the committed rows. `nix develop -c pytest` runs 72 scenarios including the
oracle's three checks and both mutants; two short queries recompute §4.1's cell table and the Route A
rows from `results/proof.jsonl` and `results/tlc.jsonl`. The equivalence audits, the closure oracle and
its interference experiment are all in the repository.

## 9. Conclusion

An AI proof loop closes general theorems for real concurrent algorithms, at a cost of seconds to
seventeen minutes and under a millicent, inside a budget two to three orders of magnitude larger than
what it uses. **That answers a question TLC cannot be asked** — arbitrary `N` rather than a bounded
instance — and it does so with a mechanically checked artifact, not a generated one.

It does not make model checking obsolete. On the same bounded claim, TLC is faster on two of four tasks,
and it checks the specification's semantics directly rather than a ported model whose equivalence is a
hand audit. **The honest summary is that the two routes answer different questions at different costs,
the crossover between them is the quantity that matters, and no experiment yet measures it.** That is
the obvious next step: a task calibrated so both routes are under pressure at the same instance.

---

## Appendix: data provenance

| Figure | Source |
|---|---|
| Route A rows | `results/tlc.jsonl`, logs under `results/logs/` |
| Route B rows | `results/proof.jsonl`; closure copies under `results/closures/<task>/` |
| Human comparators | `results/human.jsonl`; quotes pinned in `docs/human-baseline.md` |
| Method and decisions | `docs/protocol.md` |
| Closure criterion | `harness/closure_oracle.py`, `tools/checker/PROVENANCE.md` |
| Equivalence audits | `docs/equivalence-{token-ring,bakery,lcr,ewd998}.md` |
| Full matrix | `wiki/comparison-matrix.md` |
| Narrative report | `wiki/closed-by-theorem.md` |
