# Closed by theorem

Every theorem this repository has closed with an AI proof loop, what it cost in wall-clock and
dollars, and how it compares with TLC and with published human work.

**Status:** results as of 2026-09-26 / 2026-09-27. Four tasks — `token-ring`, `bakery`, `lcr`,
`ewd998` — have closed their theorem, with `ewd998`'s calibration still held at `n₀ = 3` pending a
clean sweep, for the reason §7 gives (its `n₀` is an artifact of the harness's own invocation, not a
tool boundary). Every number below traces to a row or artifact named in *Provenance*.

**How a closure is established.** An AI proof loop runs in file mode: the prover receives the seed
plus a shell. A CLOSED verdict comes from three checks run by code the candidate cannot reach —
integrity (bytes identical to the seed up to the theorem's `:=`), elaboration (handed to `lean`
directly, no `lake` in the invocation), and closure (a prebuilt checker imports the elaborated olean
and reads the axiom set out of Lean's API against `{propext, Classical.choice, Quot.sound}`). Closure
is stochastic, so the unit of evidence is a cell of R ≥ 5 runs sharing one seed digest; rows from
different configurations are never pooled. See `wiki/token-ring-route-a-vs-route-b.md` §8.

---

## 1. What is closed, per cell

| Task | Tier | Claim | n | Wall-clock median | Range | Cost median | Range |
|---|---|---|---|---|---|---|---|
| **token-ring** | 2 | `Mutex` for **arbitrary N** | 6 | **104.8 s** | 62.9 – 1021.8 | **$0.00033** | $0.00029 – $0.02221 |
| **token-ring** | 1 | `Mutex` at N=23 (corollary) | 7 | **38.5 s** | 25.1 – 64.8 | **$0.00023** | $0.00014 – $0.00027 |
| **bakery** | 2 | `MutualExclusion` for **arbitrary N** | 5 | **444.4 s** | 79.7 – 610.1 | **$0.00062** | $0.00033 – $0.00076 |
| **bakery** | 1 | `MutualExclusion` at N=9 (corollary) | 5 | **76.6 s** | 64.7 – 88.4 | **$0.00048** | $0.00039 – $0.00068 |
| **lcr** | 2 | at most one leader, **arbitrary N** | 5 | **216.0 s** | 148.0 – 970.8 | **$0.00044** | $0.00034 – $0.00086 |
| **lcr** | 1 | leader uniqueness at N=10 (corollary) | 5 | **101.0 s** | 79.2 – 178.7 | **$0.00042** | $0.00038 – $0.00077 |
| **ewd998** | 2 | invariance for **arbitrary N** | 1 | **1009.5 s** | — | **$0.00081** | — |
| **ewd998** | 1 | invariance at N=3 (corollary) | 1 | **101.2 s** | — | **$0.00062** | — |

**`ewd998`'s cells are single runs, not yet rates.** The other three tasks have R ≥ 5 per cell; `ewd998`
has one closure each, so its two figures are existence proofs rather than distributions and are not
comparable in precision with the rows above. Its calibration is also held (§7), so its corollary may be
restated at a different `N₀` — its 101.2 s is at N=3, the value under revision.

**Tier 1 is a corollary**: the general theorem instantiated at the task's calibrated `N₀`. Its cost is
consistently a fraction of the theorem's — token-ring 2.7×, bakery 5.8×, lcr 2.1× cheaper in
wall-clock.

**Cost varies by problem.** The three theorem medians span 104.8 s to 444.4 s on theorems of
comparable shape, so no single figure is "the cost of a proof", and the variation appears between a
task's own two cells as well as across tasks.

**Thirty-three of thirty-eight file-mode rows closed.** The five that did not are the controls in §2
(two `no_progress` mutant rows) and three harness `error` rows — all recorded, none discarded.

## 2. Controls — why a closure counts

A working prover and a broken rig are indistinguishable without these. The negative control runs the
loop against the task's *mutant*: a weakened model it must **fail** to close.

| Task | Arm | Result | Wall-clock | Meaning |
|---|---|---|---|---|
| **bakery** | weakened `Enter` guard | `no_progress` → `fail_to_close` | 273.2 s | the loop never closed the false statement |
| **lcr** | weakened `ElectSelf` | `no_progress` → `fail_to_close` | 502.7 s | matches the TLA+ side's `UniqueLeader` violation at depth 3 |
| **ewd998** | weakened model | `no_progress` → `fail_to_close` | 572.7 s | the loop never closed the false statement |
| **token-ring** | mutant | TLC reports `violation` | 0.666 s | the TLA+ side refutes it (23 distinct states, depth 5) |
| **tactic battery** | false statements | 4 `refuted`, 40 `success`, 1 `timeout` | — | the refutation arm, approached from the other direction |

**The mutant can cost more than the proofs it controls** — bakery's $0.0047 against $0.00062 — because
it paid for six rounds of the same refusal before `no_progress` ended it. Those rounds *are* the
evidence that the detector was needed.

## 3. Against TLC — the same-claim pairs

This is the comparison the experiment exists for: TLC enumerating the *same* claim the loop proved, at
the loop's calibrated `N₀`. Both rows are measured, and the pair is a *marginal* comparison — see the
honest basis below.

| Task | Route A — TLC | Route B — the corollary | Marginal ratio |
|---|---|---|---|
| **token-ring** | N=23, 8 workers: **837.938 s**, **$0.04655**, 289,406,976 states | 38.5 s, $0.00023 | proof **21.7×** faster, **202×** cheaper |
| **bakery** | N=9, 1 worker: **4,847.749 s**, **$0.26932**, 238,803,200 states | 76.6 s, $0.000476 | proof **63.3×** faster, **565×** cheaper |
| **lcr** | N=10, 1 worker: **2.670 s**, **$0.00015**, 177,147 states | 101.0 s, $0.000421 | **TLC 37.8× faster and cheaper** |

**Fairness note on configuration.** Each route runs at its best configuration and the row names it.
token-ring's N=23 exists at both — **6,748.604 s single-worker** and **837.938 s at eight workers**,
scaling 8.05× on an identical state count. bakery's and lcr's pairs are single-worker rows; no
multi-worker analogue has been taken for them, and no figure here is inferred from another task's
scaling.

**The honest basis is not the marginal one.** A corollary's proof is the trivial instantiation of the
general theorem, which itself cost 104.8 s (token-ring), 444.4 s (bakery) and 216.0 s (lcr). So the
defensible figure is theorem *plus* instantiation:

| Task | Route B, honest total | Route A | Ratio |
|---|---|---|---|
| token-ring | **~143 s**, ~$0.00056 | 837.938 s, $0.04655 | **5.8×** faster, **84×** cheaper |
| bakery | **~521 s** | 4,847.749 s, $0.26932 | **9.3×** faster |

Quoting the corollary alone is the same error class as reporting an assumed value where an observation
was needed.

**The third pair goes the other way, and that is the finding.** lcr enumerates 177 *thousand* states at
N=10 where token-ring enumerates 289 *million* at N=23, so its crossover sits above the `N₀` its budget
allowed. `N₀` is chosen to fit the loop's budget, which is not the same as sitting near where the two
routes trade places. **"The proof beats model checking" is therefore not a property of the two methods**
— it is a property of where a task's instance falls relative to its own crossover, and one task in three
landed on the other side.

**What is true of the shape:** TLC's cost grows exponentially in the instance (token-ring 8.0 s at N=17
→ 837.9 s at N=23, eight workers), the proof's is flat, and the crossover is where they cross — near
N≈20 for token-ring, N≈8–9 for bakery, above N=10 for lcr.

## 4. Against human work — cited, never measured

The protocol makes human interactive proof engineering an explicit non-goal, so this column is
*published data*, `machine_checked: false`, `never_pooled_with: [route_a_measured, route_b_measured]`.
**Every published comparator is TLAPS**, the TLA+ proof system.

| Our task | Human comparator | Reported | Source |
|---|---|---|---|
| `ewd998` | invariance | **1 person-day**, ~230 lines | ISoLA 2022 |
| `ewd998` | safety + refinement | **0.5 person-day**, ~110 lines | ISoLA 2022 |
| `ewd998` | liveness | **< 1 person-day**, 245 lines | ISoLA 2022 |
| `ijcar2010-peterson` | mutual exclusion | ~130 lines — **no time reported** | IJCAR 2010 |
| `ijcar2010-bakery` | mutual exclusion | 800 lines — **no time reported** | IJCAR 2010 |
| `ijcar2010-paxos` | 1st / 2nd refinement | 550 / "somewhat over 1000" lines — **incomplete** | IJCAR 2010 |
| **`token-ring`, `bakery`, `lcr`** | **none published** | — | — |

**The only task with a published person-day figure is `ewd998`.** So the human comparison is one number
against one number: a hand invariance proof took **1 person-day**; the loop's closures run **38.5 s to
444.4 s** for $0.0002–$0.0006.

**Lines are never converted into days.** The IJCAR 2010 trio reports line counts only, and the
repository does not invent an exchange rate. Published line counts also disagree with the committed
artifacts — peterson "about 130" vs 199; bakery "800" vs 383; ewd998's 585 (230+110+245) vs 863 + 123 —
and both figures are recorded rather than reconciled (`docs/human-baseline.md`, asserted by
`tests/human-baseline-contract.md`).

For reference, the machine figure the ISoLA 2022 paper reports for its own TLC run: **1.3 M distinct
states, 42 s** at `N=3, K=C=3, Q=9` — a *machine* number, not a human one.

## 5. What the claim does not cover

1. **Different claims.** Route A's row proves a bounded instance; Route B's proves arbitrary `N`. The
   cost race is measured on the corollary, which instantiates the general theorem at that instance.
2. **The equivalence is audited, not proved.** Lean-model ≡ TLA+-semantics is a hand audit per task
   (`docs/equivalence-*.md`), pinned by tests. A modelling slip would make the theorem true about the
   wrong thing.
3. **Model, not code.** Both routes prove a property of a model. There is no refinement to an
   implementation on either side.
4. **Safety only.** `Mutex` / mutual exclusion / unique leader. Liveness is untouched — and that is
   where the published EWD998 figures split (1 person-day invariance, < 1 person-day liveness).
5. **`N ≥ 2`, not `N ≥ 1`**, a real if small loss of generality in the statement, which is the human's
   authorship choice.
6. **Our verification tooling is days old.** The closure oracle had **two soundness holes found in one
   day**, both by an independent reviewer rather than by the loop, both now failing closed: one let a
   candidate print a fake axiom report, the other let a candidate *redefine* `#print axioms` in its own
   syntax so the check never ran. What is compared is a 25-year-old push-button tool against a young
   one — and neither hole was visible to a passing test suite.
7. **Ranges are wide** — token-ring's theorem cell runs 62.9–1021.8 s — so medians are quoted with
   ranges and no ratio here is more than one sample of each configuration.
8. **Peak memory**: the proof side loads Mathlib (~9 GB RSS); TLC's peak on the N=23 row was 8,724 MB.

## 6. The cost shape, stated once

> **TLC's cost grows exponentially in the instance and the proof's is flat; the crossover is where
> they trade places.** The proof does not uniformly beat model checking — it answers a strictly
> stronger question ("for all N") at a lower *marginal* cost, and only wins in wall-clock past a
> crossover that moves with TLC's configuration and the task's own state curve.

Turning that shape into a number needs a pair measured *at* a crossover, which no task here has yet:
every `N₀` was set by the loop's budget. That is a gap in the task set, not in the measurement.

## 7. Pending

**`ewd998`'s theorem and corollary have closed** — 1009.5 s and 101.2 s. What remains is its
**calibration**, which is *held* rather than set: the value `n₀ = 3` is an artifact of the harness's
own TLC invocation. `-cleanup` deletes the state pool mid-enumeration, uniquely on this task — the flag
is **necessary but not sufficient**, since bakery completed at 238,803,200 states and token-ring at
289,406,976 *with* the flag, while without it `ewd998`'s N=5 passes 16× the count at which it died with
the flag. The fix is landed and verified — the flag dropped, the per-run metadir removed from Python in
a `finally` — and two clean runs are in flight at N=4 and N=5. When a clean sweep lands, the
`N₀`-dependent artifacts (the corollary's statement, its baseline, the manifest, the audit) are revisited
in one pass; `ewd998`'s corollary figure in §1 is provisional in a way the other three are not.

All four file-mode fixes the review's cluster produced have landed: the TLC `error` tail, per-run
`metadir` isolation, the closure copy, and the in-progress copy.

**The measurement the task set still lacks** is a pair taken *at* a crossover (§6). Every `N₀` so far was
chosen to fit the loop's budget, so no task has an arm on each side of where the two routes trade places
— which is why the three measured pairs split: two favour the proof, one favours TLC. Turning the cost
shape into a number needs a task calibrated to cross its own crossover.

## Provenance

| Number | Where it comes from |
|---|---|
| Closures, per cell | `results/proof.jsonl` — `mode=file, outcome=closed`, grouped by `task` and `tier`; each cell shares one seed digest |
| Negative controls | `results/proof.jsonl` — `mutant=true, outcome=no_progress` |
| Tactic battery | `results/proof.jsonl` — `task=battery` (45 rows) |
| Route A, token-ring N=23 | `results/tlc.jsonl` — `task=token-ring, param_N=23`: 837.938 s / $0.04655 / 289,406,976 distinct at `workers=8`; 6,748.604 s / $0.37492 at `workers=1` |
| Route A, bakery N=9 | `results/tlc.jsonl` — `task=bakery, param_N=9`: 4,847.749 s / $0.26932 / 238,803,200 distinct, `workers=1` |
| Route A, lcr N=10 | `results/tlc.jsonl` — `task=lcr, param_N=10`: 2.670 s / $0.00015 / 177,147 distinct |
| Route A, token-ring N=3 | `results/tlc.jsonl` — 5 runs, 0.656–0.669 s, 36 distinct; the mutant `violation` at 23 distinct |
| EWD998 (Route B) | `results/proof.jsonl` — `task=ewd998, mode=file`: tier 2 `closed` 1009.538 s / $0.000814, tier 1 `closed` 101.217 s / $0.00062086, tier 2 `mutant=true` `no_progress` 572.665 s |
| Human prior art | `results/human.jsonl` — quotes and pinned sources; `machine_checked: false` throughout |
| The equivalence audits | `docs/equivalence-token-ring.md`, `docs/equivalence-bakery.md`, `docs/equivalence-lcr.md`, `docs/equivalence-ewd998.md` |
| The closure check | `harness/closure_oracle.py` and `tools/checker/` (whose `PROVENANCE.md` records the interference experiment) |
| The full narrative | `wiki/token-ring-route-a-vs-route-b.md`, §1–§10 |
