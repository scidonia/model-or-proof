# model-or-proof — full comparison matrix

**Audience:** a reviewing agent. Every figure is a measured row or a cited datum, both named in
*Provenance*. Nothing is estimated. Where a figure is a median, the sample size and range are given.

**Question the matrix answers:** can theorem proving, closed by an AI loop, replace TLC model checking
for concurrent-system verification — and at what wall-clock and dollar differential.

**Two routes, two tiers.**

- **Route A** — TLC 2.19 enumerating a TLA+ specification at a bounded instance `N₀`.
- **Route B** — a Lean 4 theorem closed by an AI proof loop in *file mode* (the prover receives the seed
  plus a shell). Verdict from three checks the candidate cannot reach: byte-identity with the seed up to
  the theorem's `:=`, elaboration without `lake`, and an axiom set (read from Lean's API) contained in
  `{propext, Classical.choice, Quot.sound}`.
- **Tier 2** is the general theorem, arbitrary `N`. **Tier 1** is its corollary, the theorem instantiated
  at `N₀` — the only tier comparable to Route A's bounded instance.
- **`n₀`** is defined by protocol §11 decision 3: the largest `N` whose TLC run completes inside the 2 h
  per-run cap.

---

## 1. The matrix — one row per task

| | **token-ring** | **bakery** | **lcr** | **ewd998** |
|---|---|---|---|---|
| **Property** | `Mutex` | `MutualExclusion` | at most one leader | invariance |
| **Route A `n₀`** | 23 | 9 | 10 | 3 |
| Route A wall-clock at `n₀` | **837.938 s** (8 workers) | **4,847.749 s** | **2.670 s** | **36.4 s** (median of 6) |
| Route A cost at `n₀` | **$0.04655** | **$0.26932** | **$0.00015** | **$0.00203** |
| Route A distinct states | 289,406,976 | 238,803,200 | 177,147 | 1,520,618 |
| **Route B tier 2** (general `N`) | **closed**, n=6, median **104.8 s** | **closed**, n=5, median **444.4 s** | **closed**, n=5, median **216.0 s** | **closed**, n=1, **1009.5 s** |
| tier-2 cost median | **$0.00033** | **$0.00062** | **$0.00044** | **$0.00081** |
| tier-2 range | 62.9 – 1021.8 s | 79.7 – 610.1 s | 148.0 – 970.8 s | — |
| **Route B tier 1** (corollary at `n₀`) | **closed**, n=7, median **38.5 s** | **closed**, n=5, median **76.6 s** | **closed**, n=5, median **101.0 s** | **closed**, n=1, **101.2 s** |
| tier-1 cost median | **$0.00023** | **$0.00048** | **$0.00042** | **$0.00062** |
| tier-1 range | 25.1 – 64.8 s | 64.7 – 88.4 s | 79.2 – 178.7 s | — |
| **Mutant control** | TLC `violation` (23 states, depth 5) | `no_progress` → `fail_to_close`, 273.2 s | `no_progress` → `fail_to_close`, 502.7 s | `no_progress` → `fail_to_close`, 572.7 s |
| **Human comparator** | **none published** | IJCAR 2010, 800 lines (no time) | **none published** | **1 person-day** (ISoLA 2022) |
| Equivalence audit | `docs/equivalence-token-ring.md` | `docs/equivalence-bakery.md` | `docs/equivalence-lcr.md` | `docs/equivalence-ewd998.md` |

**Read the tier-1 row as the comparable one.** Tier 2 answers a question Route A cannot ask, so it is not
a like-for-like cost comparison — §3 handles it separately.

---

## 2. The same-claim pairs — theorem plus instantiation

Both arms settle the same claim at the same instance. **The proof's true cost is the general theorem
*plus* its corollary**, since the corollary is the trivial instantiation of it. A corollary-only figure
answers "what does instantiation cost *given* the theorem", not "what does settling this claim cost" —
so the totals below are the honest comparison and the marginal ratios are the footnote.

| Task | Route A at `n₀` | theorem | corollary | **proof total** | **`K` (total)** | favours |
|---|---|---|---|---|---|---|
| token-ring (N=23) | 837.938 s / $0.04655 | 104.8 s / $0.00033 | 38.5 s / $0.00023 | **143.4 s / $0.00056** | **0.171** / 0.012 | proof, **5.8×** |
| bakery (N=9) | 4,847.749 s / $0.26932 | 444.4 s / $0.00062 | 76.6 s / $0.00048 | **521.0 s / $0.00110** | **0.107** / 0.004 | proof, **9.3×** |
| ewd998 (N=3) | 36.4 s / $0.00202 | 1009.5 s / $0.00081 | 101.2 s / $0.00062 | **1,110.8 s / $0.00143** | **30.5** / 0.709 | **TLC, 30.5×** |
| lcr (N=10) | 2.670 s / $0.00015 | 216.0 s / $0.00044 | 101.0 s / $0.00042 | **317.0 s / $0.00086** | **118.7** / 5.82 | **TLC, 118.7×** |

**Marginal ratios, for reference — and they mislead in both directions.** Corollary ÷ Route A gives
0.046 / 0.016 / 2.78 / 37.8, which **overstates** the proof's wall-clock advantage (21.7× → 5.8× at
token-ring, 63.3× → 9.3× at bakery) and **understates** TLC's (2.78× → 30.5× at EWD998, 37.8× → 118.7×
at lcr). The theorem is reusable across every instance of its claim, so its cost must be paid once
before any corollary exists.

**On wall-clock the totals split 2–2. On cost, three of four favour the proof** (only lcr's does not,
and it favours TLC on both resources).

**The disagreement is the finding, not a defect.** `n₀` is chosen to fit the loop's budget, not to sit at
the task's crossover, and **no pair in this matrix was measured at a crossover** — so the ratios report
where each instance happened to fall.

---

## 3. Route A calibration curves (all rows, `results/tlc.jsonl`)

| Task | instance | outcome | wall-clock | cost | distinct states | workers |
|---|---|---|---|---|---|---|
| token-ring | N=3 | success ×5 | 0.656 – 0.669 s | $0.00004 | 36 | 1 |
| token-ring | N=3 | **violation** (mutant) | 0.666 s | $0.00004 | 23 | 1 |
| token-ring | N=17 | success | 33.302 s | $0.00185 | 3,342,336 | 1 |
| token-ring | N=17 | success | **8.041 s** | $0.00045 | 3,342,336 | **8** |
| token-ring | N=23 | success | 6,748.604 s | $0.37492 | 289,406,976 | 1 |
| token-ring | N=23 | success | **837.938 s** | $0.04655 | 289,406,976 | **8** |
| bakery | N=3 | success | 0.667 s | $0.00004 | 164 | 1 |
| bakery | N=4 | success | 0.716 s | $0.00004 | 1,280 | 1 |
| bakery | N=5 | success | 0.916 s | $0.00005 | 11,472 | 1 |
| bakery | N=6 | success | 2.360 s | $0.00013 | 117,088 | 1 |
| bakery | N=7 | success | 19.866 s | $0.00110 | 1,343,008 | 1 |
| bakery | N=8 | success | 283.799 s | $0.01577 | 17,092,608 | 1 |
| bakery | N=9 | success | 4,847.749 s | $0.26932 | 238,803,200 | 1 |
| bakery | N=10 | **timeout** (cap) | 7,200.307 s | $0.40002 | 421,840,058 | 1 |
| lcr | N=3 – N=10 | success ×8 | 0.666 – 2.670 s | $0.00004 – $0.00015 | 39 – 177,147 | 1 |
| lcr | N=3 | **violation** (mutant) | 0.666 s | $0.00004 | 23 | 1 |
| ewd998 | N=3 | success ×6 | 35.484 – 44.249 s | $0.00197 – $0.00246 | 1,520,618 (all identical) | 1 |
| ewd998 | N=3 | **violation** (mutant) | 0.766 s | $0.00004 | 805 | 1 |
| ewd998-paper | N=3 | success | 32.130 s | $0.00178 | 1,384,582 | 1 |

**Two calibration facts worth carrying.**

- **`lcr`'s first eight rows are `error`, not measurements.** TLC resolved `Naturals` to a stale
  `/tmp/Naturals.tla` rather than the spec's own module and died in 0.26 s: `Parsing file
  /tmp/Naturals.tla` … `Error: Parsing or semantic analysis failed.` The eight successes that follow are
  the calibration. The rows are retained rather than deleted — they are what a mis-resolved search path
  looks like — and their `error` field is empty only because they predate the error-tail fix.
- **`ewd998`'s N=4 – N=6 `error` rows are harness-caused, and now explained.** All carried TLC's
  `-cleanup` flag, which deletes the state pool mid-enumeration. Without it N=4 **completes**: 248,006,200
  distinct states, depth 104, 2 h 36 min, exit 0. The flag's victims were ours. `n₀` remains 3 because
  2 h 36 min is outside the 2 h cap — the same number on sound ground.

---

## 4. Route B detail (`results/proof.jsonl`, file mode)

**Cells.** A cell is R ≥ 5 runs sharing one seed digest. `n=1` marks EWD998, which is an existence proof
rather than a distribution.

| Task | tier | n | median | min | max | cost median | turns |
|---|---|---|---|---|---|---|---|
| token-ring | 2 | 6 | 104.8 s | 62.9 s | **1021.8 s** | $0.00033 | 1 (one run: 12) |
| token-ring | 1 | 7 | 38.5 s | 25.1 s | 64.8 s | $0.00023 | 1 |
| bakery | 2 | 5 | 444.4 s | 79.7 s | 610.1 s | $0.00062 | 1 |
| bakery | 1 | 5 | 76.6 s | 64.7 s | 88.4 s | $0.00048 | 1 |
| lcr | 2 | 5 | 216.0 s | 148.0 s | 970.8 s | $0.00044 | 1 |
| lcr | 1 | 5 | 101.0 s | 79.2 s | 178.7 s | $0.00042 | 1 |
| ewd998 | 2 | 1 | 1009.5 s | — | — | $0.00081 | 1 |
| ewd998 | 1 | 1 | 101.2 s | — | — | $0.00062 | 1 |

**Non-closures, all retained.** Three harness `error` rows (token-ring tier 1 at 416.2 s; bakery tier 2
at 361.5 s ×2, zero turns — the rig, not the prover) and three mutant `no_progress` rows.

**Negative controls.** The loop is run on the task's mutant and must **fail** to close the weakened model.

| Task | outcome | wall-clock | cost | turns | evidence |
|---|---|---|---|---|---|
| bakery | `no_progress` → `fail_to_close` | 273.2 s | $0.00474 | 6 | weakened `Enter` guard never closed |
| lcr | `no_progress` → `fail_to_close` | 502.7 s | $0.00558 | 6 | weakened `ElectSelf` never closed |
| ewd998 | `no_progress` → `fail_to_close` | 572.7 s | $0.01077 | 6 | axioms still contain `sorryAx`; `no_progress_rounds=5` |

**Mutants cost more than the proofs they control** (4–10 millidollars against 0.3–0.8), because they pay
for repeated refusals before `no_progress` ends them. Those rounds are the evidence the detector was
needed.

**Tactic battery** (a separate configuration, never pooled with the above): 47 rows, 40 `success`,
4 `refuted`, 2 `timeout`, 1 `error` — the refutation arm, from the other direction.

---

## 5. Human comparators (cited data, never a measured arm)

Protocol §6a: `kind: "human_prior_art"`, `machine_checked: false`,
`never_pooled_with: [route_a_measured, route_b_measured]`. Every published comparator is **TLAPS**, the
TLA+ proof system.

| Source | Proof | Reports | Figure |
|---|---|---|---|
| ISoLA 2022 (EWD998) | invariance | **person-days** | **1 person-day**, ~230 lines |
| ISoLA 2022 (EWD998) | safety + refinement | **person-days** | **0.5 person-day**, ~110 lines |
| ISoLA 2022 (EWD998) | liveness | **person-days** | **< 1 person-day**, 245 lines |
| IJCAR 2010 | Peterson, mutual exclusion | lines only | ~130 lines |
| IJCAR 2010 | Bakery, mutual exclusion | lines only | 800 lines |
| IJCAR 2010 | Paxos, first refinement | lines only | 550 lines |
| IJCAR 2010 | Paxos, second refinement | lines only | "somewhat over 1000" — **incomplete** |

**Only EWD998 has a published person-day figure.** No line count is converted into days anywhere.
Published counts also disagree with the committed artifacts (Peterson "about 130" vs 199; Bakery "800"
vs 383; EWD998's 585 vs 863 + 123) and both are recorded rather than reconciled.

---

## 6. Verdict against the three readings of "replacement" (protocol §3)

Protocol §3 names three readings and §11 decision 1 makes **reading 2 the headline**.

| Reading | Statement | Result |
|---|---|---|
| **2 (headline)** | Route B proves the tier-2 theorem within budget `B`, where Route A cannot answer at any cost | **Supported, 4 of 4.** Worst case 1009.5 s = 14.0% of the 2 h cap and $0.00081 = 0.0016% of the $50 cap. Route A's coverage of tier 2 is 0 of 4 at any budget. |
| **1** | Route B settles the tier-1 question within a factor `K` of Route A | **Totals: `K` = 0.171 / 0.107 / 30.5 / 118.7** — two favour the proof (5.8×, 9.3×) and two favour TLC (30.5×, 118.7×). Corollary-only ratios (0.046 / 0.016 / 2.78 / 37.8) overstate the proof's advantage and understate TLC's, because the general theorem's cost must be paid before any corollary exists — see §2. |
| **3** | Coverage under a fixed budget | **Counts equal at 4 of 4, claims not equal.** Route B settles four general theorems; Route A settles four bounded instances and 0 of 4 at the general tier. |

---

## 7. Caveats a reviewer should carry

1. **Tier asymmetry.** Route A's row is a bounded instance; Route B's tier 2 is arbitrary `N`. Never pool
   the tiers — §2 uses tier 1 for that reason.
2. **The equivalence is audited, not proved.** Lean model ≡ TLA+ semantics is a hand audit per task. A
   modelling slip would make the theorem true about the wrong thing.
3. **Model, not code.** No refinement to an implementation on either route.
4. **Safety only.** Liveness is out of scope so far.
5. **`N ≥ 2`, not `N ≥ 1`** — a real if small loss of generality, the statement being human-authored.
6. **The closure oracle is days old and had two soundness holes found in one day**, both by an
   independent reviewer, both now failing closed. Route A's tool is 25 years old.
7. **Ranges are wide** — token-ring's tier-2 cell spans 62.9 – 1021.8 s — so no ratio is more than one
   sample per configuration. Medians are quoted with ranges for that reason.
8. **Cost basis.** Tokens at provider list price as recorded in the session's `usage.cost`; compute at a
   stated host rate; researcher time not costed. Components reported separately.
9. **EWD998's cells are `n=1`**, unlike every other task. Its figures are existence proofs, not rates.
10. **No pair was measured at a crossover**, which is why the four `K` values disagree. Paxos is the task
    ruled to fix that, with `n₀` set at the crossing.
11. **One calibration number rests on a scratch log, not a row** — EWD998's N=4 completion. A record
    sweep through the runner is in flight so the evidence becomes a row.
12. **Fingerprint-collision caveat** on the 248 M-state N=4 count: TLC reported `7.0E-8` actual against an
    optimistic `0.033`.

---

## Provenance

| Figure | Source |
|---|---|
| Every Route A row | `results/tlc.jsonl`, logs under `results/logs/` |
| Every Route B row | `results/proof.jsonl` (88 rows: 41 file-mode, 47 tactic battery), closure copies under `results/closures/<task>/` |
| Human comparators | `results/human.jsonl` (4 records), quotes pinned in `docs/human-baseline.md` |
| `n₀` definitions and budgets | `docs/protocol.md` §11 decisions 1–5, §3 |
| The closure criterion | `harness/closure_oracle.py`, `tools/checker/PROVENANCE.md` |
| Equivalence audits | `docs/equivalence-{token-ring,bakery,lcr,ewd998}.md` |
| Narrative | `wiki/closed-by-theorem.md`, `wiki/token-ring-route-a-vs-route-b.md` |
