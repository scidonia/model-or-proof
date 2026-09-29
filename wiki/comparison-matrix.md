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
| **Route B tier 2** (general `N`) | **closed**, n=6, median **104.8 s** | **closed**, n=5, median **444.4 s** | **closed**, n=5, median **216.0 s** | **closed**, n=5, median **162.0 s** |
| tier-2 cost median | **$0.00033** | **$0.00062** | **$0.00044** | **$0.00081** |
| tier-2 range | 62.9 – 1021.8 s | 79.7 – 610.1 s | 148.0 – 970.8 s | — |
| **Route B tier 1** (corollary at `n₀`) | **closed**, n=7, median **38.5 s** | **closed**, n=5, median **76.6 s** | **closed**, n=5, median **101.0 s** | **closed**, n=6, median **112.3 s** |
| tier-1 cost median | **$0.00023** | **$0.00048** | **$0.00042** | **$0.00062** |
| tier-1 range | 25.1 – 64.8 s | 64.7 – 88.4 s | 79.2 – 178.7 s | — |
| **Mutant control** | TLC `violation` (23 states, depth 5) | `no_progress` → `fail_to_close`, 273.2 s | `no_progress` → `fail_to_close`, 502.7 s † | `no_progress` → `fail_to_close`, 572.7 s † |
| **Human comparator** | **none published** | IJCAR 2010, 800 lines (no time) | **none published** | **1 person-day** (ISoLA 2022) |
| Equivalence audit | `docs/equivalence-token-ring.md` | `docs/equivalence-bakery.md` | `docs/equivalence-lcr.md` | `docs/equivalence-ewd998.md` |

**Read the tier-1 row as the comparable one.** Tier 2 answers a question Route A cannot ask, so it is not
a like-for-like cost comparison — §3 handles it separately.

† **Two mutant cells record an outcome, not a cost.** The `lcr` and `ewd998` mutation-arm attempts read
the positive arm's proof file while developing their refutation, so only their failure to close is
evidence — their wall-clock and dollar figures are not measurements of anything. The `bakery` mutant row
is unaffected. §7 caveat 13, evidence at `results/route-b-cell-reuse.md` §10.6.

**Route B's cost figures in this matrix are withdrawn as cost measurements (2026-09-28).** The four
tier-2 medians and the `bakery` and `lcr` tier-1 medians rest on rows whose transcripts show prior-proof
reuse, and the re-earned arms failed their own audit gate as well (§2, §7 caveat 14). The **closures**
those rows record stand — a closure is a verdict, not a cost sample — and `token-ring`'s tier-1 cell
(38.5 s) is clean.

---

### 2. The same-claim pairs — theorem plus instantiation

Both arms settle the same claim at the same instance. **The proof's true cost is the general theorem
*plus* its corollary**, since the corollary is the trivial instantiation of it. A corollary-only figure
answers "what does instantiation cost *given* the theorem", not "what does settling this claim cost" —
so the totals below were the honest comparison and the marginal ratios the footnote. **All of it is now
withdrawn as cost measurement, and kept here as what was computed:**

| Task | Route A at `n₀` | theorem | corollary | **proof total** | **`K` (total)** | favours |
|---|---|---|---|---|---|---|
| token-ring (N=23) | 837.938 s / $0.04655 | 104.8 s / $0.00033 | 38.5 s / $0.00023 | **143.4 s / $0.00056** | **0.171** / 0.012 | proof, **5.8×** |
| bakery (N=9) | 4,847.749 s / $0.26932 | 444.4 s / $0.00062 | 76.6 s / $0.00048 | **521.0 s / $0.00110** | **0.107** / 0.004 | proof, **9.3×** |
| ewd998 (N=3) | 36.4 s / $0.00202 | 162.0 s / $0.00047 | 112.3 s / $0.00051 | **274.3 s / $0.00098** | **7.53** / 0.485 | **TLC, 7.5×** |
| lcr (N=10) | 2.670 s / $0.00015 | 216.0 s / $0.00044 | 101.0 s / $0.00042 | **317.0 s / $0.00086** | **118.7** / 5.82 | **TLC, 118.7×** |

**These totals are withdrawn (2026-09-28).** Every tier-2 median, and the `bakery` and `lcr` tier-1 arms,
rest on rows with prior-proof reuse; the re-earned reruns failed their audit gate as well (§7 caveat 14;
`results/remediation/`, and `wiki/closed-by-theorem.md` §8–§9), so **no recomputed `K` is published and
no split is a result**. Route A's own rows are measured and unaffected, and the one same-claim ratio that
rests only on clean cells is `token-ring`'s marginal one — 837.938 s against the tier-1 corollary's 38.5 s.

**The reasoning the withdrawn figures once supported is kept as reasoning.** A corollary-only ratio
answers a different question from the one asked, because the theorem's cost is paid once before any
corollary exists — so corollary ÷ Route A's 0.046 / 0.016 / 2.78 / 37.8 overstated the proof's wall-clock
advantage and understated TLC's; and on cost the totals were kinder to the proof than on wall-clock (three
of four favouring it, only lcr's not, on both resources). That is an argument about *what to count*, and
it survives; the numbers made with it do not.

**And the direction was never a property of the method.** `n₀` is chosen to fit the loop's budget, not to
sit at the task's crossover, and **no pair in this matrix was measured at a crossover** — so the pairs
reported where each instance happened to fall. **The shape survives — TLC exponential, proof flat, a
crossover per task; the 2–2 split does not.**

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

**Cells.** A cell is R ≥ 5 runs sharing one seed digest. All eight are now at R ≥ 5, across four tasks.

| Task | tier | n | median | min | max | cost median | turns |
|---|---|---|---|---|---|---|---|
| token-ring | 2 | 6 | 104.8 s | 62.9 s | **1021.8 s** | $0.00033 | 1 (one run: 12) |
| token-ring | 1 | 7 | 38.5 s | 25.1 s | 64.8 s | $0.00023 | 1 |
| bakery | 2 | 5 | 444.4 s | 79.7 s | 610.1 s | $0.00062 | 1 |
| bakery | 1 | 5 | 76.6 s | 64.7 s | 88.4 s | $0.00048 | 1 |
| lcr | 2 | 5 | 216.0 s | 148.0 s | 970.8 s | $0.00044 | 1 |
| lcr | 1 | 5 | 101.0 s | 79.2 s | 178.7 s | $0.00042 | 1 |
| ewd998 | 2 | 5 | 162.0 s | 69.0 s | 1009.5 s | $0.00047 | 1 |
| ewd998 | 1 | 1 | 101.2 s | — | — | $0.00062 | 1 |

**Withdrawn as cost measurements (2026-09-28):** the four tier-2 rows and the `bakery` and `lcr` tier-1
rows — the same six arms as §1. Their `n`, medians, minima, maxima and cost medians are historical
observations, not independent samples. The `token-ring` and `ewd998` tier-1 rows are unaffected, and
every row's *outcome* — closed or not — stands.

**Non-closures, all retained.** Three harness `error` rows (token-ring tier 1 at 416.2 s; bakery tier 2
at 361.5 s ×2, zero turns — the rig, not the prover) and three mutant `no_progress` rows.

**Negative controls.** The loop is run on the task's mutant and must **fail** to close the weakened model.

| Task | outcome | wall-clock | cost | turns | evidence |
|---|---|---|---|---|---|
| bakery | `no_progress` → `fail_to_close` | 273.2 s | $0.00474 | 6 | weakened `Enter` guard never closed |
| lcr † | `no_progress` → `fail_to_close` | 502.7 s | $0.00558 | 6 | weakened `ElectSelf` never closed |
| ewd998 † | `no_progress` → `fail_to_close` | 572.7 s | $0.01077 | 6 | axioms still contain `sorryAx`; `no_progress_rounds=5` |

**† Two of these rows are quarantined: the outcome stands, the figures do not.** Rows 70 (`lcr`) and 88
(`ewd998`) read the positive arm's proof file through **bare relative filenames** — `cat LCR-r1.lean`,
`cat EWD998-r1.lean` — while developing their refutation, so neither attempt was isolated or independent.
The wall-clock, dollar and round figures in those two rows are therefore **not independent sample
statistics**: they must not be averaged, compared or quoted as rates, and must not be used to validate the
checker. The **outcome** evidence does stand: `no_progress` → `fail_to_close` is sound because the mutant
is a *false* statement, and reading a proof of the *true* theorem cannot make it closable — which is why
the rows are **retained and quarantined, never deleted**. The bakery row (65) is unaffected. Full caveat:
§7 caveat 13; the commands and transcript lines: `results/route-b-cell-reuse.md` §10.6. This is a separate
matter from the published-cell remediation and from the replaced boundary watch, which concern the
positive cells and do not repair these two.

**Mutants cost more than the proofs they control** — bakery's $0.00474 against $0.00062, the one of these
three rows whose figures are not quarantined; the 4–10 millidollar range this paragraph used to quote is
withdrawn with the two rows above — because they pay for repeated refusals before `no_progress` ends them.
Those rounds are the evidence the detector was needed.

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
| **1** | Route B settles the tier-1 question within a factor `K` of Route A | **Withdrawn**: the cell medians behind `K` rest on rows with prior-proof reuse, and the re-earned reruns failed their audit gate (§2, §7 caveat 14), so **no split is reported**. The `0.171 / 0.107 / 7.53 / 118.7` totals this row used to print — with a `30.5` variant for EWD998 — are the §2 table's, and are withdrawn with it. |
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
10. **No pair was measured at a crossover**, which is why the four pairs fell where they did — a split now
    withdrawn with the cells behind it (caveat 14). The cost *shape* (TLC exponential, proof flat) is
    measured; the crossover itself is extrapolated.
11. **One calibration number rests on a scratch log, not a row** — EWD998's N=4 completion. A record
    sweep through the runner is in flight so the evidence becomes a row.
12. **Fingerprint-collision caveat** on the 248 M-state N=4 count: TLC reported `7.0E-8` actual against an
    optimistic `0.033`.
13. **Two mutation-arm rows are quarantined: usable as outcomes, never as costs.** Rows 70 (`lcr`, session
    `LCRMutant-mutant-20260926T230410-r1`) and 88 (`ewd998`, session
    `EWD998Mutant-mutant-20260927T010250-r1`) read the positive arm's proof file through **bare relative
    filenames** (`cat LCR-r1.lean`, `cat EWD998-r1.lean`) while developing their refutation, so neither
    attempt was isolated or independent. Four consequences — none of which the published-cell remediation
    or the replaced boundary watch alters, since those concern the positive cells:

    - **Their outcome evidence stands.** The mutant is a *false* statement, so reading a proof of the
      *true* theorem cannot make it closable; the non-closure result is sound, and the rows are
      **retained and quarantined rather than deleted** to keep exactly that evidence.
    - **Their wall-clock and dollar figures are not independent sample statistics.** They must not be
      averaged, quoted as rates, or used to validate the checker. The §4 table's 4–10 millidollar range
      is withdrawn for that reason.
    - **They must not be rerun as cost arms.** The mutant's required control is a falsifiability
      *outcome*, not a median, and it is not part of `K`.
    - **A mutant row ever reporting `closure.verdict: true`** after copying a true proof would be a rig
      failure requiring separate action — never a cell to average. None has been observed.

    The commands, transcript paths and line numbers, and each session's own words, are in
    `results/route-b-cell-reuse.md` §10.6, a correction to that file's own §5; the rows themselves are
    `results/proof.jsonl` rows 70 and 88. The bakery mutation arm (row 65) is unaffected.

14. **The cross-task cost figures are withdrawn.** The published tier-2 medians for all four tasks, and
    the `bakery` and `lcr` tier-1 arms, rest on rows whose transcripts show prior-proof reuse; the six
    affected arms were re-earned under per-package isolation and failed their audit gate as well —
    **only `tok2` is whole-clean**, the clean subsets across the six arms come to **nineteen attempts, of
    which fifteen closed**, and the raw **twenty-six of thirty closed** must never be quoted as
    comparable to that, because contamination *flatters* closure. So no recomputed `K` exists and §2
    reports none; its table retains the superseded values only as historical observations, and reading 1
    of §6 reports no split. The mutation-arm rows (caveat 13) are a separate matter — usable as
    **outcomes**, never as **cost statistics**. Evidence: `results/remediation/` (per-arm
    `audit.json`/`audit.txt`, `PROVENANCE.md`, `prepare-receipts.jsonl`, `revision.json`); the original
    reuse finding is `results/route-b-cell-reuse.md` §10.4–§10.8; the narrative is
    `wiki/closed-by-theorem.md` §8–§9. Comparisons against the superseded published values are
    **indicative**, because those rows predate the field that records a withheld verdict and were produced
    under a different verdict rule.

---

## 8. Reproducing any figure here

Every number above is recomputable from the committed rows. Commands assume the dev shell
(`nix develop -c …`), which pins TLC, pytest and the toolchain.

**The whole suite** — 72 scenarios, including the closure oracle's three checks and both mutants:

```bash
nix develop -c pytest
```

**Every Route B cell, with n, median and range** — the query §4's table came from:

```bash
python3 -c "
import json, statistics as st
rows=[json.loads(l) for l in open('results/proof.jsonl') if json.loads(l).get('mode')=='file']
for t in ('token-ring','bakery','lcr','ewd998'):
    for tier in (2,1):
        rs=[r for r in rows if r['task']==t and r.get('tier')==tier and r.get('outcome')=='closed']
        w=sorted(r['wall_clock_s'] for r in rs)
        print(t, tier, len(rs), st.median(w), min(w), max(w))
"
```

**A Route A row's two faces** — the nested `tlc` object carries the counts, the top level the timing and
cost:

```bash
python3 -c "
import json
for r in (json.loads(l) for l in open('results/tlc.jsonl')):
    if r.get('task')=='bakery' and r.get('param_N')==9:
        print(r['outcome'], r['wall_clock_s'], r['states_reached'], r['tlc'])
"
```

**The closure criterion itself**, for a reviewer who would rather test the oracle than trust it:
`harness/closure_oracle.py` implements the three checks and `tools/checker/PROVENANCE.md` records the
interference experiment that forced the axiom query to read Lean's API instead of parsing
`#print axioms`.

**What the repository cannot reproduce: the model's stochastic side.** Each Route B row is one sample,
so re-running a cell yields different times and token counts. The *verdicts* are reproducible — the
oracle is deterministic given the artifact — but the *costs* are distributions, which is why medians are
quoted with ranges and why no figure here is a single run's.

## 9. Provenance

| Figure | Source |
|---|---|
| Every Route A row | `results/tlc.jsonl`, logs under `results/logs/` |
| Every Route B row | `results/proof.jsonl` (88 rows: 41 file-mode, 47 tactic battery), closure copies under `results/closures/<task>/` |
| The mutation-arm caveat (§7.13) | `results/route-b-cell-reuse.md` §10.6 — the two affected transcripts with their commands, paths and line numbers; the rows are `results/proof.jsonl` rows 70 and 88 |
| Human comparators | `results/human.jsonl` (4 records), quotes pinned in `docs/human-baseline.md` |
| `n₀` definitions and budgets | `docs/protocol.md` §11 decisions 1–5, §3 |
| The closure criterion | `harness/closure_oracle.py`, `tools/checker/PROVENANCE.md` |
| Equivalence audits | `docs/equivalence-{token-ring,bakery,lcr,ewd998}.md` |
| The original reuse finding | `results/route-b-cell-reuse.md` §10.4–§10.8 — the six contaminated arms and their fifteen rows |
| The withdrawal and the rig result (§2, §6, §7.14) | `results/remediation/PROVENANCE.md`; per-arm `results/remediation/<arm>/audit.json` and `audit.txt`; `results/remediation/prepare-receipts.jsonl`; `results/remediation/revision.json`; narrative in `wiki/closed-by-theorem.md` §8–§9 |
| Narrative | `wiki/closed-by-theorem.md`, `wiki/token-ring-route-a-vs-route-b.md` |
