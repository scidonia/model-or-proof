# Published-cell remediation — provenance

The user chose **option A**: quarantine the transcript-contaminated cells and re-earn the comparison.
`results/route-b-cell-reuse.md` §10.4–§10.8 fixes the scope at **six contaminated arms and fifteen rows**
— token-ring tier-2 (48, 59, 60, 62), bakery tier-2 (68), lcr tier-2 (77, 78, 79), ewd998 tier-2 (94, 95,
96, 97), bakery tier-1 (83), lcr tier-1 (74, 76) — while the twenty-one tier-1 rows that only import a
task's own general `*Proved` theorem stay **intended dependency** and are not rerun. The contaminated rows
are preserved in `results/proof.jsonl` as historical observations and are never pooled with these.

## What was run

Each arm is its own cell, re-earned at the **headline** configuration it replaces: default `--arms`
(`proof+refutation`), `--mode file`, **one repetition per invocation**, unchanged budgets of 7200 s / $50,
and **no `--exploratory`** — the flag marks a setup that is not the headline one, so passing it on a
replacement for a published cell would mislabel it.

| arm | task manifest | seed | tier | `--param-N` | attempts |
| --- | --- | --- | --- | --- | --- |
| `tok2` | `tasks/token-ring.json` | `TokenRing.lean` | 2 | — | 5 |
| `bak2` | `tasks/bakery.json` | `Bakery.lean` | 2 | — | 5 |
| `lcr2` | `tasks/lcr.json` | `LCR.lean` | 2 | — | 5 |
| `ewd2` | `tasks/ewd998.json` | `EWD998.lean` | 2 | — | 5 |
| `bak1` | `tasks/bakery.json` | `BakeryN0.lean` | 1 | `9` | 5 |
| `lcr1` | `tasks/lcr.json` | `LCRN0.lean` | 1 | `10` | 5 |

**Thirty attempts, each in its own prepared package.** Every attempt was prepared from the arm's template
by `harness.attempt_workspace prepare`, so it works in a tree that holds the attempted seed and its
baseline, the declared dependencies **without** their baselines, the package configuration and a link to
the pinned dependency cache — and nothing else. The receipts are committed as
`results/remediation/prepare-receipts.jsonl`; each arm's five attempts carry **one** seed digest, so each
arm is a single-digest cell. What each package may see is recorded there, and the withheld sets are the
point: a **tier-2** package holds no `<Task>Proved.lean`, so a completed proof of the theorem under
attempt cannot be in the attempt's own tree, while a **tier-1** package declares
`<Task>Proved.lean` as the dependency the protocol sanctions. Each attempt has its own workspace,
results and OMP session root.

The invocations are generated from the receipts into `results/remediation/remediation-run.sh`, so every
`--proof` path is the package the preparer actually built rather than a hand-written one. The run is
serial: one attempt at a time, per the otherwise-idle-host rule. Host load at launch was
**2.26 / 2.15 / 1.71** on 20 cores — recorded as measured, which is low but not the ~0.5 the theorem
cell was launched under, so a reader comparing the two should know the difference rather than assume
an empty machine.

## The gate: this is not a result until the audit is committed

No row here enters `K`, and none is reported as a pass or a failure, until **every** attempt's complete
OMP tool-call transcript has been inspected and its verdict recorded. The audit is the runnable gate:

```
python -m scripts.audit_attempts --sessions results/remediation/<arm>/results \
  --expect-revision results/remediation/revision.json
```

An observed read or copy of an earlier same-tier proof **invalidates that attempt** even when its Lean
file closes; the attempt is then labelled contaminated and excluded, never quietly repeated until it comes
out clean and never pooled. A rerun that itself shows reuse is a result about this rerun.

Withholdings are reported in **three classes** — proof-failure; boundary artifact (integrity, elaboration,
the permitted axiom set and `seed_intact` all true, withheld only for where a scratch file landed); and
**instrument blindness**, where the boundary was never observed — because a single count of "non-closures"
merges findings whose remedies have nothing in common. The theorem cell's two non-closures were one of
each of the latter two and no proof failure at all.

`results/remediation/revision.json` records the code the reruns ran under, over the thirteen common
inputs; each attempt's own `harness_revision` additionally digests its seed, which its receipt pins. That
section is to be **recomputed when the run ends** and a difference means the arms span two revisions —
which is why no `harness/*.py` file may be edited while this is in flight.

## Result: the re-earned arms are contaminated, and `K` cannot be recomputed from them

All thirty attempts landed and every arm was audited with the revision record before its rows were read.
**The revision is `ok` for all six arms** — no `harness/*.py` file changed during the run, so the arms do
not span two revisions. The audit's exit status is `0` for `tok2` and `1` for the other five, and the
per-attempt classification is what that status means:

| arm | clean attempts | verdict-true of clean | walls of clean attempts (s) | median | excluded, with class |
| --- | --- | --- | --- | --- | --- |
| `tok2` | **5/5** | 4/5 | 166.3, 209.8, 310.9, 405.5, 439.8 | **310.9** | — |
| `bak2` | 2/5 | 2/2 | 545.2, 635.8 | — | a1 *attempted*; a2, a4 prior-proof read |
| `lcr2` | 3/5 | 2/3 | 381.1, 405.1, 522.0 | 405.1 | a2, a3 prior-proof read (a2 cross-task) |
| `ewd2` | 2/5 | 1/2 | 869.8, 1265.0 | — | a1, a2, a4 prior-proof read |
| `bak1` | 3/5 | 3/3 | 63.7, 72.8, 76.6 | 72.8 | a1, a3 **prior transcript read** |
| `lcr1` | 4/5 | 3/4 | 66.4, 70.7, 73.3, 207.8 | 72.0 | a2 **prior transcript read** |

**Withholdings, in their three classes, named:** five attempts were withheld on a **boundary artifact**
(`tok2` a1, `lcr2` a1, `ewd2` a5, `lcr1` a1 — each `outside_events`, a scratch file landing outside the
allowed prefix) and **none on instrument blindness** and **none as a proof failure**: every withheld
attempt's `integrity`, `elaborates`, axiom set and `seed_intact` were clean. `bak2` and `ewd2` have only
**two clean attempts of five**, which is **not a strict majority**, so by the preregistered rule their
cells cannot support a settled claim at all.

**Two mechanisms caused the contamination, and both are new doors into the room the isolation was meant to
close.**

1. **A tier-2 attempt read the *shared template's* `<Task>Proved.lean` by absolute path** — `bak2` a2 and
   a4, `lcr2` a2 and a3, `ewd2` a1, a2 and a4, plus `lcr2` a2 reading **`TokenRingProved.lean`**, another
   task's completed proof. The prepared package does **not** contain that module — the receipts show it
   withheld, and `bak2`'s package holds only `Bakery.lean` — so the read reaches the *repository*, which the
   per-package isolation never removed. The contract's first half ("the attempt's own tree offers no prior
   proof") held exactly; its second half ("no observed prior same-tier read") is what failed, and the audit
   is the only reason it is visible.
2. **A tier-1 attempt read prior *evidence* rather than a proof**: `bak1` a1 read the published cell's OMP
   transcript under `results/omp/`, a sibling attempt's `proof.jsonl` and `prepare-receipts.jsonl`; `bak1`
   a3 and `lcr1` a2 read a sibling attempt's `proof.jsonl`. The declared `<Task>Proved.lean` reads that the
   same audit flags are the **intended dependency** and are excluded here — they are why the raw rule's
   output and the classification differ, and why each offence is named rather than counted.

`bak2` a1 is recorded separately as **attempted but not observed**: it read a relative `BakeryProved.lean`
that its package does not contain, so no bytes could enter. That is a different finding from a leak, and
the distinction is behavioural by the contract's own words — "an observed read/copy … invalidates".

**`K` is therefore not recomputed.** Five arms are invalidated in at least one attempt, two fall below the
strict-majority gate, and the remaining three rest on 3–4 clean attempts each; a recomputed `K` from these
rows would be the plausible number built out of contaminated samples that this whole exercise exists to
stop. What the run establishes instead is a finding about the rig: **per-package isolation is necessary and
insufficient on a host with no read sandbox**, because the attempt's shell can reach the repository's
templates and results — and the models do reach them, unprompted, by absolute path. Any clean re-earning of
these four tasks needs the *reachable* corpus changed (the promoted modules and the published transcripts
absent from the tree the attempt runs in), not just the package's contents.

**The Paxos cell is unaffected, and the reason matters:** `proofs/lean/paxos/seeds.json` registers no
`Proved` seed, so mechanism 1 has no door there, and its own audit found all five attempts clean with no
offender of either kind. That is why the Paxos half of the paper and the remediation half are separable
rather than merely sequenced.

**Load, restated beside these numbers:** 2.26 / 2.15 / 1.71 on 20 cores at launch, against the theorem
cell's ~0.5 — a quieter machine is an alternative explanation for any wall-clock difference, and the
comparison against the published figures remains **indicative** in any case, since those rows predate the
`withheld` field and were produced under a different verdict rule.

The recomputed `K`, the per-arm pass rates and the wall/dollar distributions come from **these** rows only.
**That remains the rule, and the Result above is why no such recomputation is reported: five arms are
invalidated in at least one attempt, two fall below the strict-majority gate, and the survivors rest on
three or four clean attempts each.**
Because five published rows carry `outside_events` with `withheld: None` — they predate the field — a
recomputed pass rate and a published one are computed under two different verdict rules, so the comparison
is presented as **indicative** rather than as a like-for-like correction. Every recomputed table states
which arms were re-earned, which rows were quarantined and why, and that the superseded figures were
transcript-contaminated rather than merely noisy.
