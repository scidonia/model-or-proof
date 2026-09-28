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

## How the result is to be read

The recomputed `K`, the per-arm pass rates and the wall/dollar distributions come from **these** rows only.
Because five published rows carry `outside_events` with `withheld: None` — they predate the field — a
recomputed pass rate and a published one are computed under two different verdict rules, so the comparison
is presented as **indicative** rather than as a like-for-like correction. Every recomputed table states
which arms were re-earned, which rows were quarantined and why, and that the superseded figures were
transcript-contaminated rather than merely noisy.
