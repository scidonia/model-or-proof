# Fresh Paxos tier-2 theorem cell — provenance

The retired `results/paxos-calibration/` pilot is **invalid as a cost cell** for two independent
reasons: its closure oracle resolved `Message.agreement` instead of the seeded `Paxos.agreement`, and
r2/r4/r5 copied r1's working file, so only r1 was an independent attempt. Its five rows and closure
copies are preserved there as diagnostic. This is the replacement cell.

## What was run

Five attempts of the **same registered seed**, one prepared Lean package each, each with its own
workspace, results and OMP session root, so no attempt's tree or session contains another's proof.
Every attempt was prepared from one seed digest by `harness.attempt_workspace prepare` (`61c07de`):

```
nix develop -c python -m harness.attempt_workspace prepare \
  --template proofs/lean/paxos --seed Paxos.lean --attempt <k> \
  --workspace-root results/paxos-theorem-cell/workspaces \
  --results-root   results/paxos-theorem-cell/results
```

Each receipt reported the same `seed_sha256`, the registered digest:

| attempt | package | results root | seed_sha256 |
| --- | --- | --- | --- |
| 001 | `results/paxos-theorem-cell/workspaces/attempt-001/paxos` | `results/paxos-theorem-cell/results/attempt-001` | `0d29361497a893f3ce2ca30d108161486a40cb4aec0ce6efae810986066f184e` |
| 002 | `…/attempt-002/paxos` | `…/results/attempt-002` | same |
| 003 | `…/attempt-003/paxos` | `…/results/attempt-003` | same |
| 004 | `…/attempt-004/paxos` | `…/results/attempt-004` | same |
| 005 | `…/attempt-005/paxos` | `…/results/attempt-005` | same |

Each package held the registered seeds and their baselines, `seeds.json`, the three pinned package
configuration files and `.lake/packages` as an absolute symlink to the 7.2 GB pinned cache — no
`.runs/`, promoted target, closure copy, results directory or OMP session. `lake build` was confirmed to
succeed inside a prepared package before the cell was launched (exit 0, 7.3 s), so the linked cache
resolves for the run and not only for `lake env lean`.

The cell was launched as one serial detached run, one attempt per invocation — `--reps 1`, not a shared
results root — so each attempt reads its own result root and its own session root:

```
for k in 1 2 3 4 5; do
  nix develop -c python -m harness.route_b \
    --task tasks/paxos.json \
    --proof results/paxos-theorem-cell/workspaces/attempt-00$k/paxos/Paxos.lean \
    --mode file --tier 2 --arms proof+refutation --reps 1 --exploratory \
    --results results/paxos-theorem-cell/results/attempt-00$k
done
```

Configuration: tier 2 (the unbounded general theorem), file mode, both arms, one repetition per
invocation, budgets unchanged at 7200 s and $50 per attempt. Each attempt's row lands in its own
`results/attempt-00k/proof.jsonl`, so the five rows are kept as **one named cell without merging their
invocation-local `repetition: 1` values**. Host load at launch was 0.55 / 0.47 / 0.44 on 20 cores, so
the otherwise-idle-host rule was honoured by measurement. No TLC run is part of this cell.

## Status and what the cell is not yet

The rows, closure copies and transcripts are **pending** as this file is written; the attempts run
serially and each may take up to its budget. Nothing here is a result yet.

**The cell's median is not an independent-cost operand, and no `P(N)`, parity, ratio or `n0` arithmetic
may consume it, until the per-attempt transcript audit is complete and committed.** This host has no
read sandbox: the earlier proof of the same theorem remains readable at
`proofs/lean/paxos/.runs/Paxos-r1.lean` and under `results/paxos-calibration/closures/paxos/`, so
independence rests entirely on that audit. The audit is a runnable step rather than a narrative:

```
python -m scripts.audit_attempts --sessions results/paxos-theorem-cell/results        # per-attempt lines
python -m scripts.audit_attempts --sessions results/paxos-theorem-cell/results --json # committed report
```

Its per-attempt lines are committed here as `audit.txt` and its full report as `audit.json`. An
observed read or copy of an earlier same-tier proof invalidates that attempt even if its file closes;
the attempt is then labelled contaminated and excluded rather than pooled, and the cell's pass rate and
distributions are reported with it. Exit status 2 means at least one attempt is *unaudited*, which is
not the same as clean.

The audit scans both channels: prior-proof reads, and writes through the shared `.lake/packages` cache,
which is linked rather than copied and is therefore shared mutable state — a dependency rebuild by one
attempt is visible to the template and to every other attempt, and this cell claims no isolation from
it.
