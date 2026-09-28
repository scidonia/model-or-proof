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


## The code revision this cell ran under

A file-mode row records **no** `harness_revision`, so this cell's rows cannot state which code produced
them. It is captured here instead, computed by the runner's own `harness_revision`
(`harness/route_b.py:217-232`) over the prepared package and the tree as it stood at capture. Combined
digest:

    8fcea371daabcfc77a8e84fd427aa2ee5df7691ba470a6497375f87bf5bf7607

Captured at HEAD `eb1f85f5e6908641499669857960a57f1990c0b2` on 2026-09-28T15:06:07Z, over these inputs:

| input | sha256 |
| --- | --- |
| `harness/__init__.py` | `7ff4ca89bba7f2acdadd9c77cf3ab184c68b7617f3cb06eb7bf6f985a223c198` |
| `harness/attempt_workspace.py` | `d89aba5952ed18f10aad8f134c2b65329cfecc3e7e4c46df841b4e600b83fa89` |
| `harness/closure.py` | `e7e14d5754ee109f7c1e51cbd880d9042e3eea542e7032ea9941c3894d54862c` |
| `harness/closure_oracle.py` | `539b3b94d85a0ba5d359fe0a5d3cf18beb04b5cd4be993aa7adaf78fe3d3b551` |
| `harness/file_mode.py` | `dc3027f0e06bb7e5bcb0c18dff45384068f862d3fd19007835be6617752a4d7b` |
| `harness/lean_lex.py` | `2b00edfe9fe04b3f01f000e1015a02c22713af968964bd37b5bec80a0f696c5d` |
| `harness/lean_repl.py` | `f8e2811b9bde970ac49099c54864f10d00024ea0348b2bc9c3132ee22ed8c4ef` |
| `harness/model.py` | `78bc99d611fccddd0fa5a0ddfbc643f21ca75e9fad8385228395779533ca85a0` |
| `harness/outside_watch.py` | `41c996a779ad32268fb75b92068ff2d7aff9f8196cd988a73f58622861a490dd` |
| `harness/result.py` | `ab9ccd96f993e2d7b6652e0b712a974415bfe24ae85d0d09b1e0fb8a54534b32` |
| `harness/route_b.py` | `ab5c0227c37f89b92f277ac0efe844b488ad7a1240472546a534376d8a1b1d6f` |
| `harness/tlc_run.py` | `8188b83804beb3fa1b4f05fdc11ac8d83cb4482344eae6727a1df9576f14e4ce` |
| `proofs/lean/token-ring/prompt_examples.lean` | `86e0d649ec8931602f249eb185793feeba47067cf976a501bbcb399ad795db63` |
| `results/paxos-theorem-cell/workspaces/attempt-001/paxos/Paxos.lean` | `0d29361497a893f3ce2ca30d108161486a40cb4aec0ce6efae810986066f184e` |
| `results/paxos-theorem-cell/workspaces/attempt-001/paxos/seeds.json` | `8fa7f689ee3e8914dcbb68fc9a7d72645960bce4cb82ce3fa82439c25d9cb47d` |

The attempted seed's digest is the registered `0d29361497a893f3ce2ca30d108161486a40cb4aec0ce6efae810986066f184e`
that every prepare receipt recorded, so this map is anchored to the same bytes the cell was launched
from.

**What it licenses, and what it does not.** It pins the twelve `harness/*.py` files, the few-shot
examples the prompt reads, the attempted seed and the package's `seeds.json`. It is the revision for
attempt 1, and for every later attempt **only for as long as no `harness/*.py` file changes** — a
file-mode row records no revision, so a mid-cell harness edit would leave the later rows produced by
different code with nothing in them to show it. Recompute this section when the cell ends; any
difference splits the cell's five rows across two revisions and must be recorded rather than smoothed
over. That is why no harness edit may land while a cell is in flight, and why this capture exists: the
row cannot say it, so the provenance file must.

## Shape so far — an observation, not evidence

Recorded mid-flight while the attempts run, and deliberately **not** a result: no oracle verdict exists
for any attempt yet, and the per-attempt transcript audit has not run. What was observed is shape.
Attempt-001's session read for roughly nine minutes before its first write, then edited the working copy
`13882 → 22574 → 23234` bytes by about 705 s — against the retired pilot's r1, which read before writing
and reached a comparable size on a comparable clock. r1 is the only attempt in that cell whose transcript
shows no reuse, and therefore the only honest datum available about what a real attempt costs, so an
attempt whose shape matches it is the strongest signal obtainable *before* the audit that this cell is
doing real work. The audit's scan of the same live transcript shows 23 tool calls with **zero** offences
and only the attempt's own working copy among the files it touched.

Why the status matters, and it is the whole reason this section says "observation" rather than "sign":
**a cell that reproduces a neighbour's bytes would also be "writing proof text" — copying a proof *is*
writing it.** What separates the two is whether the transcript shows those bytes arriving from
somewhere else, which is the audit's question and not one a byte count or a duration can answer. Equally,
neither number above is a cost: an attempt's wall clock becomes a datum when its row lands with its
closure verdict, and the cell's median only after all five rows and a complete, committed audit. Nothing
in this section may be cited as independence, as a pass, or as `P(N)`.

**A hypothesis this cell will test, recorded with that status and no more.** The three landed walls are
1,514 / 1,641 / 1,717 s — a 202-second spread, against the retired pilot's 193–1,935 s. If that holds
across all five attempts, the pilot's wide distribution was itself plausibly a *symptom of copying*: each
repetition raced to a different prior proof, so each measured a different amount of remaining work,
whereas five honest attempts from the same seed do the same work and should cluster. The hypothesis is
that the honest distribution is **tight** and the contaminated one was wide. It is not a finding and may
not be used as one: three of five attempts is not a distribution, walls are not costs until their rows
carry verdicts, and the audit decides whether these five are independent at all. The remaining rows and
the audit's verdicts are what test it, and the test is a comparison of distributions recorded *after* the
fact — never a licence to describe this cell as tight before its audit exists.

**Attempt-003's withholding is the benign scratch class, not a candidate breach.** Its two events are
`CREATE` and `MODIFY` of `check_axioms.lean` at its own package root, produced by a `cat > check_axioms.lean`
that ran with the package root as its working directory while the attempt then looked for the file under
`.runs/` — the same working-directory accident as the retired pilot's r4, verified by transcript. Its
`closure` otherwise reads `integrity: true`, `elaborates: true`, `axioms: ['Classical.choice', 'Quot.sound',
'propext']`, `seed_intact: true`, so the proof is good and the boundary is the only reason its verdict is
false. The guard is right to withhold; the cause is an accident.
