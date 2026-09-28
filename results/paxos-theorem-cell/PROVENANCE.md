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

## Result

All five attempts completed and the audit is committed beside them (`audit.txt`, `audit.json`).

| attempt | outcome | wall (s) | final verdict | withheld | integrity | elaborates | axioms | closure copy |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 001 | closed | 1640.690 | **true** | — | true | true | permitted 3 | yes |
| 002 | closed | 1716.946 | **true** | — | true | true | permitted 3 | yes |
| 003 | closed | 1514.427 | false | `outside_events` | true | true | permitted 3 | no |
| 004 | closed | 1712.214 | **true** | — | true | true | permitted 3 | yes |
| 005 | closed | 386.999 | false | `watch_blind` | true | true | permitted 3 | no |

**Pass rate 3 of 5 verdict-true**, a strict majority, so the cell supports a settled claim. All-attempt
wall times with both withheld attempts' actual elapsed times included: min 386.999, **median 1640.690**,
max 1716.946 s; cell cost $0.00498. A closed-only median is not reported, because it is not the selection
operand.

**The audit passes.** `scripts/audit_attempts.py --expect-revision` over
`results/paxos-theorem-cell/results`, exit **0**: all five attempts `clean`, **zero** offences across
**359 tool calls**, and `revision ok`. So no attempt read or copied an earlier same-tier proof, and the
tree still matches the recorded revision — the cell is not split across revisions. The gate's own
evidence is committed as `audit.txt` (per-attempt lines) and `audit.json` (full report).

**Both withholdings are boundary artifacts, not failures to prove — in two different classes.**

- **attempt-003 — write location.** Two events, `CREATE` and `MODIFY` of its own
  `workspaces/attempt-003/paxos/check_axioms.lean`: a `cat > check_axioms.lean` whose working directory
  was the package root while the attempt then looked for the file under `.runs/`, the same accident as
  the retired pilot's r4. `outside_writes` is empty, so no watched file outside the working copy changed.
- **attempt-005 — instrument blindness, and it is the harness's own fault.** Its `watch_blind` reads
  *"the event stream is not readable: 'Watching new directory …/attempt-005/paxos/.runs/probe/'"*. That
  line is **inotifywait's own announcement that it added a watch** for a newly created subdirectory, and
  `harness/outside_watch.py:95-113` fails closed on any line it cannot parse. Reproduced directly:
  `inotifywait -m -r --format "%e %w%f" -e create -e modify -e delete -e attrib <root>`, with a
  subdirectory created inside the tree, prints `Watching new directory <path>/` on stdout *before* the
  corresponding `CREATE,ISDIR`. So a model that organises scratch into a subdirectory **inside the allowed
  prefix** — the most compliant behaviour available to it — blinds the watch and forfeits its verdict.
  Its transcript shows only two write-ish calls, both `own-copy`, so nothing was written outside its own
  package; but the transcript sees only the model's own tool calls, not what a command's children wrote,
  so it cannot certify the boundary alone and the withholding stands.

  The rate is therefore **two boundary artifacts and zero proof failures**: the arithmetic that reads as
  "3 of 5 with two failures to prove" is the wrong reading, and only the transcripts separate them.
  This is also the third instance of the guard or the harness withholding a *correct* action — after
  attempt-003's scratch write and the retired pilot's row 58 repair.

The gate is re-runnable in one command, and its output *is* the committed evidence:

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

**Recomputed at cell end, as this section required.** Every one of the fifteen inputs still hashes to
its recorded value and the combined digest still matches, so no `harness/*.py` file changed while the
cell ran and its five rows were produced by **one** code revision — the check `scripts/audit_attempts.py
--expect-revision` performs inside the gate, where it reported `revision ok`. The row cannot carry this,
so the audit does.

**What it licenses, and what it does not.** It pins the twelve `harness/*.py` files, the few-shot
examples the prompt reads, the attempted seed and the package's `seeds.json`. It is the revision for
attempt 1, and for every later attempt **only for as long as no `harness/*.py` file changes** — a
file-mode row records no revision, so a mid-cell harness edit would leave the later rows produced by
different code with nothing in them to show it. Recompute this section when the cell ends; any
difference splits the cell's five rows across two revisions and must be recorded rather than smoothed
over. That is why no harness edit may land while a cell is in flight, and why this capture exists: the
row cannot say it, so the provenance file must.

**Re-running the check today will name two files, and that is expected rather than a split revision.**
The harness's placeholder clause was corrected *after* this cell ended (`harness/lean_lex.py`,
`harness/lean_repl.py`): `count_unclosed` had counted a named synthetic placeholder as a hole and so
refused a proof the oracle certifies closed, and the fix splits the scan, leaving `count_holes` — which
`harness.closure.incomplete_body` still uses for its declaration-level question — untouched. So
`audit_attempts.py --expect-revision results/paxos-theorem-cell/revision.json` will now report those two
paths as changed. They changed **after** the last attempt finished, which the committed `audit.txt`
(`revision ok`, five `clean` sessions, zero offences) is the in-flight evidence for, and the edit cannot
move these rows: their verdicts come from the closure oracle and the outside watch, and `count_unclosed`
reaches only `guard_imports`, over the **seed** whose sole hole is the intended `sorry` that the run
exists to close. A reader who sees two names here should read this paragraph rather than conclude the
cell spans two revisions.

## The mid-flight shape note, and whether it held

Written while the attempts were running and kept because it named the hypothesis in advance. It read:
attempt-001 spent roughly nine minutes reading before its first write, then reached 22574 → 23234 bytes
by about 705 s, matching the retired pilot's r1 shape — and the retired cell's wide 193–1,935 s spread
was, on this reading, plausibly a *symptom of copying*, since each repetition raced to a different prior
proof and therefore measured different remaining work, whereas honest attempts from one seed should
cluster.

**It held, with one outlier that the audit clears.** The four full-length attempts landed at 1514.427 /
1640.690 / 1712.214 / 1716.946 s — a **202-second spread**, against the retired pilot's 1,742-second one.
The fifth, attempt-005, closed in **386.999 s**, roughly four times faster, and it is the attempt whose
watch was blind; but its transcript audit is **clean** (43 tool calls, zero offences), so the honest
reading is a fast close rather than a fast copy. What the note forbade still stands: a tight cluster is
not evidence of independence, and it was the audit — not the distribution — that decided this cell.

A note on what this section is not: the mid-flight paragraphs asserting that nothing here was a result
have been superseded by the Result section above, and the two preceding paragraphs describing
attempt-003's withholding have been folded into it rather than left to age in place.
