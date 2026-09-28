# Tier-1 corollary pilot at N=6 — provenance

This is the **instantiation-cost datum for H2**, not a bracket operand. H2 claims the proof route is close
to flat in `N` because the theorem it uses is general and instantiation is free; the corollary-at-N cost is
exactly that figure, and one cell at a fixed instance measures it against the theorem cell's median.

**It cannot change the crossing verdict, and was not run for it.** `P(N) = median(tier-2 theorem) +
median(tier-1 corollary-at-N)` with the first term fixed at 1640.69 s and the second non-negative, against
every measured `A(N) ≤ 1405.943 s`, means `A(N) < P(N)` at every candidate `N` in 2…6 and no bracket — the
arithmetic is in `plans/2026-09-27-paxos-agreement.md`, and this cell's result is reported below as a
measured operand with **no ratio**.

## What was run

Five attempts of the same registered seed, one prepared Lean package each, each with its own workspace,
results and OMP session root. Every attempt was prepared from one seed digest, `d3043114fe8a…`:

```
nix develop -c python -m harness.attempt_workspace prepare \
  --template proofs/lean/paxos --seed PaxosN6Pilot.lean --dependency PaxosProved.lean \
  --attempt <k> --workspace-root results/paxos-corollary-pilot/workspaces \
  --results-root results/paxos-corollary-pilot/results
```

Each receipt reported `included ["PaxosN6Pilot.lean", "PaxosProved.lean"]` and
`withheld ["Paxos.lean", "PaxosMutant.lean"]` — the tier-1 asymmetry: the proved module is the **declared
dependency** the attempt is meant to instantiate, while the tier-2 seed and the mutant are withheld (for
the tier-2 theorem cell the same module is withheld instead, which is the difference that matters).

The cell was run one attempt per invocation, serial, `--reps 1`, mirroring the theorem cell:

```
for k in 3 4 5; do
  nix develop -c python -m harness.route_b --task tasks/paxos.json \
    --proof results/paxos-corollary-pilot/workspaces/attempt-00$k/paxos/PaxosN6Pilot.lean \
    --mode file --tier 1 --param-N 6 --arms proof+refutation --reps 1 --exploratory \
    --results results/paxos-corollary-pilot/results/attempt-00$k
done
```

## The launcher stalled after two attempts, and the remainder was relaunched

Roughly fourteen minutes of silence after attempt-002's row: `attempt-003/omp/<session>` existed and was
empty, attempts 004/005 had empty results roots, and nothing was running. **The third invocation began and
was killed mid-run** — its session directory is what proves it (the prepare step creates the results root
*empty*), and its transcript shows dozens of tool calls before it died. The cause was the **launcher**: a
plain background shell, whose death was reported to nobody — not a rig fault. It is preserved as evidence
at `results/paxos-corollary-pilot-killed-attempt-003/`, **outside** the cell root so a live attempt cannot
reach it by walking up.

The relaunch rebuilt attempt-003 only (a killed attempt's package is not clean) and kept 004/005's original
packages (never run, so still clean), under the same frozen revision, and registered it as a service with a
ready signal and a terminal marker so its exit surfaces rather than its death going unreported.

## The seed

`proofs/lean/paxos/PaxosN6Pilot.lean` states `Paxos.agreement` at `N = 6`, with `Fin 2` values and
strict-majority quorums (`{Q | Q.ncard > N₆ / 2}`, `PaxosFinite.tla:35`), imports the promoted
`PaxosProved`, and carries exactly one `sorry` — the one hole the run closes. It is **not** `PaxosN0.lean`:
`tasks/paxos.json`'s `n0` is null, the plan selects `n0` from the crossing's own medians, and `PaxosN0.lean`
is authored only after that selection. Its prose also records that `PaxosN6.cfg` bounds `B = 1` while the
model's ballot type is `ℕ` — so the corollary at any `N` is **stronger** than the bounded TLC row it is
priced against, and the two wall-clock numbers are not two measurements of one claim.

## Result

| attempt | outcome | wall (s) | closed | elaborates | integrity | axioms | withheld | closure copy |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 001 | closed | 115.701 | true | true | true | permitted 3 | `outside_events` | no |
| 002 | closed | 75.344 | true | true | true | permitted 3 | `outside_events` | no |
| 003 | closed | 665.100 | true | true | true | permitted 3 | `outside_events` | no |
| 004 | closed | 577.630 | true | true | true | permitted 3 | `outside_events` | no |
| 005 | closed | 418.929 | true | true | true | permitted 3 | `outside_events` | no |

**Five attempts, five complete proofs, five withholdings for compiling.** Every row is `closed`,
`elaborates`, `integrity` true with `axioms = {propext, Classical.choice, Quot.sound}` and `seed_intact`
true; every one is withheld, and **all five for the same cause**: the toolchain's own build output. The
events (22–25 per attempt) are `lake build` writing inside the attempt's **own** package —
`CREATE,ISDIR …/paxos/.lake/build`, `ir/PaxosProved.setup.json`, `lib/lean/PaxosProved.olean.tmp.<pid>`,
`MOVED_FROM`/`MOVED_TO` — with `outside_writes` empty in every row. That is a rig defect, not a proof
failure: `.lake/packages` is the symlink to the shared cache and must stay watched, but `.lake/build` is the
attempt's own local output and cannot reach the repo or a sibling. Recorded here and fixed after the
freeze, because `harness/outside_watch.py` is inside the cell's revision record.

**The H2 datum.** All-attempt median **418.929 s**, so `P(6) = 1640.69 + 418.929 = 2059.619 s` against
`A(6) = 1405.943 s`. The median is taken over **all** precommitted attempts whether or not their verdicts
are true, the precedent the theorem cell set and the reason its withheld attempts' actual times are in its
median; a reader who assumes withheld attempts are excluded would compute a different median from the same
rows. What the withholding changes is only the naive pass rate — read without this, the cell says 0 of 5 —
and the pass rate is not the measure.

## The audit

`scripts/audit_attempts.py --sessions results/paxos-corollary-pilot/results --expect-revision
results/paxos-corollary-pilot/revision.json` → **exit 0**: five sessions, **283 tool calls**, all five
**clean**, `revision ok`.

**What it licenses, precisely.** No attempt read or copied a prior proof: no `prior-copy`, no
`promoted-proof`, no closure copy. Three attempts (003–005) did read earlier attempts' **rows** —
`results/attempt-001/proof.jsonl` and `attempt-002/proof.jsonl`, including through a shell glob over
`attempt-$a/proof.jsonl` — which the audit now reports as `other`, not as a reuse channel: a row is the
run's record (verdict, axioms, paths) and carries no reasoning and no proof text. Those rows name
`closure_copy: null`, so no proof path was even named to them. Two classifier corrections were needed to
reach an honest verdict, each with a scenario, a red and a guard-rail in
`tests/audit-boundary-contract.md`: the tier-1 **declared dependency** is the design and not reuse
(Scenario 5 — without it every row here would have been excluded for doing what its receipt told it to do),
and a row is metadata rather than a transcript (Scenario 6 — without it these three attempts would have
been reported as reusing a proof they never read). Both fixes are fail-closed in the direction that
matters: a **foreign** task's proved module still contaminates, a **tier-2** attempt reading any proved
module still contaminates, an attempt with **no row** declares nothing, and another attempt's
**transcript** still invalidates.

## The code revision this cell ran under

A file-mode row records **no** `harness_revision`, so this cell's rows cannot state which code produced
them. It is captured instead in `revision.json`, computed by the runner's own `harness_revision` over the
prepared attempt-001 package and the tree:

    digest 4adf11cea8673bbf74a217576006b3b419e4250f2fc960fae9bff418612d29bd
    HEAD   164e311164c633307edc061db92ab276fc0df4c7

**Captured after launch rather than before it, and re-verified at cell end: the recomputed digest is
identical and no input differs.** So the post-launch capture is not a weakness here — the harness was
frozen through the cell and the package's own copies were untouched, and the row's `pristine_sha256` and
`baseline.matches` carry the seed's integrity independently of this file. Any difference would have split
the cell's five rows across two revisions and had to be recorded rather than smoothed over; there is none.

## What it licenses, and what it does not

It licenses one measured figure: **instantiating the proved general theorem at a six-acceptor instance
costs a median 418.929 s**, against the general theorem's 1640.69 s — about a quarter — and the sum still
exceeds the largest TLC instance that completes. It does **not** license a ratio, a crossing, or a pass
rate: the crossing is ruled out by arithmetic on operands that do not include this one, and the five
withholdings are the build-write defect, not failures to prove.
