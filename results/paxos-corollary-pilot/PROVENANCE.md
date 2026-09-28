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

**The H2 datum.** All-attempt median **418.929 s**; with attempt-003 excluded as contaminated (see the
audit below), the operand is the clean median **267.315 s**, so
**`P(6) = 1640.69 + 267.315 = 1908.005 s`** against **`A(6) = 1405.943 s`**. Both medians are given
because the selection rule takes **all** precommitted attempts whether or not their verdicts are true — the
precedent the theorem cell set, and the reason its withheld attempts' actual times are in its median — while
a **contaminated** attempt is excluded rather than pooled; a reader who applies only one of the two clauses
would compute a different number from the same rows. The conclusion does not turn on it: `1908.005 > 1405.943`
as `2059.619 > 1405.943`, and the crossing is nonviable either way. What the withholdings change is only the
naive pass rate — read without this, the cell says 0 of 5 — and the pass rate is not the measure.

## The audit

`scripts/audit_attempts.py --sessions results/paxos-corollary-pilot/results` → **exit 1**: four sessions
**clean**, one **contaminated**.

**attempt-003 is contaminated, and what it read is a prior artifact of this cell's own seed.** Its
transcript contains `cat` of
`results/paxos-corollary-pilot-killed-attempt-003/attempt-003-workspace/paxos/.runs/PaxosN6Pilot-r1.lean` —
the working file of the *first* attempt-003, the one the launcher's death killed and whose workspace was
preserved as evidence. That file is a partial proof of the same statement. So this attempt's cost is **not
an independent measurement** and it is excluded from the H2 operand above rather than pooled. The
contamination came from my own preservation step: the killed attempt's workspace was moved out of the cell
root to keep it away from live attempts, and it was still reachable by absolute path.

**Three attempts (003–005) also read earlier attempts' rows** — `attempt-001/proof.jsonl` and
`attempt-002/proof.jsonl`, including through a shell glob — which are **metadata**: a row is the run's
record (verdict, axioms, paths) and carries no reasoning and no proof text, and those rows name
`closure_copy: null`, so no proof path was even named. Those hits are reported and do not invalidate
(contract Scenario 6). What crosses attempts is otherwise enumeration — 005 `find`s a sibling's package,
which the contract treats as listing rather than opening.

**What it licenses, precisely.** No attempt read or copied a prior **proof** except attempt-003, whose read
is above and whose row is excluded; the remaining four are clean, with no `prior-copy`, no undeclared
`promoted-proof` and no closure copy. Two classifier corrections were needed to reach that verdict, each
with a scenario, a red and a guard-rail in `tests/audit-boundary-contract.md`: the tier-1 **declared
dependency** is the design and not reuse (Scenario 5 — without it every row here would have been excluded
for doing what its receipt told it to do), and a row is metadata rather than a transcript (Scenario 6 —
without it three attempts would have been reported as reusing a proof they never read).

**A third correction came only from this cell, and it is the reason the cell's first clean verdict was
wrong.** `other-copy`-by-name could not tell an attempt's own `<stem>-r1.lean` from an identically named
file in a sibling package or another cell, and every attempt and every cell starts at `r1`; attempt-003's
read of the killed attempt's file was invisible to it, and to the hand-run transcript scan that had been
used to license the earlier claim, for the same reason. Scenario 7 now decides by path within the
repository — outside both the package the row names and the attempt's own results tree — which catches
attempt-003's read and leaves the other four and the whole theorem cell untouched. **The audit makes that
check itself now**, per attempt, which is what matters for a remediation of six arms: a hand-run scan per
arm is not a gate.

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
