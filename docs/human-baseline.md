# The published human-proof baseline

This document records what is **known from the literature** about the human effort of proving the
same systems this experiment measures, and how that prior art is carried in this repository. It exists
so the AI closure loop (Route B) has a human anchor, and so nobody mistakes a published figure for a
measurement made here.

The data lives in [`results/human.jsonl`](../results/human.jsonl) — four records, one per published
experiment, each `kind: "human_prior_art"`, each `machine_checked: false`. The schema, the pooling
rule, and the assertion that no record can be confused with a measured row are fixed by the behavior
contract [`tests/human-baseline-contract.md`](../tests/human-baseline-contract.md).

## Pooling rule

The human baseline may be **cited and charted beside** Route A and Route B. It is **never pooled** into
the same distribution, ratio, or cost statistic, and every record carries
`never_pooled_with: ["route_a_measured", "route_b_measured"]`. The marker is structural rather than a
matter of discipline:

- `kind: "human_prior_art"` and `machine_checked: false`;
- the **absence** of every measured field — no `route`, `tool`, `outcome`, `wall_clock_s`, `startup_s`,
  `peak_rss_mb`, `states_reached`, `cost_usd`, `cost_basis`, `tlc`, `proof`, `repetition`, `tier`,
  `negative_control`;
- a distinct file, `results/human.jsonl`, that no measurement path in `harness/` ever writes to
  (`harness/result.py::append_row` writes `results/<route>.jsonl`, and `route` is `tlc` or `lean`).

No human arm is run: protocol §1 excludes human interactive proof-engineering effort from the claim,
and §11 decision 5 makes the human's role the *statements* (specification, lemma statements), not the
proofs. What follows is therefore evidence carried as data with citations, not a cost we incurred.

## The two publications

1. **Konnov, Kuppe, Merz**, *Specification and Verification With the TLA+ Trifecta: TLC, Apalache, and
   TLAPS*, ISoLA 2022 — <https://members.loria.fr/SMerz/papers/2022-isola.pdf>. Applies all three tools
   to one specification (EWD998, Safra's termination detection on a ring) and is the only publication
   in the set that reports **person-days** for proof effort.
2. **Chaudhuri, Doligez, Lamport, Merz**, *Verifying Safety Properties With the TLA+ Proof System*,
   IJCAR 2010 — <https://members.loria.fr/SMerz/papers/ijcar2010.pdf>. TLAPS proof sizes for Peterson's
   mutual exclusion, Lamport's bakery algorithm, and Paxos consensus. It reports **line counts only**:
   no person-day figure is given, and none is invented here.

## Imported artifacts and their provenance

The artifacts these figures describe are committed in this repository, byte-for-byte from pinned
commits. Per-file repositories, commits, upstream paths, byte and line counts, git blob SHA-1s, and the
license notices are in:

- [`specs/tla/ewd998/PROVENANCE.md`](../specs/tla/ewd998/PROVENANCE.md) — EWD998 (`tlaplus/Examples`
  @ `3dfe0087…`, MIT) plus the four vendored CommunityModules modules (`tlaplus/CommunityModules`
  @ `9aae8ea1…`, MIT).
- [`specs/tla/ijcar2010/PROVENANCE.md`](../specs/tla/ijcar2010/PROVENANCE.md) — Peterson, Bakery, Paxos
  (`tlaplus/tlapm` @ `7824dab5…`, BSD-2-Clause).

**`machine_checked: false` is not a formality.** The imported `*_proof.tla` / `*.tla` modules are TLAPS
proof scripts (`EXTENDS TLAPS`). `tlapm` is not in the dev shell and is not in nixpkgs, so the proofs
are committed **as text with provenance** and are *not* checked by this repository. No test, scenario,
or harness path invokes `tlapm`, and none of these files is parsed by SANY. A record's `artifact_size`
is the one thing about it measured here: the committed file's actual `bytes` and `lines`, which
`tests/test_human_baseline.py` re-checks against the file on disk.

## Published figures

| Record | Figure | Value | Source |
| --- | --- | --- | --- |
| `ewd998` | TLC distinct states, N = 3, K = C = 3, Q = 9 | 1 300 000 | ISoLA 2022 |
| `ewd998` | TLC wall-clock, same instance | 42 s | ISoLA 2022 |
| `ewd998` | TLC states generated, same instance | 10.1m | imported artifact's own table |
| `ewd998` | TLC search depth (diameter), same instance | 60 | imported artifact's own table |
| `ewd998` | Apalache, inductive invariant at N = 100 | 20 s | ISoLA 2022 |
| `ewd998` | TLAPS invariance proof | **1 person-day**, 230 lines | ISoLA 2022 |
| `ewd998` | TLAPS safety + refinement | **half a person-day**, 110 lines | ISoLA 2022 |
| `ewd998` | TLAPS liveness | **less than one person-day**, 245 lines | ISoLA 2022 |
| `ijcar2010-peterson` | TLAPS proof, mutual exclusion | about 130 lines | IJCAR 2010 |
| `ijcar2010-bakery` | TLAPS proof, mutual exclusion | 800 lines | IJCAR 2010 |
| `ijcar2010-paxos` | TLAPS proof, first refinement | 550 lines | IJCAR 2010 |
| `ijcar2010-paxos` | TLAPS proof, second refinement | somewhat over 1000 lines, **incomplete** | IJCAR 2010 |

Every figure in `results/human.jsonl` carries the verbatim `quote` it was taken from. Quotes marked
with a `quote_source` of `docs/protocol.md §1a` are the fragments the protocol commits from the papers;
the rest are quoted directly. The N = 4 context — 219 million distinct states and about 50 minutes, and
"hopeless" beyond — is in protocol §1a and the paper, and is not part of the N = 3 anchor record.

## Published figures versus the committed artifacts

The published line counts and the committed artifacts **disagree**, in both directions. Both are
recorded, and the disagreement is stated in the record's `line_count_disagreement` field; it is never
silently reconciled, because a reader who saw only one side would misjudge the comparison.

| Record | Published | Committed artifact | Note |
| --- | --- | --- | --- |
| `ewd998` | 230 + 110 + 245 = 585 proof lines | `EWD998_proof.tla` 863 lines (+ `AsyncTerminationDetection_proof.tla` 123) | the published figures are per-property and count the proof language only; the artifacts are whole modules, comments included |
| `ijcar2010-peterson` | "about 130 lines" | `Peterson.tla` 199 lines | the artifact carries the specification and the proof |
| `ijcar2010-bakery` | "800 lines" | `Bakery.tla` 383 lines | published *more* than the artifact, the opposite direction |
| `ijcar2010-paxos` | 550 + "somewhat over 1000" | `Paxos.tla` 530 + `Consensus.tla` 22 | the second refinement is incomplete |

A line of proof script and a line of a committed `.tla` module are not the same unit, which is why the
two are reported side by side rather than converted into each other.

## Caveats

- **Person-days only for EWD998.** The IJCAR 2010 records have `effort.unit: "lines_only"` and carry no
  `person_days` figure — a scenario asserts this, so a person-day cannot be added to them by accident.
- **Paxos is partial.** The second refinement proof is incomplete ("most of the proof"). Its figure is
  marked `"partial": true` and is never presented as a finished proof.
- **"Less than one person-day" is a bound, not a measurement.** It is recorded with
  `"bound": "less_than"` and a `value_basis`, so a chart cannot read it as 1.0 day.
- **Units are the paper's units.** "1.3 million distinct states" and "10.1m" are the published
  roundings, recorded as such.

## The EWD998 TLC calibration, against these published numbers

Protocol §11 decision 6 makes EWD998 the externally calibrated task: TLC is run over the imported
instance and compared with the published numbers. Those runs are *measured* Route A runs, so their rows
land in `results/tlc.jsonl` (`route: "tlc"`, `param_N: 3`) — not in `results/human.jsonl`. The
publication-era revision of the same system is committed beside the pin in `specs/tla/ewd998-paper/`
(commit `75f2a7a7369d`, the last revision before upstream widened `Init`), with its own `PROVENANCE.md`;
it is **not** the pin, and it exists so the calibration can *reproduce* a published figure rather than
only cite one.

Invocation — both revisions are measured through the same instrument (D3 of
`plans/2026-09-25-human-proof-baseline.md`; `EWD998Small.cfg`, `N = 3`, `StateConstraint`, invariants
`TerminationDetection`, `Inv`, `TypeOK`):

```bash
# the pinned branch head (specs/tla/ewd998/)
nix develop -c python -m harness.tlc_run --task tasks/ewd998.json --results results --reps 1
# the publication-era revision (specs/tla/ewd998-paper/, commit 75f2a7a7369d)
nix develop -c python -m harness.tlc_run --task tasks/ewd998-paper.json --results results --reps 1
```

| | Distinct states | States generated | Depth | Wall-clock |
| --- | --- | --- | --- | --- |
| Published (the artifact's own table, measured 01/2021) | 1.3m | 10.1m | 60 | 42 s |
| **Publication-era revision** `75f2a7a7369d` (`ewd998-paper`) | **1 384 582** | 10 150 343 | **60** | 32.1 s |
| Pinned branch head `3dfe0087…` (`ewd998`) | **1 520 618** | 11 238 019 | **59** | 35.5 s |

The publication-era revision **reproduces** the published row: 1 384 582 distinct states is the
published "1.3 million", 10 150 343 is the published "10.1m", and the diameter matches exactly at 60.
The pinned branch head does not, and the reason is a single upstream line: `dafe1e5c8a74` (2023-07-28,
"The token may be at any node of the ring initially") widened `Init` of `EWD998.tla` —

```diff
-  /\ token \in [ pos: {0}, q: {0}, color: {"black"} ]
+  /\ token \in [ pos: Node, q: {0}, color: {"black"} ]
```

— *after* the table's figures were added in `2589f6465cc5` (2021-01-21). The only other difference
between the two revisions is one comment line inside `Inv` (`51b9c62ba461`, 2024-03-25); `Next` and
`StateConstraint` are identical, so the instance bound (K = C = 3, Q = 9) is the paper's in both. The
widening enlarges the reachable state set, in the direction measured — more allowed initial states, a
larger distinct count, a shorter diameter (59 against 60). The table embedded in the pinned file is
therefore a stale snapshot of a smaller earlier instance, not a measurement of the bytes that carry it.

Both runs complete with `outcome: success`, no invariant violation, and deterministic counts (the state
space is a function of the module's `Init`/`Next`/`StateConstraint` alone, so the vendored
CommunityModules files cannot influence it). TLC resolves those vendored modules from the spec's own
directory, with no library-path plumbing.

These three rows are recorded as a published-versus-measured finding in the same spirit as the
line-count disagreement above: all of them are stated, none is reconciled, and no row is adjusted to
meet another. The imported spec is **not** edited to restore the 2021 `Init`, the publication-era
revision is a *separate committed directory* rather than a modification of the pin, and no TLC flag or
config is tuned to move the measured numbers. Machine-readably, the same three rows sit on the `ewd998`
record of `results/human.jsonl` under `calibration` (`published`, `paper_era`, `branch_head`,
`root_cause`), which `tests/test_human_baseline.py` asserts — including that the branch head's count is
at least the paper-era count, since the widening can only enlarge the set.
