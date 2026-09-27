# Non-vacuity witnesses — Paxos finite projection

**Control:** `docs/protocol.md` §4.10 (bounded non-vacuity witness). A finite projection or a bound can
make an invariant true *by preventing the behavior under test*, and `Consistency` is exactly such an
invariant: it is trivially true of every reachable state if no value can ever be chosen. For every N
measured on the positive curve, this file records a **second** TLC run whose checked property is the
deliberately false diagnostic predicate `NoChoice == ~(\E v \in Values : Chosen(v))`
(`specs/tla/paxos/PaxosFinite.tla`, last definition). A TLC counterexample to `NoChoice` is a real,
reachable behavior in which a value **is** chosen at that N — which is what makes the positive row a
measurement rather than a vacuous pass.

These are **diagnostic** runs. Their rows live in `results/paxos-witness/tlc.jsonl`, never in the
headline `results/tlc.jsonl`, and are excluded from every Route A/B statistic. They do **not** replace
the mutant (`specs/tla/paxos/PaxosFiniteMutant.tla`, `tasks/paxos.json`), which tests a different
failure: the witness shows a decision is reachable, the mutant shows the weakened `Phase2a` guard lets
two different values be chosen.

**Held constant across every row:** ballot bound `B = 1` (inside every `PaxosN<N>Witness.cfg`), value
domain `Values = {"v0", "v1"}` with the sentinel `"NoValue"`, strict-majority
`Quorums == {Q \in SUBSET Acceptors : Cardinality(Q) > N \div 2}`, one TLC worker, spec
`specs/tla/paxos/PaxosFinite.tla`. Only the acceptor count `N` varies.

**Invocation (one positive and one witness attempt per N; serial on an unloaded host, D10):**

```bash
nix develop -c python -m harness.tlc_run --task tasks/paxos-witness.json --results results/paxos-witness --instance <N> --reps 1
```

| N | B | property checked | input config | row | log | trace depth | witnessed value | status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 1 | `NoChoice` | `specs/tla/paxos/PaxosN2Witness.cfg` | `results/paxos-witness/tlc.jsonl:1` (param_N=2) | `results/paxos-witness/logs/paxos-witness-20260927T231102-r1.log` | 7 | `Chosen("v1")`: ballot-0 `2b` votes from acceptors 1,2 — the whole acceptor set, a quorum at N=2 | `violation` (0.706 s) |
| 3 | 1 | `NoChoice` | `specs/tla/paxos/PaxosN3Witness.cfg` | `results/paxos-witness/tlc.jsonl:2` (param_N=3) | `results/paxos-witness/logs/paxos-witness-20260927T231105-r1.log` | 7 | `Chosen("v1")`: ballot-0 `2b` votes from acceptors 1,2 — 2 of 3, a strict majority | `violation` (0.717 s) |
| 4 | 1 | `NoChoice` | `specs/tla/paxos/PaxosN4Witness.cfg` | `results/paxos-witness/tlc.jsonl:3` (param_N=4) | `results/paxos-witness/logs/paxos-witness-20260927T231106-r1.log` | 9 | `Chosen("v1")`: ballot-0 `2b` votes from acceptors 1,2,3 — 3 of 4, a strict majority | `violation` (0.817 s) |
| 5 | 1 | `NoChoice` | `specs/tla/paxos/PaxosN5Witness.cfg` | `results/paxos-witness/tlc.jsonl:4` (param_N=5) | `results/paxos-witness/logs/paxos-witness-20260927T231107-r1.log` | 9 | `Chosen("v1")`: ballot-0 `2b` votes from acceptors 1,2,3 — 3 of 5, a strict majority | `violation` (1.217 s) |
| 6 | 1 | `NoChoice` | `specs/tla/paxos/PaxosN6Witness.cfg` | `results/paxos-witness/tlc.jsonl:5` (param_N=6) | `results/paxos-witness/logs/paxos-witness-20260927T231113-r1.log` | 11 | `Chosen("v1")`: ballot-0 `2b` votes from acceptors 1,2,3,4 — 4 of 6, a strict majority | `violation` (4.924 s) |
| 7 | 1 | `NoChoice` | `specs/tla/paxos/PaxosN7Witness.cfg` | `results/paxos-witness/tlc.jsonl:6` (param_N=7) | `results/paxos-witness/logs/paxos-witness-20260927T231144-r1.log` | 11 | `Chosen("v1")`: ballot-0 `2b` votes from acceptors 1,2,3,4 — 4 of 7, a strict majority | `violation` (31.179 s) |
| 8 | 1 | `NoChoice` | `specs/tla/paxos/PaxosN8Witness.cfg` | none written | none written | — | — | **not run to completion**: started 23:12, stopped by hand at 23:14 once it was off the sweep's path; it wrote no row and no log, and that run is not evidence of anything |

## Scope of this file

One witness per **measured positive instance**: the sweep runs N=2,3,4,… in order under the 7200 s cap and stops at the first observed timeout (plan D1 as revised). Every instance with a positive row — success *or* timeout — gets its witness check; a configured instance above the first timeout gets none, because it is never compared and §4.10 asks for a witness for each *compared* instance. `tasks/paxos-witness.json` keeps the same instance list as `tasks/paxos.json` regardless, so the two manifests stay in lockstep and `tests/test_paxos_projection.py:23-53` holds.

## Provenance of the measured module text

The module bytes named by every row above are the committed bytes: `specs/tla/paxos/PaxosFinite.tla` and `PaxosFiniteMutant.tla` were **not** edited at any point during the sweep, and the witness configs differ from their positive configs only in the invariant name (verified by diff). No `ASSUME` was added: the accepted domain `N ≥ 2`, `B ≥ 1` is carried by the instance family and by the planner-owned contract test over every configured `N` and `B`, not by a constant-level assertion inside the projection (planner decision on the D1 wording). The imported `specs/tla/ijcar2010/paxos/Paxos.tla` and `Consensus.tla` remain byte-identical to their pinned blobs
(`git hash-object` → `bdec77b86eb79d31069f33df725e8cce14acc18c` and `41be40c6a8e11f92bcedd1cc715a8e7d36d5ca41`, 530 and 22 lines).

**Known gap, for the planner rather than for this task:** `harness/tlc_run.py` records `artifacts.spec` and `artifacts.config` as paths only, with no digest of the module, so a row cannot be tied to the exact text that produced it without this file's word for it.
