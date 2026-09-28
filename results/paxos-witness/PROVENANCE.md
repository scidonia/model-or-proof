# Non-vacuity witnesses — Paxos finite projection

**Control:** `docs/protocol.md` §4.10 (bounded non-vacuity witness). A finite projection or a bound can
make an invariant true *by preventing the behavior under test*, and `Consistency` is exactly such an
invariant: it is trivially true of every reachable state if no value can ever be chosen. For every N
checked below, this file records a **second** TLC run whose checked property is the
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

**Coverage.** Witnesses were run one attempt per N for N=2,3,…,7 — the pre-planned diagnostic set — alongside the positive sweep, which runs N=2,3,4,… in order under the 7200 s cap and stops at the first observed timeout (plan D1 as revised). Every instance that carries a positive row, success *or* timeout, is therefore covered. If the sweep's first timeout falls below N=7, the higher-numbered rows here are diagnostics *beyond* the compared set: they are retained rather than deleted, and they show the projection still admits a reachable decision at those bounds even though no positive row was measured there. N=8 has no witness row — it is needed only if a positive N=8 row exists, and the sweep stops at the first timeout before that (see that row). `tasks/paxos-witness.json` keeps the same instance list as `tasks/paxos.json` regardless, so the two manifests stay in lockstep and `tests/test_paxos_projection.py:23-53` holds.

## Provenance of the measured bytes

Rows name their spec and config by **path**, not by digest (`harness/tlc_run.py:322-326`), so the digests below are what fixes *which* bytes produced the rows already measured — the positive rows in `results/tlc.jsonl` and the witness rows in `results/paxos-witness/tlc.jsonl`. They were taken while the sweep was in flight (N=6 running) and re-checked after it ended; the module bytes were **not** edited at any point during the sweep, and each witness config differs from its positive config only in the invariant name (verified with `diff`).

All files live in `specs/tla/paxos/`; copy the block there and run `sha256sum -c` to re-check. `PaxosMutant.cfg` and `PaxosN3.cfg` are byte-identical by design (both `N = 3`, `B = 1`, `INVARIANT Consistency`).

```
c487e2d933dd7004b720e29b505ff5a01dc68c23e2d9e49eddd0c0518ccc653d  PaxosFinite.tla
667cbe931f3b876a1007ea311561544e340cbca3cf00d9a05b7dab176377d4e7  PaxosFiniteMutant.tla
6e660a031f6ba0a9257985a39c71abdc46c7aa8a1fa1d41a7ff5ab2dc18ca0da  PaxosMutant.cfg
63d840c6316168d5ec43352c5b9ec7dc276503072ea80f6aa615c4ea3b79daa8  PaxosN2.cfg
6e660a031f6ba0a9257985a39c71abdc46c7aa8a1fa1d41a7ff5ab2dc18ca0da  PaxosN3.cfg
8bf7a274d94888408551c365ee7735ec67bb9399be42429ec8ed4572ae8c3d41  PaxosN4.cfg
cb6c43c879c2dc2c7f0d174600f95ab0e825fdcf053fa70bfbd63d4416125081  PaxosN5.cfg
c764a584353a481887cfa270dea212663742583f6a11d3cb6191e4bd0373d9c2  PaxosN6.cfg
f9c7bc3ed04078f36e481051ed16460f5039eab989996d49a77f0c04cce56ad0  PaxosN7.cfg
7b3b0c91be70064786da1baf34e3d53e468e6f4e84af78f08807676c3469be27  PaxosN8.cfg
5944626873dceddc438e701b291d49d6e1a17e92087a87b4397705f8929638cf  PaxosN2Witness.cfg
aa93b80d264181fd5c7b296f858e929d759f48a226ef78b3887f6d264fbe2655  PaxosN3Witness.cfg
fcef2f276b4492176aea77567a298c6828c11837169fcc62dd2e5bda7d697524  PaxosN4Witness.cfg
dc20b53765cf6537595d6a13a815e99b888b6be53bc291dee40cff0a45101ff0  PaxosN5Witness.cfg
85dc1c502b62b1598a7be8881eb5e7c684bbb26b6a8e42b17e224620eecfa5a2  PaxosN6Witness.cfg
4ee62b9a5af616c79517d3d21203cd429f6cbea794e492857d7d4d56f020da4d  PaxosN7Witness.cfg
425a25d86ab3c7d0819ee3296a50c461ad666e39240f5035f3edecd58e2364a9  PaxosN8Witness.cfg
```

No `ASSUME` was added: the accepted domain `N ≥ 2`, `B ≥ 1` is carried by the measured instance family and by the planner-owned structural contract over every configured `N` and `B` (`tests/test_paxos_projection.py:23-53`), not by a constant-level assertion inside the projection (planner decision on the D1 wording; `plans/2026-09-27-paxos-agreement.md:25-27`). The imported `specs/tla/ijcar2010/paxos/Paxos.tla` and `Consensus.tla` remain byte-identical to their pinned blobs (`git hash-object` → `bdec77b86eb79d31069f33df725e8cce14acc18c` and `41be40c6a8e11f92bcedd1cc715a8e7d36d5ca41`, 530 and 22 lines).

## What the projection costs per state (positive rows, exhaustive)

| N | wall-clock | distinct | generated | depth | µs / distinct | MB / distinct, peak RSS |
| --- | --- | --- | --- | --- | --- | --- |
| 2 | 0.717 s | 145 | 347 | 13 | 4,945 | 1,276.8 |
| 3 | 1.067 s | 3,921 | 16,971 | 17 | 272 | 117.6 |
| 4 | 2.620 s | 20,609 | 105,723 | 21 | 127 | 38.6 |
| 5 | 129.029 s | 701,505 | 5,041,259 | 25 | 184 | 8.2 |
| 6 | 1,428.163 s | 4,768,897 | 38,393,851 | 29 | 299 | 1.2 |

Startup is 0.20–0.22 s on every row and dominates N=2; from N=3 on search time is 127–299 µs per distinct state and peak footprint falls from ~118 to ~1.2 MB per 1,000 states as the fixed heap overhead amortises. Depth grows by exactly 4 per acceptor (13, 17, 21, 25, 29). Wall-clock tracks the distinct-state curve with a mild super-linear factor, which is the shape the crossover rule interrogates (protocol §7).

## Sweep boundary, and the interrupted first N=7 launch

Positive instances measured: **N = 2, 3, 4, 5, 6** — every row `success`, exhausted (`left = 0`), inside the 7,200 s cap, each with its witness row above.

**The first N=7 launch is recorded rather than dropped.** It started 23:38:30 and was killed at 3,600 s by the *caller's* command timeout — a clock outside the experiment, neither the harness's 7,200 s cap nor a TLC failure — writing no row and no log. It establishes nothing: the memory readings taken while it ran (VmRSS 3.87 GB / VmHWM 5.65 GB at 693 s and 783 s) describe a process its caller terminated, and cannot be cited as an N=7 measurement. Its private metadir was removed. It is kept in the record because a sweep that silently omits an instance reads as a clean stop.

**The second N=7 launch is the measurement of record.** Started 00:39, detached (`setsid`, PPID 1), so no tool-call shell could impose a shorter clock on it and the manifest's 7,200 s was the only cap in play; a stop inside the JVM would have surfaced as an `error` row carrying TLC's own tail rather than as silence. Outcome: **`timeout` at 7,200.278 s** — row `results/tlc.jsonl` (param_N=7), log `results/logs/paxos-20260928T023927-r1.log`. The log holds 120 `Progress` lines and **no** anchored final summary (so the row's `tlc` object is `null`, as a capped run must be), the last of them reporting 66,416,257 states generated and **10,850,698 distinct**; peak RSS 5,535.5 MB, `error: null`, load 0.30/0.77/0.94 before and 1.06/1.03/1.07 after on 20 cores. This is the first observed boundary: N=7 did not finish inside the cap.

N=8 was not run. The sweep ends at the first observed boundary, and N=7 is bounded above by it (state counts grow with the acceptor count), so a further instance could only time out again; `tasks/paxos.json` still lists N=2–8 as its configured family, as the contract requires.

Boundary fields: `calibration.n_cap_exploratory = 6` — the largest adjacent successful predecessor of the timed-out N=7. `calibration.n_cap = null`: the protocol-facing cap boundary is **not** established, because this timeout was measured under the implicit 14,247 MB heap and random `-fp`/`-seed` profile described below, and the planner requires the same bound under a pinned profile before it may be called a fixed-profile 2 h cap.

## The run profile every row was taken under — exploratory, not §4.4 pinned

Protocol §4.4 asks for `-workers 1`, an explicit heap, and `-fp`/`-seed` pinned where supported. The runner passes `-workers 1` and a private `-metadir` and nothing else (`harness/tlc_run.py:159-181`), so every row below ran under an **observed implicit 14247 MB heap whose mechanism is unresolved** (the same installed wrapper reports `-XX:+PrintFlagsFinal` MaxHeapSize 16027 MiB today, so the banner value is observed, not explained) and a **fresh random fingerprint seed**. This curve is therefore an *exploratory* measured curve, not a §4.4 pinned-profile row set. Planner ruling: a first timeout under this profile establishes only `calibration.n_cap_exploratory`; the protocol-facing `calibration.n_cap` stays `null` until the same bound is measured under a later pinned profile, so an implicit-heap timeout cannot masquerade as a fixed-profile 2 h cap. TLC's own collision estimate over these runs is 1.6E-15, 2.8E-12, 9.5E-11 at N=2/3/4 and 1.7E-7 optimistic / 1.9E-7 from actual fingerprints at N=5, so the random seed did not cost search completeness at these sizes.

| row | N | outcome | banner fp | banner seed | banner heap MB | log |
| --- | --- | --- | --- | --- | --- | --- |
| positive | 2 | success | 8 | -165648106063103797 | 14247 | `results/logs/paxos-20260927T230818-r1.log` |
| positive | 3 | success | 28 | -7394619524535080688 | 14247 | `results/logs/paxos-20260927T230821-r1.log` |
| positive | 4 | success | 63 | -1652023382366728610 | 14247 | `results/logs/paxos-20260927T230828-r1.log` |
| positive | 5 | success | 56 | -8036432052181894872 | 14247 | `results/logs/paxos-20260927T231040-r1.log` |
| positive | 6 | success | 22 | 133727571898917963 | 14247 | `results/logs/paxos-20260927T233726-r1.log` |
| mutant | 3 | violation | 112 | -6730006281999691425 | 14247 | `results/logs/paxos-mutant-20260927T231059-r1.log` |
| witness | 2 | violation | 37 | 7202064801940915905 | 14247 | `results/paxos-witness/logs/paxos-witness-20260927T231102-r1.log` |
| witness | 3 | violation | 88 | 903043798033623582 | 14247 | `results/paxos-witness/logs/paxos-witness-20260927T231105-r1.log` |
| witness | 4 | violation | 31 | 6148752159345823495 | 14247 | `results/paxos-witness/logs/paxos-witness-20260927T231106-r1.log` |
| witness | 5 | violation | 85 | -7330318802819205065 | 14247 | `results/paxos-witness/logs/paxos-witness-20260927T231107-r1.log` |
| witness | 6 | violation | 108 | -8227674557129224136 | 14247 | `results/paxos-witness/logs/paxos-witness-20260927T231113-r1.log` |
| witness | 7 | violation | 73 | 7639425086431027480 | 14247 | `results/paxos-witness/logs/paxos-witness-20260927T231144-r1.log` |
| positive | 7 | timeout | 83 | 998027106692881263 | 14247 | `results/logs/paxos-20260928T023927-r1.log` |

**Known gap, for the planner rather than for this task:** `harness/tlc_run.py` records `artifacts.spec` and `artifacts.config` as paths only, with no digest of the module, so a row cannot be tied to the exact text that produced it without this file's word for it, and no row field carries the heap, `-fp` or `-seed` above — they are recoverable only from the committed log banner. A further gap, evidenced by the first N=7 launch: the harness writes its row only *after* a run ends, so a run killed by something outside both TLC and the harness (an OS OOM kill, a caller-side timeout) leaves no row and no log at all, and the record simply stops one instance short. A stop caused by the OS rather than by TLC is invisible to the record unless it is written down by hand, as the sweep-boundary section above does for that launch.
