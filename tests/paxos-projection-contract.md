# Contract: Paxos's finite TLC projection and negative control

Subject: the `paxos` task consumed by `python -m harness.tlc_run`, with a new executable projection beside the byte-for-byte IJCAR import. Owner: planner. The runner and row schema already exist; the implementer writes the task, projection, mutant, and configs. The reference artifact is never rewritten.

The ordinary test below checks **structural conformance**, not an entire TLC state graph: exhaustive crossover runs can take up to two hours each and are acceptance measurements, not deterministic unit-test fixtures. A real TLC mutant trace at `N = 3`, `B = 1` and a real completed positive row are mandatory, separately recorded acceptance checks. No mock model, network, wall clock, or external filesystem is used in the executable tests.

## Scenario 1 — a researcher can select the same finite Paxos task across the instance sweep

- **Actor**: the researcher running the existing Route A CLI.
- **Boundary**: `tasks/paxos.json` and its named `PaxosN*.cfg` inputs to that CLI.
- **Given**: the imported `specs/tla/ijcar2010/paxos/Paxos.tla` and `Consensus.tla` remain pinned and immutable.
- **When**: the researcher selects each configured instance `N = 2,…,8` (plus any contiguous extension) from the manifest.
- **Then**: each instance names a distinct existing config whose externally read settings are `SPECIFICATION Spec`, `INVARIANT Consistency`, that `N`, and the *same* constant ballot cap `B = 1`; its corresponding `PaxosN<N>Witness.cfg` instead checks `NoChoice` for an actually reachable decision, and the finite projection (not the imported TLAPS file) is the spec handed to TLC. The manifest's wall-clock cap is 7200 s and its `calibration.n0_rule` explicitly distinguishes the crossing selection from the generic largest-under-cap rule.
- **Why**: the sample axis must be acceptors alone and the positive result must not pass only because no value can be chosen.
- **Expected failure before implementation**: `FileNotFoundError` loading `tasks/paxos.json` (the new task is absent).

## Scenario 2 — the negative-control task keeps the genuine quorum definition but weakens proposal admission

- **Actor**: the researcher selecting `--mutant` in the existing Route A CLI.
- **Boundary**: the same manifest's mutant spec and config.
- **When**: the mutant input is selected.
- **Then**: its config declares `N = 3`, `B = 1`, `INVARIANT Consistency`, and its module exposes the same four-step Paxos state relation and `Consistency` predicate as the positive projection while replacing *only* the `Phase2a` quorum-membership guard `Q ∈ Quorums` with membership in nonempty subsets of `Acceptors`; the config still uses majority `Quorums` for `ChosenIn`. A genuine TLC invocation must produce `outcome: violation` and a trace rather than a successful mutant run before recording the cell.
- **Why**: two different values may be proposed from disjoint singleton responses, while genuine choices still require intersecting majorities.
- **Expected failure before implementation**: `FileNotFoundError` loading the missing manifest (after scenario 1 is added), and then a missing mutant fixture if only the positive task has landed.

The executable tests restrict themselves to structural conformance of configs, schema and the positive/mutant source diff. Verifying a real counterexample trace, a reached choice, and the statistical crossing are the coder's TLC/proof smokes and measured-row audit, not a test that asserts source-string echoes.

## Scenario 3 — the measured crossover cannot be silently relabelled as the budget edge

- **Actor**: the researcher reading the finalized manifest and the recorded calibration.
- **Boundary**: `tasks/paxos.json`, `results/tlc.jsonl`, `results/proof.jsonl`, and the Paxos analysis entry.
- **When**: the selected instance is reported as `n0`.
- **Then**: it is the predeclared log-nearest instance to the measured same-claim theorem-plus-corollary cost, bracketed by adjacent completed **and chosen-value-witnessed** Route A instances, with selected ratio within 2× and both completed rows inside the 2 h cap; a timed-out row never counts as success. If this cannot be established, the task is reported nonviable and **no** crossing `n0` or cost-parity claim is fabricated.
- **Why**: a pair at the resource limit would repeat the known four-task gap, not close it.
- **Expected failure before implementation**: missing calibration rows / missing `n0` (not a test assertion on statistical wall-clock; this is a documented acceptance gate after actual measurement).

The runner accepts `--instance N` and `--mutant` without a new library or CLI mode; separate per-run metadirs prevent a concurrent TLC run from deleting a sibling's state pool. Real measurements run on an otherwise idle fixed host, so run simultaneous TLC calibrations only when disk/CPU isolation is explicitly sufficient.
