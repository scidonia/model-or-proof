# Contract: the TLC runner

Subject: `harness/tlc_run.py` — running one TLA+ task under TLC and turning the run into a result row
(the schema is `docs/protocol.md` §6). Owner: planner. Implemented by: coder.

The runner is the measuring instrument for Route A. Its whole value is that a row is trustworthy: the
numbers must come from TLC's final summary, a violated invariant must be distinguishable from a
completed proof of the property, and a run that was killed must not be reported as either.

## Scenario 1 — a completed check yields a success row with TLC's final counts

- **Actor**: the researcher running the harness.
- **Boundary**: the `harness.tlc_run` command line (module entry point), its argument being a task
  manifest path.
- **Given**: `specs/tla/token-ring/TokenRing.tla` and `TokenRing.cfg` with `CONSTANT N = 3`, and an
  empty results directory.
- **When**: the runner is invoked once for that task, selecting the `N = 3` instance
  (`--instance 3` — the task ships a second, `N₀` instance, so the single-instance default no longer
  applies).
- **Then**: `results/tlc.jsonl` holds exactly one row with `route: "tlc"`, `outcome: "success"`,
  `tlc.generated = 73`, `tlc.distinct = 36`, `tlc.left = 0`, `tlc.depth = 11`, `tlc.workers = 1`,
  `param_N = 3`, a positive `wall_clock_s`, a `startup_s` no greater than `wall_clock_s`, and a
  `log` artifact path that exists.
- **Why**: the distinct-state and depth counts are the measurement; if the rig cannot reproduce the
  numbers a manual TLC run prints, nothing downstream means anything.

## Scenario 2 — progress lines are never mistaken for the final summary

- **Actor**: the researcher.
- **Boundary**: the log parser, given a captured TLC log.
- **Given**: a captured log that contains `Progress(28) at …: 2,623,897 states generated (2,623,897
  s/min), 337,897 distinct states found` followed later by the run's final
  `73 states generated, 36 distinct states found, 0 states left on queue.`
- **When**: the parser reads the log.
- **Then**: the parsed counts are 73/36/0 — the final summary — and not the progress line's.
- **Why**: TLC emits progress lines with the same phrases as the summary (observed on a real run);
  a parser that takes the first match reports a running count as the answer.

## Scenario 3 — a violated invariant yields a violation row carrying the trace

- **Actor**: the researcher.
- **Boundary**: the same command line, with the mutant task.
- **Given**: `specs/tla/token-ring/TokenRingMutant.tla`, where a node may enter its critical section
  without the token.
- **When**: the runner is invoked for that task.
- **Then**: the row has `outcome: "violation"`, its log artifact exists and contains the invariant
  violation text, and the row records the same `param_N` as the config.
- **Why**: the mutant is the negative control for the whole rig; a runner that cannot tell a
  counterexample from a proof would report the mutant as a success.

## Scenario 4 — a killed run is a timeout, not a verdict

- **Actor**: the researcher.
- **Boundary**: the same command line, with a wall-clock cap.
- **Given**: a stand-in TLC binary that prints a progress line and then sleeps past the cap.
- **When**: the runner is invoked with `--cap-s 1` and `--instance 3` (the task ships two instances;
  the fake binary ignores the spec, but the runner needs an instance selected before it launches).
- **Then**: the row has `outcome: "timeout"`, `tlc` is null (no completed summary), `states_reached`
  carries the distinct-state count from the last progress line (337 897 in the fixture), and neither
  `success` nor `violation` appears in the row; the log artifact exists.
- **Why**: the protocol's timeout policy — a killed run must not be reported as the property
  established or refuted.

## Scenario 5 — a requested TLC profile is checked against what TLC reports

- **Actor**: the researcher measuring a pinned Route A instance.
- **Boundary**: the `harness.tlc_run` command line and its persisted result row/log.
- **Given**: the already-measured fast token-ring `N=3` task, an empty temporary result directory,
  and a local stand-in TLC executable that prints the JVM's delivery line
  `Picked up JAVA_TOOL_OPTIONS: -Xmx14336m`, then the **observed** OpenJDK8 ParallelGC usable-heap
  banner value **12743MB** for a requested `-Xmx14336m`, a completed summary, fp 28 and seed 1.
  The stand-in shape is fixed by the real-token-ring smoke, not invented from the earlier contract
  (`tests/fixtures/fake_tlc_profile.py`).
- **When**: the researcher selects `--instance 3 --heap-mib 14336 --fp-index 28 --seed 1` with that
  executable, under the existing one-worker setting.
- **Then**: one successful row reports 36 distinct states,
  `tlc_profile.requested == {heap_mib: 14336, fp_index: 28, seed: 1}`,
  `tlc_profile.heap_delivery == "-Xmx14336m"` parsed from the JVM's own pickup line, and
  `tlc_profile.observed == {heap_mib: 12743, fp_index: 28, seed: 1}` parsed from TLC's banner.
  **The -Xmx ceiling and the banner's usable maximum are not numerically equal.** `-fp 28 -seed 1`
  reach TLC; the row's existing `peak_rss_mb` remains whole-process *used* memory, not either maximum.
- **Why**: matching the requested maximum to its delivery witness and separately recording the
  usable maximum makes a fixed profile honest on the installed JRE.
- **Expected first failure after this planner-owned revision, before correction**: the current
  runner falsely reports `outcome: error` because it compares the requested 14336 against TLC's
  real/banner 12743 (an assertion on `outcome: success`), not because the CLI or fake is missing.

## Scenario 6 — omitted profile flags remain visibly unset

- **Actor**: the researcher inspecting a legacy-style, unpinned TLC invocation.
- **Boundary**: the same command line/result row.
- **Given**: the same local executable emits a successful banner with effective heap 14247 MiB,
  polynomial index 7, and seed 17 when no flags are requested.
- **When**: the researcher invokes the fast task without any profile flags.
- **Then**: the row succeeds and distinguishes `tlc_profile.requested == {heap_mib: null,
  fp_index: null, seed: null}` from `tlc_profile.observed == {heap_mib: 14247, fp_index: 7,
  seed: 17}`, with `tlc_profile.heap_delivery: null` because no heap was requested. Older rows
  lacking `tlc_profile` mean **not recorded**, not a retrospectively inferred set of null requests.
- **Why**: omitted settings can happen to equal explicitly requested settings without making the
  two measurements the same configuration.
- **Expected first failure after this planner-owned revision, before correction**: the current
  runner's persisted row lacks `tlc_profile.heap_delivery` (`KeyError`); its pre-revision
  red was the entirely missing `tlc_profile` object.

## Scenario 7 — a contradictory banner cannot produce a pinned success

- **Actor**: the researcher attempting a fixed-profile Route A cell.
- **Boundary**: the same command line/result row/log.
- **Given**: the stand-in prints a **correct** JVM `-Xmx14336m` pickup and the corresponding
  12743MB banner, plus a plausible completed 36-state summary, but reports fingerprint index
  **29**, not requested **28**.
- **When**: the researcher invokes `--heap-mib 14336 --fp-index 28 --seed 1`.
- **Then**: the row is `outcome: error`, has no accepted `tlc` summary, preserves
  `tlc_profile.heap_delivery == "-Xmx14336m"`, carries requested fp 28 and observed fp 29,
  gives a diagnostic naming **fp** (not an irrelevant numeric heap mismatch), and retains the log.
- **Why**: an incorrect fingerprint polynomial must not silently settle a different configuration.
- **Expected first failure after planner revision**: missing `heap_delivery` on the row or an error
  naming heap before fp because the old runner compares unlike heap quantities.

## Scenario 8 — a banner alone cannot attest delivery of an explicit heap request

- **Actor**: the researcher attempting a fixed-profile Route A cell.
- **Boundary**: the runner CLI and persisted row/log.
- **Given**: the local fake still reports a 12743MB banner, fp 28 and seed 1 with a complete
  36-state summary, but deliberately **omits** the JVM `Picked up JAVA_TOOL_OPTIONS:` line.
- **When**: the researcher requests `--heap-mib 14336 --fp-index 28 --seed 1`.
- **Then**: `outcome: error`, `tlc: null`, `tlc_profile.requested.heap_mib: 14336`,
  `tlc_profile.observed.heap_mib: 12743`, `tlc_profile.heap_delivery: null`, a heap-delivery
  diagnostic and the raw log. There is **no banner fallback** for a claimed explicit heap.
- **Why**: a banner value can coincidentally resemble a requested maximum without proving that
  this invocation delivered the requested JVM option.
- **Expected first failure before correction**: the current row lacks `heap_delivery` (`KeyError`)
  or, if it gets the field but still trusts a banner echo, incorrectly reports success.

## Scenario 9 — a caller's JVM override cannot defeat the explicitly pinned heap

- **Actor**: the researcher running a pinned Route A cell from a shell with inherited JVM options.
- **Boundary**: `python -m harness.tlc_run` and its persisted row and TLC log.
- **Given**: the caller environment contains `_JAVA_OPTIONS=-Xmx1000m` and
  `JDK_JAVA_OPTIONS=-Xmx1000m`. The stand-in TLC child reads its actual inherited environment:
  if `_JAVA_OPTIONS` reaches it, the fake prints the JVM's second `Picked up _JAVA_OPTIONS:` line
  and the reviewer-measured **958MB** usable heap for this later override; with only the runner's
  `JAVA_TOOL_OPTIONS=-Xmx14336m`, it reports **12743MB**.
- **When**: the researcher selects token-ring N3 with explicit
  `--heap-mib 14336 --fp-index 28 --seed 1`.
- **Then**: the successful row reports 36 distinct states, requested heap 14336, independently
  confirmed `heap_delivery: "-Xmx14336m"`, banner usable heap **12743**, and its raw log has
  **no** `Picked up _JAVA_OPTIONS:` line. Only the TLC child's environment is scrubbed: the
  runner does not change the caller's shell. Without an explicit heap request, the runner retains
  its pre-existing environment behavior.
- **Why**: this OpenJDK8 JVM applies `_JAVA_OPTIONS` *after* `JAVA_TOOL_OPTIONS`; witnessing
  delivery alone cannot establish the heap actually selected if an inherited override survives.
- **Expected first failure before implementation**: the current runner copies all of `os.environ`
  into the TLC child; it appends `outcome: success` with **958MB observed**, so the assertion that
  `tlc_profile.observed.heap_mib == 12743` fails (not a missing fixture or argument).

## Scenario 10 — an unlaunchable TLC binary leaves a diagnosed error row and no metadir

- **Actor**: the researcher launching a TLC row with a mistyped or missing `--tlc-bin` (a typo'd
  path, an absent fixture, a bad nix store path).
- **Boundary**: the runner CLI, its persisted row and its per-invocation state pool.
- **Given**: the token-ring N3 manifest and a `--tlc-bin` naming a path that does not exist.
- **When**: the researcher runs the row.
- **Then**: the invocation **completes normally** rather than crashing — it appends exactly one row
  with `outcome: "error"`, `tlc: null`, and an `error` diagnostic that **names the unlaunchable
  binary**; its CLI exit status is the normal status of a finished row; the row carries its log
  artifact like every other row; and the spec's `.tlc-states/` holds **no new** `run-*` directory,
  because the metadir's `finally` owns the pool from before the launch rather than after it.
- **Why**: a launch failure is a diagnosis about the caller's input, and today it is
  indistinguishable from a crashed harness. The row a reader needs in order to see *what* failed is
  missing, and the pool directory the code's own comment promises never survives a sweep is left
  behind — an empty directory nobody can attribute, in the one place a stale pool would be read as a
  sibling run's sabotage.
- **Expected first failure before correction**: `subprocess.Popen` raises `FileNotFoundError`
  **outside** the `try/finally` whose `finally` removes the metadir, so the CLI exits non-zero with a
  traceback, writes no row at all, and leaves the `run-*` directory in place. Both the row assertion
  and the metadir-set assertion fail, and neither failure is a missing fixture or a bad argument.

**Outcome, and the wording ruling.** The fix landed (`7598cc8`, `harness/tlc_run.py` only) and was
verified independently: `tests/test_tlc_run.py` is `10 passed`, and a direct `--tlc-bin /tmp/no-such-tlc`
run exits **0**, writes one row with `outcome: error`, `tlc: null` and an `error` list led by
`could not launch the TLC binary '/tmp/no-such-tlc': [Errno 2] No such file or directory: …`, writes its
log artifact, and leaves `.tlc-states/` with **0** `run-*` entries before and after. The diagnostic lives
in the **existing** `error` list — the row's 21 keys are identical to the pre-fix row's, so no consumer of
the row schema is affected — and it appears only on the launch-failure path, which is what keeps it from
being a field that is always present. **What is contracted is the form, not the bytes:** the sentence must
lead with a fixed, greppable phrase naming the binary and must carry the operating system's reason after
it. The exact rendering of that reason is left to the platform's exception, because pinning it would make
a libc's wording a contract term and turn a cosmetic change into a re-registration.

## Scenario 11 — a launched run that fails silently names its exit status

- **Actor**: the researcher whose `--tlc-bin` launches but exits non-zero without printing a summary.
- **Boundary**: the runner CLI and the row it persists.
- **Given**: `--tlc-bin /bin/false` with the success node's task and instance — a real launch, exit 1, no
  output.
- **When**: the row is written.
- **Then**: `outcome: error`, `tlc: null`, and the row's `error` **names the exit status**: the diagnostic
  contains the word `exit` and the status, so a reader can tell a silent non-zero exit from a run that
  printed nothing because a budget bound or the harness died.
- **Why**: this is deliberately *not* part of Scenario 10. That path is *no process at all* and now carries
  a sentence; this one is *a process that ran and said nothing*, where `failure_tail` of an empty log is an
  empty list — so the row reports a failure and names nothing. Same shape as every reporting defect this
  round has found: a row that looks handled because its outcome label is right and its reason is absent.
  Observed before the fix was written: `outcome: error`, `error: []`, `tlc: null`, with a log artifact and
  no pool leak, so the metadir half of the launch fix already covers this path.
- **Expected first failure before correction**: the row's `error` is `[]`, so the assertion that it names
  the exit status fails.

This fake is a local parser/provenance substitute; it makes **no** model, network, clock or external
filesystem call. The coder additionally smokes the *actual* measured-fast token-ring N3 with the
explicit chosen profile after implementation to verify the real wrapper's `JAVA_TOOL_OPTIONS` and TLC
banner (outside these deterministic scenarios). Full Paxos N5/N6 remeasurements are acceptance rows,
not pytest fixtures. Do not modify the mutable `tests/` files as a coder.

## Expected failure before implementation

Historical scenarios 1–4 were observed red on unresolved `harness.tlc_run` imports before the runner
existed. Scenarios 5–7 were first red before their CLI implementation and again before the
heap-delivery correction. Scenario 8 is non-vacuous under a faithful reviewer scratch mutation but
**was not observed red before the satisfying code landed**; that failure-first violation remains
reported in the plan/review record rather than silently reclassified as a red. Scenario 9 above
must be observed failing for its specific **ambient override** assertion before its production fix.
Scenario 10's contract and its red are authored now, while the fresh theorem cell runs, because
authoring costs no measurement load; its **fix waits** for that cell to finish and be audited, since it
touches the shared TLC runner and the host must stay serial and unloaded for the cell. Its red is
observed on both assertions — no row written, and a leaked `run-*` metadir — before any implementation.
No scenario explores an unmeasured Paxos instance in pytest.
