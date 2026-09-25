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
- **When**: the runner is invoked once for that task.
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
- **When**: the runner is invoked with `--cap-s 1`.
- **Then**: the row has `outcome: "timeout"`, `tlc` is null (no completed summary), `states_reached`
  carries the distinct-state count from the last progress line (337 897 in the fixture), and neither
  `success` nor `violation` appears in the row; the log artifact exists.
- **Why**: the protocol's timeout policy — a killed run must not be reported as the property
  established or refuted.

## Expected failure before implementation

Every scenario fails with an unresolved import (`harness.tlc_run` does not exist), which is the
`does not exist yet` row of the authoring guide. After the first implementation, scenarios 1–4 must
pass, and the observed failure output from the red run is reported with the implementation report.
