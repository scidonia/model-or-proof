# Contract: the cfg parser reads the imported EWD998 config forms

Subject: `harness/tlc_run.read_cfg` — extracting the instance parameter `N` and the invariant name
from a TLC config. Owner: planner. Implemented by: coder.

The imported EWD998 configs use the **block** forms that the token-ring config does not:
`CONSTANTS\n    N = 3` (plural, constant on the following line) and a multi-line `INVARIANT` block.
The runner must read the same `N` and property from these that TLC itself reads, or the EWD998
calibration row would carry the wrong instance. This is a *parse* contract: no TLC is invoked.

## Scenario 1 — the paper's N = 3 instance parses

- **Actor**: the researcher reading a config through the harness.
- **Boundary**: `harness.tlc_run.read_cfg(Path)`.
- **Given**: `specs/tla/ewd998/EWD998Small.cfg` (the imported `CONSTANTS\n    N = 3` config).
- **When**: `read_cfg` reads it.
- **Then**: `param_N == 3` and `property == "TerminationDetection"` (the first invariant of the block).
- **Why**: `EWD998Small.cfg` is the paper's instance (K = C = 3, Q = 9 via `StateConstraint`); if the
  harness reads `N` as `None`, the calibration row claims the wrong instance and the 1.3 M comparison
  is meaningless.

## Scenario 2 — the branch's N = 4 config parses

- **Actor**: the researcher.
- **Boundary**: `harness.tlc_run.read_cfg(Path)`.
- **Given**: `specs/tla/ewd998/EWD998.cfg` (the imported `CONSTANTS\n    N = 4` config).
- **When**: `read_cfg` reads it.
- **Then**: `param_N == 4` and `property == "TerminationDetection"`.
- **Why**: the two configs must be distinguishable by `N` so a reader can tell the paper's N = 3
  instance from the branch's N = 4 one; both share the same block form.

## Scenario 3 — the single-line token-ring form still parses (regression)

- **Actor**: the researcher.
- **Boundary**: `harness.tlc_run.read_cfg(Path)`.
- **Given**: `specs/tla/token-ring/TokenRing.cfg` (`CONSTANT N = 3`, single line).
- **When**: `read_cfg` reads it.
- **Then**: `param_N == 3` and `property == "Mutex"`.
- **Why**: widening the parser to the block form must not break the form the existing tasks use; the
  runner is the one instrument for both.

## Expected failure before implementation

Scenarios 1 and 2 fail with `FileNotFoundError` (the imported config is not committed yet) — the
"does not exist yet" row. After the import but before the regex change they fail with an assertion
(`param_N is None`, because `CONSTANTS` does not match `CONSTANT`). Scenario 3 passes before and after.

## Observed red run

The red-run output for these scenarios is recorded in-tree at `docs/red-run-evidence.md`. That
document is a **reconstruction by replay** of the pre-implementation tree (not the original
transcript); its provenance, commands and tree states are stated there. What it records:

- **Stage A** — pre-implementation tree + the two new scenario files (no imported configs): Scenarios
  1 and 2 fail with `FileNotFoundError: [Errno 2] No such file or directory: '…/specs/tla/ewd998/EWD998Small.cfg'`
  (and `…/EWD998.cfg`); Scenario 3 (the token-ring regression) passes.
- **Stage B1** — configs imported, the harness regex still `CONSTANT`: Scenarios 1 and 2 fail with
  `AssertionError: {'param_N': None, 'property': 'TerminationDetection'}` / `assert None == 3` (and
  `assert None == 4`); Scenario 3 passes.

After implementation, `nix develop -c pytest -q` reported `15 passed` — the phase's own scenarios plus
the pre-existing suite. The full suite is red on the tree today only because it now also holds the next
slice's pre-implementation scenarios (`tests/test_p1_closeout.py`), which fail by design until that
slice implements.

Run with: `nix develop -c pytest tests/test_ewd998_cfg.py`
