# Contract: P1 close-out — `N₀` in the manifests and the Bakery task

Subject: the P1 task manifests (`tasks/token-ring.json`, `tasks/bakery.json`) and the Bakery configs —
the *recorded* `N₀` decisions and the config forms the runner reads. Owner: planner. Populated by:
coder (the calibrated manifests and the bounded Bakery spec/configs). Verified by: this contract.

This is the "calibration landed" contract: it pins that token-ring's `N₀` (settled by arithmetic in
`plans/2026-09-25-p1-closeout.md`) is recorded and runnable, and that the Bakery task — the bounded
atomic-register derivation of the IJCAR 2010 artifact — is complete and calibrated. It is a pure
data/parse contract: it reads JSON manifests and config files through the harness's own
`read_cfg`, and invokes no TLC, no network, and no model. The calibration *runs* themselves are
coder-run steps that append rows; they are not scenarios.

## Scenario 1 — token-ring `N₀` is recorded and runnable

- **Actor**: the researcher reading the task manifest.
- **Boundary**: the committed `tasks/token-ring.json` and the config it points at, via
  `harness.tlc_run.read_cfg`.
- **Given**: the manifest exists.
- **When**: its `n0` field and `instances` are read.
- **Then**: `n0 == 23`; the manifest ships a `param_N == 23` instance whose config parses to
  `param_N == 23` and `property == "Mutex"`; and the `param_N == 3` instance is still present (the
  fast instance the runner scenarios select).
- **Why**: `N₀` is fixed before the result cells (protocol §4.2) and must be the value the calibration
  decided, not left `null`; the `N = 23` instance is how the harness runs the calibrated size, and the
  `N = 3` instance is how the ~1 s scenarios stay fast.

## Scenario 2 — the Bakery manifest is complete and calibrated

- **Actor**: the researcher.
- **Boundary**: the committed `tasks/bakery.json`.
- **Given**: the manifest exists.
- **When**: its fields are read.
- **Then**: it names `specs/tla/bakery/Bakery.tla`, declares property `MutualExclusion` of `kind:
  "safety"`, carries a mutant entry pointing at `BakeryMutant.tla` / `BakeryMutant.cfg`, ships at
  least one instance, and has a positive-integer `n0` (≥ 2) equal to one shipped instance's
  `param_N`.
- **Why**: a Bakery manifest that is missing its mutant or still has `n0: null` means the calibration
  did not land; a `n0` that matches no shipped instance means the calibrated size cannot be run
  through the harness.

## Scenario 3 — the Bakery configs parse

- **Actor**: the researcher.
- **Boundary**: the committed Bakery configs, via `harness.tlc_run.read_cfg`.
- **Given**: the config files exist.
- **When**: each instance config and the mutant config are read.
- **Then**: each instance config parses to its `param_N` and `property == "MutualExclusion"`, and the
  mutant config parses to `property == "MutualExclusion"`.
- **Why**: the runner reads `N` and the invariant name from the config to label the row; if the Bakery
  configs don't parse, the calibration rows would carry the wrong instance or property.

## Expected failure before implementation

- **S1**: `tasks/token-ring.json` currently has `n0: null`, so `assert manifest["n0"] == 23` fails
  (`AssertionError`); the `N = 23` instance and `specs/tla/token-ring/TokenRingN23.cfg` do not exist
  yet, so reading them raises `StopIteration` / `FileNotFoundError`.
- **S2**: `tasks/bakery.json` does not exist → `FileNotFoundError`.
- **S3**: `specs/tla/bakery/*.cfg` do not exist → `FileNotFoundError`.

The observed failure output from the red run is recorded here once observed (in-tree, per the
"Observed red run" convention), not merely reported with the implementation.

Run with: `nix develop -c pytest tests/test_p1_closeout.py`
