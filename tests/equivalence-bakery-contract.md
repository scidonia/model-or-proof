# Contract: the Bakery equivalence audit

Subject: `docs/equivalence-bakery.md` — the committed line-correspondence audit between the bounded
atomic-register Bakery (`specs/tla/bakery/Bakery.tla`) and its idiomatic Lean model (protocol §4.1).
Owner: planner. Populated by: coder. Verified by: this contract.

The audit maps every operator of the TLA+ reference to its Lean correspondence, names the general
theorem, and states the no-strengthening/no-weakening guarantee. It is pure data — no TLC, no Lean, no
network.

## Scenario 1 — every operator is a correspondence-table row with a non-empty Lean side

- **Actor**: the researcher checking the audit.
- **Boundary**: the committed `docs/equivalence-bakery.md`.
- **Given**: the file exists.
- **When**: its text is read and the correspondence **table** is parsed (a pipe-table whose header names
  both `TLA+`/`operator` and `Lean`, the first such table from the top).
- **Then**: every Bakery operator — `P`, `TypeOK`, `Init`, `LL`, `SetFlag`, `ChooseTicket`, `Enter`,
  `Exit`, `Next`, `MutualExclusion`, `Spec` — is a row with a **non-empty** Lean-side entry.
- **Why**: the bounded bakery has more operators than token-ring (the flag/ticket registers, the
  doorway and critical-section steps); an operator named in prose but not mapped is not an audit.

## Scenario 2 — the general theorem and the faithfulness guarantee are stated

- **Actor**: the researcher.
- **Boundary**: the same file.
- **When**: its text is read.
- **Then**: it names the general theorem's Lean statement (`mutual_exclusion`) and states that the Lean
  model neither strengthens an assumption nor weakens the goal; it names the `N₀` corollary
  (`mutual_exclusion_n0`) at `N₀ = 9` — Bakery's TLC calibration landed there, so the tier-1 instance is
  fixed.
- **Why**: the two-tier framing (§2) and the no-strengthen/no-weaken guarantee (§4.1) must be tied to the
  actual Lean statement; the corollary is named so a reader does not mistake its absence for an omission.

## Expected failure before implementation

`docs/equivalence-bakery.md` does not exist → `FileNotFoundError` for both scenarios (the "does not exist
yet" row). The observed failure output is recorded here once observed, not merely reported.

Run with: `nix develop -c pytest tests/test_equivalence_bakery.py`
