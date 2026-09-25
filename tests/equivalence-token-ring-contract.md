# Contract: the token-ring equivalence audit

Subject: `docs/equivalence-token-ring.md` — the committed line-correspondence audit between the TLA+
reference semantics and the idiomatic Lean model (protocol §4.1). Owner: planner. Populated by: coder
(once the Lean model exists). Verified by: this contract.

The audit is what makes the Route B model defensible against translation bias: it must map **every**
operator of `specs/tla/token-ring/TokenRing.tla` to its Lean correspondence, name the two tiers, and
state the no-strengthening/no-weakening guarantee. It is pure data — no TLC, no Lean, no network.

## Scenario 1 — every TLA+ operator has a Lean correspondence

- **Actor**: the researcher checking the audit.
- **Boundary**: the committed `docs/equivalence-token-ring.md`.
- **Given**: the file exists.
- **When**: its text is read.
- **Then**: it carries a correspondence **table** — a markdown pipe-table whose header names both
  `TLA+` (or `operator`) and `Lean`, and which is the **first such table** reachable from the top of the
  file (no earlier pipe-table may carry a `TLA+`/`operator` + `Lean` header, so the parser is
  deterministic) — and every token-ring operator — `Nodes`, `TypeOK`, `Init`, `Request`, `Enter`,
  `Release`, `Next`, `Mutex`, `Spec` — is a **row** of that table with a **non-empty** Lean-side entry.
- **Why**: an audit that names the operators in prose but maps none of them is not a line-correspondence
  audit; the table rows are what make §4.1's "statement by statement" checkable rather than aspirational.

## Scenario 2 — the tiers and the faithfulness guarantee are stated

- **Actor**: the researcher.
- **Boundary**: the same file.
- **When**: its text is read.
- **Then**: it names the two Lean statements — `mutex` (the general theorem, all `N`) and `mutex_n0`
  (the `N₀` corollary, tier 1) — and states that the Lean model neither strengthens an assumption nor
  weakens the goal.
- **Why**: the two-tier framing (§2) and the no-strengthen/no-weaken guarantee (§4.1) must be tied to
  the actual Lean statements, not to prose keywords, or the audit could claim the guarantee while
  naming no theorem.

## Expected failure before implementation

`docs/equivalence-token-ring.md` does not exist → `FileNotFoundError` for both scenarios (the "does
not exist yet" row). Observed red run (step-2/3 coder): `FileNotFoundError: …/docs/equivalence-token-ring.md`.

Run with: `nix develop -c pytest tests/test_equivalence_token_ring.py`
