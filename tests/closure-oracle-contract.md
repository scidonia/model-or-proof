# Contract: the file-mode closure oracle

Subject: the D26 closure oracle (`closure_oracle.check`): the three mechanical checks that turn a
file-mode run into "closed". Owner: planner. Implemented by: coder.

"Closed" is demonstrated, not asserted: the candidate must be byte-identical to the seed up to the
theorem's `:=` (no alteration of the statements or definitions), elaborate with `lake env lean`, and
introduce no axioms beyond `{propext, Classical.choice, Quot.sound}`. The axiom check is the
load-bearing one: a `sorry`-carrying file *compiles* and fails only this check.

## Scenario 1 — the positive fixture demonstrates closure

- **Actor**: the harness, after a file-mode run.
- **Boundary**: `closure_oracle.check(candidate, pristine=<recorded pristine text>, package=<pkg dir>,
  theorem=<name>)` — the integrity baseline is the *recorded pristine text*, never a path the prover's
  shell could have edited.
- **Given**: the positive fixture (`proofs/lean/token-ring/reference/SeedWithReferenceProof.lean`) — the
  seed's definitions and statement byte-identical up to `:=`, with a real proof body.
- **When**: checked.
- **Then**: `integrity is True`, `elaborates is True`, `axioms ⊆ {propext, Classical.choice, Quot.sound}`,
  and `closed is True`.

## Scenario 2 — a `sorry`-carrying seed compiles but is not closed

- **Given**: the untouched seed (`proofs/lean/token-ring/TokenRing.lean`) — the theorem is still `sorry`.
- **Then**: `integrity is True`, `elaborates is True`, `axioms` includes `sorryAx`, and `closed is False`.
- **Why**: a `sorry`-carrying file *compiles*; only the axiom set distinguishes it from a closed proof.
  This is the check that makes "demonstrating them all closed" mean something under file + shell access.

## Scenario 3 — an altered prefix fails integrity

- **Given**: a candidate whose text before the theorem's `:=` differs from the seed (e.g. a declaration
  prepended).
- **Then**: `integrity is False` — the violation is *reported*, never silently accepted, so a prover
  cannot weaken the model and prove a different theorem.

The oracle also returns `pristine_sha256`, and `verdict(result, *, seed_intact=True)` refuses a seed that
moved during the check (the CLI reports `seed <path> changed during the check`), so the integrity
baseline is the recorded pristine text, not whatever the working tree currently holds.

## Expected failure before implementation

`closure_oracle` does not exist yet → `ModuleNotFoundError` / `ImportError` (the "does not exist yet"
row). Observed red run: recorded by the coder once observed.

Run with: `nix develop -c pytest tests/test_closure_oracle.py`
