# Contract: the Lean prover driver

Subject: `harness/lean_repl.py` — the `Prover` port that speaks the `lean-repl` JSON protocol, and the
artifact-close assertion. Owner: planner. Implemented by: coder.

Route B's "success" must come from the prover reporting no unclosed goals, never from a transcript.
The driver's close-guard and the artifact-close assertion carry that guarantee, and this contract pins
both. No real Lean, no network, and no model are touched: `count_unclosed` is a pure function over
strings, and `LeanReplProver` is exercised against a **scripted responder** (a seam that stands in for
the repl process — the plan's "a scripted lean-repl responder, no real Lean").

## Scenario 1 — `count_unclosed` flags every spelling of an unclosed goal

- **Actor**: the harness, after a run, before it records `success`.
- **Boundary**: `harness.lean_repl.count_unclosed(text)`.
- **Given**: texts containing `sorry`, `sorryAx`, `admit`, `Admitted`, and `axiom`, a text whose proof
  is `trivial`, and texts whose only `sorry` is in a `--` comment, a `/- … -/` block comment, or a
  string literal.
- **When**: `count_unclosed` is applied to each.
- **Then**: the count is positive for every spelling and for a `?ident` metavariable, zero for the clean
  proof, zero for the comment/string-only mentions (including nested `/- … -/` and doc `/--`/`/-!`
  comments), zero for `sorry` inside a longer identifier, and an unterminated literal must not hide a
  real `sorry`.
- **Why**: protocol §8 — the artifact must have zero unclosed goals, and `admit`/`sorryAx`/`Admitted`
  are the same hole under other names; but a `sorry` mentioned only in prose must not refuse a genuinely
  closed proof (and lose its row).

## Scenario 2 — the driver reads the goals the responder reports

- **Actor**: the closure loop, reading the prover.
- **Boundary**: `harness.lean_repl.LeanReplProver(proof, repl_cmd, responder=…)`, `start()`, `goals()`,
  `unclosed()`.
- **Given**: a scripted responder returning `{"proofStatus": "Incomplete", "goals": ["⊢ 0 < 1", "⊢ 1 < 2"]}`.
- **When**: the driver starts and is read.
- **Then**: `goals() == ["⊢ 0 < 1", "⊢ 1 < 2"]` and `unclosed() == 2`.
- **Why**: the loop feeds the current goals to the model; a driver that drops or mangles goals makes the
  model reason about the wrong state.

## Scenario 3 — closure is `goals: []` with a completed status

- **Actor**: the loop.
- **Boundary**: the same driver.
- **Given**: a responder returning `{"proofStatus": "Completed", "goals": []}`.
- **When**: the driver starts.
- **Then**: `unclosed() == 0` — this is the only signal that permits `success`.

## Scenario 4 — the `sorry` shape is not closure

- **Actor**: the loop.
- **Boundary**: the same driver.
- **Given**: a responder returning `{"proofStatus": "Incomplete: contains sorry", "goals": []}` — the
  repl's shape for a proof that ends in `sorry`.
- **When**: the driver starts.
- **Then**: `unclosed() > 0` — an empty goal list with a non-completed status must not count as closure.
- **Why**: this is the close-guard; without it a `sorry`-proved theorem reports `success`.

## Scenario 5 — a malformed response is not closure

- **Actor**: the loop.
- **Boundary**: the same driver.
- **Given**: a responder returning `{"proofStatus": "Completed"}` (no `goals` key).
- **When**: the driver starts.
- **Then**: `unclosed() > 0` — a response the driver could not read is never silently "closed".
- **Why**: a missing `goals` key must not degrade to "no goals"; the driver must refuse rather than
  guess.

## Scenario 6 — an unreadable completion status is a transport refusal, not a Lean one

- **Actor**: the loop, reading the refusals the driver records.
- **Boundary**: the same driver (`LeanReplProver`, `responder=…`, `start()`, `failures`).
- **Given**: a responder returning `{"goals": [], "proofState": 1}` — no `proofStatus` field — or a
  `proofStatus` that is not a string starting `Completed`/`Incomplete` (e.g. `"Weird"`).
- **When**: the driver starts.
- **Then**: `failures` records one entry with `kind == "transport"`, whose message names the unreadable
  status.
- **Why**: an unreadable completion is the rig's fault, not a Lean rejection of a tactic — recording it
  as `lean` teaches the model a false lesson about its own syntax.

## Scenario 7 — a recognised "contains sorry" judgment is a lean refusal

- **Actor**: the loop.
- **Boundary**: the same driver.
- **Given**: a responder returning `{"goals": [], "proofStatus": "Incomplete: contains sorry"}`.
- **When**: the driver starts.
- **Then**: `failures` records one entry with `kind == "lean"`, carrying the "not a closed proof"
  judgment (and the first error when the repl sent one).
- **Why**: `contains sorry` is a recognised Lean judgment — the proof is incomplete, which is the model's
  work, not a transport fault.

## Scenario 8 — a `;`-sequence is handed over parenthesised; other tactics unchanged

- **Actor**: the driver, applying a tactic.
- **Boundary**: `LeanReplProver(…, responder=…).apply(tactic)`, with a responder that captures the payload.
- **Given**: `"skip; skip"`, `"skip"`, and `"exact by\n  omega"`.
- **When**: each is applied.
- **Then**: the repl receives `{"tactic": "(skip; skip)", …}` for the `;`-sequence, and the others
  byte-exact (`"skip"`, `"exact by\n  omega"`).
- **Why**: Lean's `tactic` category does not include `;` (it lives in `tacticSeq`), so `t1; t2` dies at
  the `;`; the parenthesised form parses and runs (probe-backed: `(skip; skip)` runs where `skip; skip`
  dies at `expected end of input`). Parentheses change no semantics; only what the repl is handed is
  wrapped, and the reply itself stays verbatim in transcript and history.

## Expected failure before implementation

`harness.lean_repl` does not exist → `ModuleNotFoundError` for all five scenarios (the "does not exist
yet" row). Observed red run (step-4 coder): `ModuleNotFoundError: No module named 'harness.lean_repl'`
— collection error, scenarios not collected.

Scenarios 6–8 landed **after** their fixes, so their first observed run was green; the genuine reds are
recovered against the pre-change code (temporary revert) and recorded here:
- S6/S7 — the pre-`_status_of` code recorded an unreadable answer as `Lean error: …`; expected red:
  `assert [f["kind"] …] == ["transport"]` fails (it is `["lean"]`).
- S8 — the pre-parenthesisation code handed `skip; skip` over verbatim; expected red:
  `assert seen[-1]["tactic"] == "(skip; skip)"` fails (it is `"skip; skip"`).

Run with: `nix develop -c pytest tests/test_lean_driver.py`
