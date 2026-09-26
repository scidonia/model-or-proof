# Contract: the extended Route B row

Subject: `harness/closure.py` — the fields the Route B row gains beyond what
`tests/closure-contract.md` already pins: `startup_s`/`proof_s` separation, the `assisted`/
`auxiliary_invariants` seed-diff, the fallback-model flag, empty-content handling, and provider
failures. Owner: planner. Implemented by: coder.

The closure loop is exercised here with a stub prover and a scripted model only (no network, no real
Lean, no model), exactly as the existing closure contract does. **Stub hygiene (D19):** a stub prover's
`apply()` must not close (or raise) on a tactic it does not recognise — since the automation pass runs
first every proof turn, a stub that closes on arbitrary text would end the run before the model's turn
and break the scenario; stubs ignore `harness.closure.AUTOMATION_TACTICS`.

## Scenario 1 — `startup_s` is the prover's controlled ready time, not a definitional split

- **Actor**: the researcher running the closure harness.
- **Boundary**: `harness.closure.run_loop(prover, model, clock=…)`.
- **Given**: a prover whose `start()` advances the clock by a **known** 3.0 s, then reports closed, and
  a clock that only advances when the prover tells it to.
- **When**: the loop runs.
- **Then**: `startup_s == 3.0` (the prover's ready time, independently known) and `proof_s ==
  wall_clock_s − 3.0`.
- **Why**: `startup_s` must be an observed instant, not a partition of the wall-clock — otherwise an
  implementation that sets `startup_s = wall_clock_s` (and `proof_s = 0`) would satisfy the old
  equality and mask a wrong number (§4.6).

## Scenario 2 — `assisted` is a full-body declaration diff, not a `:=`-prefix compare

- **Actor**: the harness, diffing the artifact against the seed.
- **Boundary**: `harness.closure.detect_assisted(seed_text, artifact_text)`.
- **Given**: a seed `theorem mutex … := by sorry`, and artifacts that (a) replace `sorry` with a real
  proof, (b) rewrite `def Mutex : Prop := False` into `:= True`, and (c) add an extra declaration in
  each spelling (`lemma`, `private lemma`, `@[simp] lemma`, `opaque`, `inductive`).
- **When**: `detect_assisted` diffs the declarations by name across their **full body**.
- **Then**: (a) `assisted: false` (faithful closure — the statement is unchanged); (b) `assisted: true`
  (a changed `def` value is a rewrite, not a proof); (c) `assisted: true` for every spelling — including
  **indented** declarations (indentation is styling, never a boundary) and **every declaration kind**
  (`def`/`notation`/`abbrev`/`instance`, not only `theorem`/`lemma`/`axiom`).
- **Why**: the `assisted` label (§11 decision 5) must catch a human-supplied invariant *and* a silently
  rewritten meaning — comparing only up to the first `:=` misses both.

## Scenario 3 — the fallback flag is OR'd across turns, never overwritten

- **Actor**: the researcher.
- **Boundary**: the same entry point.
- **Given**: a prover that closes after two tactics, and a model whose `usage()` reports
  `is_fallback: true` on the first turn and `false` afterwards.
- **When**: the loop runs.
- **Then**: `resolvedModelIsFallback: true` — one fallback turn flags the whole run, even though a later
  turn is primary.
- **Why**: §4.5 — a fallback-served run is reported separately; a flag that records only the *last*
  turn would silently pool a partially-fallback run with the primary model's runs.

## Scenario 4 — empty content is consumed and re-asked; the budget, not an abort, terminates

- **Actor**: the researcher.
- **Boundary**: the same entry point.
- **Given**: a model that returns the empty tactic `""` for two calls then a real tactic (against a
  prover closing after one real tactic), and a model that always returns `""` under a small wall-clock
  cap.
- **When**: the loop runs each.
- **Then**: the first records `outcome: "success"` with `proof.turns == 3` (the empties are consumed and
  re-asked); the always-empty model records `outcome: "timeout"` with `budget_exceeded: "wall_clock"`
  and the empty turns counted — the budget, not a consecutive-empty abort, is the terminator.
- **Why**: a reasoning model can return empty `content`; the loop must consume and re-ask (§6), and the
  run must run until a budget binds so the mutant's `fail_to_close` (a timeout) is reachable.

## Scenario 5 — a mid-run provider failure lands an error row, not a lost budget

- **Actor**: the researcher.
- **Boundary**: the same entry point.
- **Given**: a prover that never closes, and a model that returns a real tactic for two turns then
  raises `ProviderError(402, "credit_balance_exhausted")`.
- **When**: the loop runs.
- **Then**: `outcome: "error"`, `error == {"kind": "provider_failure", "status": 402, "message":
  "credit_balance_exhausted"}`, and `proof.turns == 2` — the row is returned, no exception propagates.
- **Why**: a 402/429/5xx forty turns into a run must cost a recorded row, not a silently wasted budget
  (§2 "anything else is an outcome, not a result").

## Scenario 6 — a prover-side failure lands an error row, not a lost run

- **Actor**: the researcher.
- **Boundary**: the same entry point.
- **Given**: a stub prover that raises `ProverError` from `start()` ("seed failed to load") and another
  that raises it from `apply()` ("step timed out").
- **When**: the loop runs each.
- **Then**: both land `outcome: "error"` with `error == {"kind": "prover_failure", "message": <verbatim>}`;
  the `start()` failure records `proof.turns == 0`, the `apply()` failure `proof.turns == 1` — the row is
  returned, no exception propagates, the consumed budget is recorded.
- **Why**: a step timeout / repl exit / seed-load failure mid-run must cost a recorded row, never a
  silently lost budget (§2, D12).

## Scenario 7 — a mutant that closes is a rig-broken error

- **Actor**: the researcher.
- **Boundary**: the same entry point, with `mutant=True`.
- **Given**: a prover that closes after one tactic, and a model returning `simp`.
- **When**: the loop runs.
- **Then**: `outcome: "error"` with `error.kind == "mutant_closed"` and `row["mutant"] == "closed"` —
  never `success` — and the turns/tokens are kept.
- **Why**: a mutant that closes means the rig is broken; that observation is exactly what must be
  recorded, not reported as a successful proof (§5).

## Scenario 8 — an unreadable artifact is an error, with `assisted` unknown

- **Actor**: the researcher.
- **Boundary**: the same entry point, with a `seed_text` and a nonexistent `artifact_path`.
- **Given**: a prover that closes, and an artifact path that cannot be read after the run.
- **When**: the loop runs and then reads the artifact for the `assisted` diff.
- **Then**: `outcome: "error"` with `error.kind == "artifact_unreadable"` and `assisted is None` — a
  missing artifact is an error, and "no evidence" must not read as "unassisted".
- **Why**: the `assisted` label must never claim a guarantee it could not check (D5/D15).

## Scenario 9 — a machine-checked refutation is accepted on the mutant

- **Actor**: the researcher.
- **Boundary**: `harness.closure.run_loop(…, arms="proof+refutation", mutant=True)`.
- **Given**: a stub prover whose `cmd()` accepts exactly `#eval witness` as a machine-checked witness,
  and a scripted model whose `refute()` returns that command.
- **When**: the loop runs with both arms racing.
- **Then**: `outcome: "refuted"` — a refutation is accepted only because the prover machine-checked it,
  never on the model's say-so.
- **Why**: the refutation arm must be falsifiable and its witness real (§5, D16).

## Scenario 10 — a rejected refutation does not count

- **Actor**: the researcher.
- **Boundary**: the same entry point.
- **Given**: a stub prover whose `cmd()` rejects `#eval rejected`, and a model whose `refute()` returns it.
- **When**: the loop runs under a small wall-clock cap.
- **Then**: `outcome: "timeout"` with `budget_exceeded: "wall_clock"` — a rejected refutation is not
  accepted, and the race runs to the budget rather than fabricating a result.
- **Why**: a "counterexample" the prover did not check must never read as a refutation.

## Scenario 11 — a refutation against a statement TLC says holds is a rig defect

- **Actor**: the researcher.
- **Boundary**: the same entry point, with `mutant=False`.
- **Given**: a stub prover whose `cmd()` accepts a witness, on the positive statement.
- **When**: the loop runs.
- **Then**: `outcome: "error"` with `error.kind == "rig_refutation"` — a witness against a statement the
  reference semantics says holds is the mirror of the mutant-closed defect, and fails loudly.
- **Why**: §5's "a rig that reports success on a mutant is broken" has a symmetric inverse for refutation.

## Scenario 12 — the proof arm plans; the refutation arm does not (an empty plan is re-asked)

- **Actor**: the researcher.
- **Boundary**: `harness.closure.run_loop(…, arms="proof+refutation")`, with a model that has a
  `plan(arm, goals, history)` turn.
- **Given**: a model returning a proof plan, and a model returning `""` once before the real plan.
- **When**: the loop runs.
- **Then**: `row["plan"]["proof"]` is the plan verbatim, `row["plan"]["refutation"] is None` with a
  non-empty `refutation_reason`, and the model's `plan()` is never asked for the `"refutation"` arm; the
  proof plan's empty reply is a consumed turn re-asked with the nudge.
- **Why**: a plan to refute a true statement is known-useless work and conflicts with the arm's
  one-command instruction (D19); the refutation arm's decision is a single command, not a plan.

## Scenario 13 — the automation pass runs first and is recorded when it closes

- **Actor**: the researcher.
- **Boundary**: the same entry point, with a prover whose `apply("aesop")` closes the goal.
- **When**: the loop runs.
- **Then**: `outcome: "success"` with `proof.automation_closed == "aesop"` — the cheap automation pass ran
  before any model call and its closing tactic is recorded.
- **Why**: §5's vacuousness guard needs to know a goal was closed by automation with no induction.

## Scenario 14 — the few-shot examples carry no forbidden hint

- **Actor**: the researcher.
- **Boundary**: the committed, versioned `proofs/lean/token-ring/prompt_examples.lean`.
- **When**: its text is read.
- **Then**: it contains none of `"holds the token"`, `"critical node"`, `TokenRing`, `Reachable`,
  `ringSucc`, `nodeZero` — the token-ring invariant and namespace never appear in the examples.
- **Why**: the user's ruling is that we may invite the activity but never the content; this assertion is
  the durable evidence the prompt never said it (D19).

## Scenario 15 — invited-guess labelling: model-guessed is not assisted, human-supplied is

- **Actor**: the harness, labelling a helper.
- **Boundary**: `harness.closure.detect_assisted(older, newer, human=…)`.
- **Given**: a seed with only the goal theorem, an artifact that adds `lemma inv`, and the same pair with
  the `human` flag flipped.
- **When**: `detect_assisted` diffs them.
- **Then**: `human=False` (the loop's own guess) → `assisted: false` with `auxiliary_invariants == ["inv"]`;
  `human=True` (a helper in the seed beyond the goal) → `assisted: true`.
- **Why**: the experiment's central distinction — a model-guessed helper is the loop's work, a
  human-supplied one is `assisted` (D19).

## Scenario 16 — the refutation arm must not win by proving the statement; hopelessness is recorded

- **Actor**: the researcher.
- **Boundary**: `harness.closure.run_loop(…, arms="proof+refutation")`.
- **Given**: a model whose `refute()` returns the sentinel `"no_witness"`, and a model whose `refute()`
  returns a *proof of the statement* while the prover's `cmd()` rejects it (the negation-wrap does not
  close).
- **When**: the loop runs each, the proof arm closing the true statement.
- **Then**: the first records `outcome: "success"` with `refutation: "no_witness"` (the arm terminates
  cleanly, the race continues on the proof arm); the second records `outcome != "refuted"` — a proposal
  that proves `P` is wrapped in `¬ P` and rejected, so the arm cannot win by proving the thing it must
  refute.
- **Why**: on true statements the arm must be able to declare it cannot find a counterexample, and it must
  never be credited with a refutation for proving the statement (D16).

## Scenario 17 — the OMP session directory is absolute, under the run's session root

- **Actor**: the harness (a run_loop/route_b caller).
- **Boundary**: `harness.model.omp_command(session_root, role)`.
- **Given**: a *relative* `session_root` (`results/omp/run1`) while the process cwd is the repository.
- **When**: `omp_command` builds the command.
- **Then**: the `--session-dir` value is **absolute**, equals `<session_root resolved>/<role>` — the same
  path the port creates for that role.
- **Why**: OMP resolves a relative `--session-dir` against its `--cwd`, silently moving the run's
  transcript outside the durable run directory (the empty-repo-dir bug); a scenario may not drive a real
  model, so the absolute-path property is the pin.

## Scenario 18 — the reply is applied whole; a bare `by` is wrapped as `exact by`

- **Actor**: the loop (extracting a tactic from a model reply).
- **Boundary**: `harness.model.extract_tactic(reply)`.
- **Given**: a reply that is a fenced proof with prose around it (`Here is the proof:\n```lean\nby\n  omega\n```\nThat closes it.`).
- **When**: the tactic is extracted.
- **Then**: the fence and surrounding prose are stripped, the multi-line block is kept **whole** (not
  truncated to its first line), and the bare `by` is wrapped as `exact by\n  omega` — a bare `by` is not
  a standalone tactic (`expected tactic`), so the wrap is the same syntactic normalisation as D16's
  refutation wrap. A single tactic (`induction hs`) and an already-formed `exact by …` pass through
  unchanged.
- **Why**: the whole-reply path must apply the proof the model wrote, not one line of it; silently
  truncating a multi-line sequence to its first line would drop the closing lines with no failure recorded.

## Scenario 19 — the refutation command is not rewritten by the proof-arm wrap

- **Actor**: the loop (extracting a refutation command vs a proof tactic).
- **Boundary**: `harness.model.extract_command(reply)` vs `harness.model.extract_tactic(reply)`.
- **Given**: a `by`-led reply (`by\n  decide`).
- **When**: each is extracted.
- **Then**: `extract_command` leaves it **byte-exact** (`by\n  decide`); `extract_tactic` wraps it
  (`exact by\n  decide`). `no_witness` and a full `example : … := by …` command pass through
  `extract_command` unchanged.
- **Why**: the `exact by` wrap is **proof-arm-only** — `refute()` routes through `extract_command`
  (fence-only), so the negative control's behaviour is unchanged by the whole-reply iteration. This is a
  **behavioural** pin (the wrap does not reach the refutation channel), not a byte-identity claim: the
  batch also rewrote the refutation prompt in an earlier ticket, so byte-identity across the batch is not
  what this scenario claims.

## Scenario 20 — a cut turn records `turn_deadline`, not `provider_failure`

- **Actor**: the researcher.
- **Boundary**: `harness.closure.run_loop(…)`.
- **Given**: a model that raises `ProviderError(0, …, deadline=360.0)` — the per-turn deadline bound.
- **When**: the loop runs.
- **Then**: `outcome: "error"` with `error.kind == "turn_deadline"` — a budget event, never
  `provider_failure` (which stays reserved for the rig failing).
- **Why**: the per-turn deadline is *our* budget choice; a reader must draw the distinction from the row
  alone, the same `lean` vs `transport` separation.

## Expected failure before implementation

The row keys `startup_s`/`proof_s`/`resolvedModelIsFallback`/`error`/`mutant`/`assisted` do not
exist yet → `KeyError` on the returned row; `detect_assisted`/`ProviderError`/`ProverError` do not exist
yet → `AttributeError`/`ImportError`; the `mutant`/`seed_text`/`artifact_path`/`arms` keyword arguments
and the `refute`/`cmd` port methods do not exist yet → `TypeError`/`AttributeError`; the `refuted`
outcome and `rig_refutation` kind do not exist yet. Observed red run (step-5/6 coder): `ImportError:
cannot import name 'detect_assisted' from 'harness.closure'`.

Observed red for S6–S8 (pre-fix, in-process stubs / smoke; the scenarios landed after the fix, so these
are the escapes they now pin):
- S6 prover failure — `run_loop` escaped with `LeanReplError` (`start`: "the repl could not load
  TokenRing.lean: …"; `apply`: "the repl did not answer applying 'simp' within 600s") — the row was lost.
- S8 artifact unreadable — `FileNotFoundError: …/ProofvanishFalse.lean` raised at
  `harness/closure.py:446` (`Path(artifact_path).read_text()`), before route_b's guard — the row was lost.
- S7 mutant closed — reconstructed, labelled in `/tmp/mutant_closed_prefix_repro.py`: pre-fix `run_loop`
  escaped with `MutantClosedError` (protocol §5's rig-broken message) — no row.

Fail-first evidence for S12/S17/S18/S19 — **expected reds, to be recovered against the pre-change code**
(temporary revert of the specific change, not `git show HEAD`, which predates the whole batch and only
ImportErrors). The reds actually recorded at the time (S17 `TypeError: session_root`; S18 `ImportError:
extract_tactic`; S19 first-run green) are scaffolding, not the behaviour failure, and do not count:

- S17 — the pre-`.resolve()` `omp_command` emits a relative `--session-dir`; expected red: `assert
  Path(value).is_absolute()` fails.
- S18 — the pre-wrap extraction returns `by\n  omega`; expected red: `assert extract_tactic(reply) ==
  "exact by\n  omega"` fails.
- S19 — the pre-split `refute()` routes through `extract_tactic` and wraps; expected red: `assert
  extract_command(reply) == "by\n  decide"` fails (it returns `exact by\n  decide`).
- S12 (D19 update) — the pre-D19 loop asks the refutation arm for a plan; expected red: `assert
  "refutation" not in model._asked` fails.

Each recovered red is observed and recorded in `docs/red-run-evidence.md` before the scenario is counted
as protective.

Run with: `nix develop -c pytest tests/test_route_b_row.py`
