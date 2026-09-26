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
  module=<seed file stem>, theorem=<fully-qualified name>)` — `module` and `theorem` are both **required**
  (no fallback): `module` is the candidate's own module (what it is elaborated as and imported by), and
  `theorem` is the fully-qualified declaration name. The integrity baseline is the *recorded pristine
  text*, never a path the prover's shell could have edited.
- **Given**: the positive fixture (`proofs/lean/token-ring/reference/SeedWithReferenceProof.lean`) — the
  seed's definitions and statement byte-identical up to `:=`, with a real proof body.
- **When**: checked.
- **Then**: `integrity is True`, `elaborates is True`, `axioms ⊆ {propext, Classical.choice, Quot.sound}`,
  and `closed is True`.

## Scenario 2 — a `sorry`-carrying seed compiles but is not closed

- **Given**: the pristine baseline (`proofs/lean/token-ring/baseline/TokenRing.lean`) — the file that keeps
  the `sorry` text forever. After a promotion, "the seed" (proved) and "the pristine baseline" (`sorry`)
  are **different files**, and a `sorry`-based fixture means the baseline.
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

## Scenario 4 — the oracle's `errors` carries the failure, not the axiom report

- **Actor**: the oracle (the `errors` field is the oracle's own contract).
- **Boundary**: `closure_oracle.check` — the `errors` field.
- **Given**: a candidate faithful up to the theorem's `:=` whose body is `exact bogus_tactic_name`.
- **When**: checked.
- **Then**: `integrity is True`, `elaborates is False`, `errors` is **non-empty** and contains
  `bogus_tactic_name`, and no line is a `Note:` line, a warning line (Lean prefixes warnings with the
  file path), or a `depends on axioms` line.
- **Why**: the oracle's `errors` is what a failing round can act on — Lean's own words, not the
  linter/axiom tail that tells it nothing.

The untouched seed's `errors` is **empty** (its `sorry` warning is dropped) while `closed is False` via
`sorryAx` — error recovery leaves the declaration `sorry`-ed, so an unelaborating file still reports
`sorryAx`, which a future reader would otherwise file as a bug.

## Scenario 5 — every interference with the axiom report fails closed (the negative control)

- **Actor**: the harness, before recording `closed`.
- **Boundary**: `closure_oracle.check`, the `axiom_report ∈ {ok, missing, ambiguous}` vocabulary.
- **Given** four forged candidates, each faithful up to `:=` and carrying `sorry`:
  1. a **name-less** forgery — `#eval IO.println "depends on axioms: []"` (no theorem name);
  2. a **named** forgery — `#eval IO.println "TokenRing.mutex depends on axioms: []"`;
  3. a **suppressed** report — an unterminated comment that swallows the rest of the file;
  4. a **macro-interception** — the candidate installs `syntax`/`macro_rules` for `#print axioms ident`.
- **When**: each is checked.
- **Then**: `closed is False` in all four. The API checker reads the axiom set from the *elaborated
  environment*, not from output, so an injected `#eval`/`#print` line — name-less (1) or named (2) — is
  ignored: `axiom_report: "ok"`, `axioms` includes `sorryAx`. The macro-interception (4) is refused the
  same way — the checker has no matchable syntax, so `sorryAx` is read. The suppression (3) does not
  elaborate, so there is no olean and no set: `axiom_report: "missing"`, `axioms is None`. The
  `"ambiguous"` value stays in the vocabulary but no longer occurs — a checker that never parses
  candidate source cannot be shown two reports, so the injection is caught by going to the API, not by
  counting reports.
- **Why**: the only path to `closed` is to actually prove the theorem — spoofing cannot pay.

## Scenario 6 — the next prompt carries the first Lean error (file-mode feedback)

- **Actor**: the model, on its next turn after a failed round.
- **Boundary**: `harness.file_mode.run_file(…)` with a scripted session that records the prompts it is
  handed, and a scripted `closure_oracle.check` returning a fixed failed result (no real Lean).
- **Given**: the oracle reports an error naming `bogus_tactic_name`.
- **When**: the loop runs a round and builds the retry prompt.
- **Then**: the session's **next** prompt leads with `bogus_tactic_name` (the errors lead); the linter's
  `Note:` lines are never shown, and an unusable or absent axiom report (`missing`/`ambiguous`) produces
  no `depends on axioms` sentence — the harness says it cannot read the report rather than inventing one.
- **Why**: a failing round must be told *why* it failed — the errors are what the model can act on; the
  appended axiom/linter tail is what used to be shown instead.
- **Expected red (before the fix)**: the feedback was the raw tail, so the next prompt does not contain
  the identifier — recovered by temporarily restoring the pre-fix feedback path.

## Expected failure before implementation

`closure_oracle` does not exist yet → `ModuleNotFoundError` / `ImportError` (the "does not exist yet"
row). Observed red run: recorded by the coder once observed.

Run with: `nix develop -c pytest tests/test_closure_oracle.py`
