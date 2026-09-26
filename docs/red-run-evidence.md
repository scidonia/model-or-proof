# Red-run evidence for the failure-first pins

Scenarios 6/7 (an unreadable completion is the rig's refusal, not Lean's) and 8 (a `;`-sequence is
handed to the repl parenthesised) were worded *after* the behaviour they pin was implemented, so no
red was available to observe in the ordinary way. The reds below were recovered by reverting the
pre-change code in `harness/lean_repl.py` for one run each and restoring it afterwards - the failed
run is the evidence that the scenario can fail, and the pre-change code is the reason it did.

## S6/S7 (pre-`_status_of`)

Reverted to the pre-change code (one edit in `harness/lean_repl.py`), then:

```
$ nix develop -c pytest -q tests/test_lean_driver.py::test_unreadable_completion_status_is_a_transport_refusal tests/test_lean_driver.py::test_unrecognised_status_string_is_a_transport_refusal
    ]
FAILED tests/test_lean_driver.py::test_unrecognised_status_string_is_a_transport_refusal - AssertionError: [{'kind': 'lean', 'message': "opening x.lean's statement: the repl reports 'Weird', not a closed proof"}]
assert ['lean'] == ['transport']
  
  At index 0 diff: 'lean' != 'transport'
  
  Full diff:
    [
  -     'transport',
  +     'lean',
    ]
2 failed in 0.02s
```
exit code 1

## S8 (pre-parenthesisation)

Reverted to the pre-change code (one edit in `harness/lean_repl.py`), then:

```
$ nix develop -c pytest -q tests/test_lean_driver.py::test_semicolon_sequence_is_handed_over_parenthesised
E         ? -          -
E         + skip; skip

tests/test_lean_driver.py:140: AssertionError
=========================== short test summary info ============================
FAILED tests/test_lean_driver.py::test_semicolon_sequence_is_handed_over_parenthesised - AssertionError: {'tactic': 'skip; skip', 'proofState': 0}
assert 'skip; skip' == '(skip; skip)'
  
  - (skip; skip)
  ? -          -
  + skip; skip
1 failed in 0.02s
```
exit code 1
## Restored

The same file, after restoring the change:

```
$ nix develop -c pytest -q tests/test_lean_driver.py
  - (skip; skip)
  ? -          -
  + skip; skip
1 failed, 11 passed in 0.02s
```
exit code 1

## Findings from the file-mode review

## S5 — pre-fix first-match axiom extraction

Reverted to the pre-change code, then:

```
$ nix develop -c pytest -q tests/test_closure_oracle.py::test_name_less_forgery_is_not_a_report
        result = check(spoof, pristine=seed_text, package=PACKAGE, theorem=THEOREM)
>       assert result["closed"] is False, result
E       AssertionError: {'integrity': True, 'elaborates': True, 'axioms': set(), 'axiom_report': 'ok', ...}
E       assert True is False

tests/test_closure_oracle.py:66: AssertionError
=========================== short test summary info ============================
FAILED tests/test_closure_oracle.py::test_name_less_forgery_is_not_a_report - AssertionError: {'integrity': True, 'elaborates': True, 'axioms': set(), 'axiom_report': 'ok', ...}
assert True is False
1 failed in 2.57s
```
exit code 1

## S6 — pre-fix raw-tail feedback (faithful revert, replacing the earlier mangled attempt)

`file_mode`'s prompt fed the raw tail instead of the oracle's diagnostics, with `errors` still
defined as it was then, so the failure is the behaviour and not a `NameError`:

```
$ nix develop -c pytest -q tests/test_closure_oracle.py::test_file_mode_feedback_carries_the_first_lean_error
  
  Lean did not elaborate the file:
  depends on axioms: [...]
  
  the axiom check did not pass and carried no set to report
  
  Close the theorem in that file.
assert 'bogus_tactic_name' in 'The statement under test:\n\n\n\nYour working file: working.lean (in the current directory).\n\nThe previous round di...pends on axioms: [...]\n\nthe axiom check did not pass and carried no set to report\n\nClose the theorem in that file.'
1 failed in 0.02s
```
exit code 1

The earlier entry for this scenario recorded a `NameError` from a revert that removed the `errors`
definition while the fallback still referenced it. That was a scaffolding failure, not the expected
red, and Main caught it; this entry is the real one.

## The macro-interception attack, observed before its fix

`test_macro_interception_is_not_closed` (planner-authored, the fourth shape of Scenario 5) fails on
the parser-path check: a candidate installing `syntax`/`macro_rules` for `#print axioms` makes the
check read a forged empty set while Lean's own environment would say `sorryAx`. Recorded here by
running it, before the `tools/` API checker exists — the red the fix has to turn green.

```
$ nix develop -c pytest -q tests/test_closure_oracle.py::test_macro_interception_is_not_closed
        spoof = seed_text + (
            '\nsyntax (name := fakeAxiomPrint) "#print" "axioms" ident : command\n'
            'macro_rules (kind := fakeAxiomPrint)\n'
            '  | `(#print axioms $n:ident) => `(command| #eval IO.println "'
            + THEOREM + ' depends on axioms: []")\n'
        )
        result = check(spoof, pristine=seed_text, package=PACKAGE, theorem=THEOREM)
>       assert result["closed"] is False, result
E       AssertionError: {'integrity': True, 'elaborates': True, 'axioms': set(), 'axiom_report': 'ok', ...}
E       assert True is False

tests/test_closure_oracle.py:101: AssertionError
=========================== short test summary info ============================
FAILED tests/test_closure_oracle.py::test_macro_interception_is_not_closed - AssertionError: {'integrity': True, 'elaborates': True, 'axioms': set(), 'axiom_report': 'ok', ...}
assert True is False
1 failed in 2.65s
```
exit code 1
