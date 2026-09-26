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
