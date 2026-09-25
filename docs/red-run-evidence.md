# Observed red runs — `tests/test_ewd998_cfg.py` and `tests/test_human_baseline.py`

Evidence for the reviewer finding "no observed red-run output or implementation report" on the
published-human-baseline phase.

**Provenance, stated plainly.** The phase ran in an earlier session that did not capture its red-run
output in the tree, so this is a **reconstruction by replay**: the committed pre-implementation tree
plus the two scenario files, run under the dev shell. It is *not* the original transcript — the
original run's output was not recorded anywhere. What it is, is the observed output of the
pre-implementation tree states, complete and unedited, and reproducible with the recipe below.

Nothing in the captures below is elided, aggregated or substituted. Each is the raw concatenation of
stdout and stderr for the command it names, with temporary paths as they were. The runs were piped
rather than attached to a terminal, so they carry no colour — and no dev-shell
`warning: Git tree … is dirty` line, because the script enters the dev shell from the `/tmp` trees,
which are not git repositories (that warning does appear when the dev shell is entered from inside
this repository, as in the manual runs the contracts' expected-failure text describes).

`COLUMNS=200` is set by the recipe because pytest truncates its own `FAILED …` summary lines to the
detected terminal width; pinning it keeps them whole. Beyond that, a replay under an attached
terminal, or under a different pytest build, can render spacing, colour and the reported durations
slightly differently. What reproduces is the substance: the per-test failure reason and the counts
(`7 failed, 1 passed`; `2 failed, 1 passed`; `1 failed, 4 passed`). Durations quoted below are one
observed run's and are not a claim about a replay's timing.

## Recipe

The recipe is a committed script: **`docs/redrun-replay.sh`**. From the repository root:

```bash
bash docs/redrun-replay.sh /tmp/redrun-out
```

It needs only `git`, `python3` and the dev shell. `PRE_PHASE` inside the script pins the commit
*before* this phase (`a9275fb`) rather than using `HEAD`, so the recipe still reconstructs the right
tree after the phase is committed. The script:

1. exports that commit to `/tmp/redrun-A` and copies the four scenario files
   (`tests/{ewd998-cfg-contract.md,test_ewd998_cfg.py,human-baseline-contract.md,test_human_baseline.py}`)
   in — **stage A**;
2. copies that tree to `/tmp/redrun-B`, adds `specs/tla/{ewd998,ewd998-paper,ijcar2010}` and writes
   `results/human.jsonl` with the record's top-level `calibration` key removed — **stage B**, the state
   after implementation step 5 and before step 6;
3. runs the three pytest commands with `COLUMNS=200` and writes one capture per stage into the output
   directory.

## Stage A — pre-implementation tree + the two new scenario files

Tree: the `a9275fb` tree with the four scenario files copied in. No imported specs, no
`results/human.jsonl`, and the harness still carrying the singular-only `CFG_CONSTANT_RE`.

```text
$ cd /tmp/redrun-A
$ nix develop -c pytest tests/test_ewd998_cfg.py tests/test_human_baseline.py -q
FF.FFFFF                                                                                                                                                                                         [100%]
=============================================================================================== FAILURES ===============================================================================================
___________________________________________________________________________________ test_ewd998_small_cfg_parses_n3 ____________________________________________________________________________________

    def test_ewd998_small_cfg_parses_n3():
        """Scenario 1: the paper's N = 3 instance parses."""
>       cfg = read_cfg(REPO / "specs" / "tla" / "ewd998" / "EWD998Small.cfg")
              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

tests/test_ewd998_cfg.py:12: 
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
harness/tlc_run.py:86: in read_cfg
    text = Path(config).read_text()
           ^^^^^^^^^^^^^^^^^^^^^^^^
/nix/store/d64q19q1xjdwfhqx6czvrjgrhq0n3lcc-python3-3.14.7/lib/python3.14/pathlib/__init__.py:787: in read_text
    with self.open(mode='r', encoding=encoding, errors=errors, newline=newline) as f:
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 

self = PosixPath('/tmp/redrun-A/specs/tla/ewd998/EWD998Small.cfg'), mode = 'r', buffering = -1, encoding = 'locale', errors = None, newline = None

    def open(self, mode='r', buffering=-1, encoding=None,
             errors=None, newline=None):
        """
        Open the file pointed to by this path and return a file object, as
        the built-in open() function does.
        """
        if "b" not in mode:
            encoding = io.text_encoding(encoding)
>       return io.open(self, mode, buffering, encoding, errors, newline)
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
E       FileNotFoundError: [Errno 2] No such file or directory: '/tmp/redrun-A/specs/tla/ewd998/EWD998Small.cfg'

/nix/store/d64q19q1xjdwfhqx6czvrjgrhq0n3lcc-python3-3.14.7/lib/python3.14/pathlib/__init__.py:771: FileNotFoundError
______________________________________________________________________________________ test_ewd998_cfg_parses_n4 _______________________________________________________________________________________

    def test_ewd998_cfg_parses_n4():
        """Scenario 2: the branch's N = 4 config parses."""
>       cfg = read_cfg(REPO / "specs" / "tla" / "ewd998" / "EWD998.cfg")
              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

tests/test_ewd998_cfg.py:19: 
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
harness/tlc_run.py:86: in read_cfg
    text = Path(config).read_text()
           ^^^^^^^^^^^^^^^^^^^^^^^^
/nix/store/d64q19q1xjdwfhqx6czvrjgrhq0n3lcc-python3-3.14.7/lib/python3.14/pathlib/__init__.py:787: in read_text
    with self.open(mode='r', encoding=encoding, errors=errors, newline=newline) as f:
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 

self = PosixPath('/tmp/redrun-A/specs/tla/ewd998/EWD998.cfg'), mode = 'r', buffering = -1, encoding = 'locale', errors = None, newline = None

    def open(self, mode='r', buffering=-1, encoding=None,
             errors=None, newline=None):
        """
        Open the file pointed to by this path and return a file object, as
        the built-in open() function does.
        """
        if "b" not in mode:
            encoding = io.text_encoding(encoding)
>       return io.open(self, mode, buffering, encoding, errors, newline)
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
E       FileNotFoundError: [Errno 2] No such file or directory: '/tmp/redrun-A/specs/tla/ewd998/EWD998.cfg'

/nix/store/d64q19q1xjdwfhqx6czvrjgrhq0n3lcc-python3-3.14.7/lib/python3.14/pathlib/__init__.py:771: FileNotFoundError
___________________________________________________________________________ test_every_record_is_a_labelled_prior_art_record ___________________________________________________________________________

    def test_every_record_is_a_labelled_prior_art_record():
        """Scenario 1: exactly four labelled, non-poolable prior-art records, no extras."""
>       recs = records()
               ^^^^^^^^^

tests/test_human_baseline.py:32: 
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
tests/test_human_baseline.py:20: in records
    text = HUMAN.read_text()  # FileNotFoundError before the data is written (the expected red run).
           ^^^^^^^^^^^^^^^^^
/nix/store/d64q19q1xjdwfhqx6czvrjgrhq0n3lcc-python3-3.14.7/lib/python3.14/pathlib/__init__.py:787: in read_text
    with self.open(mode='r', encoding=encoding, errors=errors, newline=newline) as f:
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 

self = PosixPath('/tmp/redrun-A/results/human.jsonl'), mode = 'r', buffering = -1, encoding = 'locale', errors = None, newline = None

    def open(self, mode='r', buffering=-1, encoding=None,
             errors=None, newline=None):
        """
        Open the file pointed to by this path and return a file object, as
        the built-in open() function does.
        """
        if "b" not in mode:
            encoding = io.text_encoding(encoding)
>       return io.open(self, mode, buffering, encoding, errors, newline)
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
E       FileNotFoundError: [Errno 2] No such file or directory: '/tmp/redrun-A/results/human.jsonl'

/nix/store/d64q19q1xjdwfhqx6czvrjgrhq0n3lcc-python3-3.14.7/lib/python3.14/pathlib/__init__.py:771: FileNotFoundError
______________________________________________________________________________ test_artifact_sizes_match_committed_files _______________________________________________________________________________

    def test_artifact_sizes_match_committed_files():
        """Scenario 2: each recorded artifact size matches the committed file."""
>       for row in records():
                   ^^^^^^^^^

tests/test_human_baseline.py:55: 
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
tests/test_human_baseline.py:20: in records
    text = HUMAN.read_text()  # FileNotFoundError before the data is written (the expected red run).
           ^^^^^^^^^^^^^^^^^
/nix/store/d64q19q1xjdwfhqx6czvrjgrhq0n3lcc-python3-3.14.7/lib/python3.14/pathlib/__init__.py:787: in read_text
    with self.open(mode='r', encoding=encoding, errors=errors, newline=newline) as f:
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 

self = PosixPath('/tmp/redrun-A/results/human.jsonl'), mode = 'r', buffering = -1, encoding = 'locale', errors = None, newline = None

    def open(self, mode='r', buffering=-1, encoding=None,
             errors=None, newline=None):
        """
        Open the file pointed to by this path and return a file object, as
        the built-in open() function does.
        """
        if "b" not in mode:
            encoding = io.text_encoding(encoding)
>       return io.open(self, mode, buffering, encoding, errors, newline)
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
E       FileNotFoundError: [Errno 2] No such file or directory: '/tmp/redrun-A/results/human.jsonl'

/nix/store/d64q19q1xjdwfhqx6czvrjgrhq0n3lcc-python3-3.14.7/lib/python3.14/pathlib/__init__.py:771: FileNotFoundError
______________________________________________________________________________ test_line_count_disagreement_is_preserved _______________________________________________________________________________

    def test_line_count_disagreement_is_preserved():
        """Scenario 3: the published-vs-artifact line-count disagreement is preserved."""
>       recs = records()
               ^^^^^^^^^

tests/test_human_baseline.py:65: 
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
tests/test_human_baseline.py:20: in records
    text = HUMAN.read_text()  # FileNotFoundError before the data is written (the expected red run).
           ^^^^^^^^^^^^^^^^^
/nix/store/d64q19q1xjdwfhqx6czvrjgrhq0n3lcc-python3-3.14.7/lib/python3.14/pathlib/__init__.py:787: in read_text
    with self.open(mode='r', encoding=encoding, errors=errors, newline=newline) as f:
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 

self = PosixPath('/tmp/redrun-A/results/human.jsonl'), mode = 'r', buffering = -1, encoding = 'locale', errors = None, newline = None

    def open(self, mode='r', buffering=-1, encoding=None,
             errors=None, newline=None):
        """
        Open the file pointed to by this path and return a file object, as
        the built-in open() function does.
        """
        if "b" not in mode:
            encoding = io.text_encoding(encoding)
>       return io.open(self, mode, buffering, encoding, errors, newline)
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
E       FileNotFoundError: [Errno 2] No such file or directory: '/tmp/redrun-A/results/human.jsonl'

/nix/store/d64q19q1xjdwfhqx6czvrjgrhq0n3lcc-python3-3.14.7/lib/python3.14/pathlib/__init__.py:771: FileNotFoundError
________________________________________________________________________ test_person_days_only_for_ewd998_and_tlc_anchor_cited _________________________________________________________________________

    def test_person_days_only_for_ewd998_and_tlc_anchor_cited():
        """Scenario 4: person-days only for EWD998, and the TLC anchor is cited."""
>       recs = records()
               ^^^^^^^^^

tests/test_human_baseline.py:83: 
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
tests/test_human_baseline.py:20: in records
    text = HUMAN.read_text()  # FileNotFoundError before the data is written (the expected red run).
           ^^^^^^^^^^^^^^^^^
/nix/store/d64q19q1xjdwfhqx6czvrjgrhq0n3lcc-python3-3.14.7/lib/python3.14/pathlib/__init__.py:787: in read_text
    with self.open(mode='r', encoding=encoding, errors=errors, newline=newline) as f:
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 

self = PosixPath('/tmp/redrun-A/results/human.jsonl'), mode = 'r', buffering = -1, encoding = 'locale', errors = None, newline = None

    def open(self, mode='r', buffering=-1, encoding=None,
             errors=None, newline=None):
        """
        Open the file pointed to by this path and return a file object, as
        the built-in open() function does.
        """
        if "b" not in mode:
            encoding = io.text_encoding(encoding)
>       return io.open(self, mode, buffering, encoding, errors, newline)
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
E       FileNotFoundError: [Errno 2] No such file or directory: '/tmp/redrun-A/results/human.jsonl'

/nix/store/d64q19q1xjdwfhqx6czvrjgrhq0n3lcc-python3-3.14.7/lib/python3.14/pathlib/__init__.py:771: FileNotFoundError
__________________________________________________________________ test_ewd998_tlc_figures_reproduced_at_paper_era_and_drifted_at_pin __________________________________________________________________

    def test_ewd998_tlc_figures_reproduced_at_paper_era_and_drifted_at_pin():
        """Scenario 5: published TLC figures reproduced at the paper-era revision, drifted at the pin."""
>       ewd = by_id(records(), "ewd998")
                    ^^^^^^^^^

tests/test_human_baseline.py:102: 
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
tests/test_human_baseline.py:20: in records
    text = HUMAN.read_text()  # FileNotFoundError before the data is written (the expected red run).
           ^^^^^^^^^^^^^^^^^
/nix/store/d64q19q1xjdwfhqx6czvrjgrhq0n3lcc-python3-3.14.7/lib/python3.14/pathlib/__init__.py:787: in read_text
    with self.open(mode='r', encoding=encoding, errors=errors, newline=newline) as f:
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 

self = PosixPath('/tmp/redrun-A/results/human.jsonl'), mode = 'r', buffering = -1, encoding = 'locale', errors = None, newline = None

    def open(self, mode='r', buffering=-1, encoding=None,
             errors=None, newline=None):
        """
        Open the file pointed to by this path and return a file object, as
        the built-in open() function does.
        """
        if "b" not in mode:
            encoding = io.text_encoding(encoding)
>       return io.open(self, mode, buffering, encoding, errors, newline)
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
E       FileNotFoundError: [Errno 2] No such file or directory: '/tmp/redrun-A/results/human.jsonl'

/nix/store/d64q19q1xjdwfhqx6czvrjgrhq0n3lcc-python3-3.14.7/lib/python3.14/pathlib/__init__.py:771: FileNotFoundError
======================================================================================= short test summary info ========================================================================================
FAILED tests/test_ewd998_cfg.py::test_ewd998_small_cfg_parses_n3 - FileNotFoundError: [Errno 2] No such file or directory: '/tmp/redrun-A/specs/tla/ewd998/EWD998Small.cfg'
FAILED tests/test_ewd998_cfg.py::test_ewd998_cfg_parses_n4 - FileNotFoundError: [Errno 2] No such file or directory: '/tmp/redrun-A/specs/tla/ewd998/EWD998.cfg'
FAILED tests/test_human_baseline.py::test_every_record_is_a_labelled_prior_art_record - FileNotFoundError: [Errno 2] No such file or directory: '/tmp/redrun-A/results/human.jsonl'
FAILED tests/test_human_baseline.py::test_artifact_sizes_match_committed_files - FileNotFoundError: [Errno 2] No such file or directory: '/tmp/redrun-A/results/human.jsonl'
FAILED tests/test_human_baseline.py::test_line_count_disagreement_is_preserved - FileNotFoundError: [Errno 2] No such file or directory: '/tmp/redrun-A/results/human.jsonl'
FAILED tests/test_human_baseline.py::test_person_days_only_for_ewd998_and_tlc_anchor_cited - FileNotFoundError: [Errno 2] No such file or directory: '/tmp/redrun-A/results/human.jsonl'
FAILED tests/test_human_baseline.py::test_ewd998_tlc_figures_reproduced_at_paper_era_and_drifted_at_pin - FileNotFoundError: [Errno 2] No such file or directory: '/tmp/redrun-A/results/human.jsonl'
7 failed, 1 passed in 0.20s
exit=1
```

## Stage B1 — configs imported, harness regex still `CONSTANT`

Tree: stage B, whose `harness/tlc_run.py` is the pre-phase one —
`CFG_CONSTANT_RE = re.compile(r"(?m)^\s*CONSTANT\s+N\s*=\s*(\d+)")` — with the imported configs
present.

```text
$ cd /tmp/redrun-B
$ nix develop -c pytest tests/test_ewd998_cfg.py -q
FF.                                                                                                                                                                                              [100%]
=============================================================================================== FAILURES ===============================================================================================
___________________________________________________________________________________ test_ewd998_small_cfg_parses_n3 ____________________________________________________________________________________

    def test_ewd998_small_cfg_parses_n3():
        """Scenario 1: the paper's N = 3 instance parses."""
        cfg = read_cfg(REPO / "specs" / "tla" / "ewd998" / "EWD998Small.cfg")
>       assert cfg["param_N"] == 3, cfg
E       AssertionError: {'param_N': None, 'property': 'TerminationDetection'}
E       assert None == 3

tests/test_ewd998_cfg.py:13: AssertionError
______________________________________________________________________________________ test_ewd998_cfg_parses_n4 _______________________________________________________________________________________

    def test_ewd998_cfg_parses_n4():
        """Scenario 2: the branch's N = 4 config parses."""
        cfg = read_cfg(REPO / "specs" / "tla" / "ewd998" / "EWD998.cfg")
>       assert cfg["param_N"] == 4, cfg
E       AssertionError: {'param_N': None, 'property': 'TerminationDetection'}
E       assert None == 4

tests/test_ewd998_cfg.py:20: AssertionError
======================================================================================= short test summary info ========================================================================================
FAILED tests/test_ewd998_cfg.py::test_ewd998_small_cfg_parses_n3 - AssertionError: {'param_N': None, 'property': 'TerminationDetection'}
FAILED tests/test_ewd998_cfg.py::test_ewd998_cfg_parses_n4 - AssertionError: {'param_N': None, 'property': 'TerminationDetection'}
2 failed, 1 passed in 0.02s
exit=1
```

## Stage B2 — human records written, `calibration` not yet measured

Tree: stage B, with `results/human.jsonl` present and its `calibration` key removed. Every
`artifact_size` path in it exists, so the only missing piece is `calibration`.

```text
$ cd /tmp/redrun-B
$ nix develop -c pytest tests/test_human_baseline.py -q
....F                                                                                                                                                                                            [100%]
=============================================================================================== FAILURES ===============================================================================================
__________________________________________________________________ test_ewd998_tlc_figures_reproduced_at_paper_era_and_drifted_at_pin __________________________________________________________________

    def test_ewd998_tlc_figures_reproduced_at_paper_era_and_drifted_at_pin():
        """Scenario 5: published TLC figures reproduced at the paper-era revision, drifted at the pin."""
        ewd = by_id(records(), "ewd998")
>       c = ewd["calibration"]
            ^^^^^^^^^^^^^^^^^^
E       KeyError: 'calibration'

tests/test_human_baseline.py:103: KeyError
======================================================================================= short test summary info ========================================================================================
FAILED tests/test_human_baseline.py::test_ewd998_tlc_figures_reproduced_at_paper_era_and_drifted_at_pin - KeyError: 'calibration'
1 failed, 4 passed in 0.03s
exit=1
```

## Green after implementation (for contrast, not part of the red run)

- `nix develop -c pytest tests/test_human_baseline.py tests/test_ewd998_cfg.py -q` — `8 passed`.
- The phase's full suite was `15 passed` when the phase's implementation finished. The suite is
  currently red only in the *next* slice's scenarios (`tests/test_p1_closeout.py`, its Bakery `N₀`
  scenario awaiting measurement), which are pre-implementation contracts by design and outside this
  phase. `docs/red-run-evidence.md` claims nothing about them.
