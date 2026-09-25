# Contract: the published human-proof baseline

Subject: `results/human.jsonl` — the committed, cited record of the published human-proof experiments
(EWD998, ISoLA 2022 "Trifecta"; Peterson / Bakery / Paxos, IJCAR 2010). Owner: planner. Populated by:
coder (from the pinned upstream sources and the paper quotes). Verified by: this contract.

The human baseline is *published evidence carried as data*, never a measured arm. A record must be
impossible to mistake for a Route A or Route B row, its figures must be quoted from the papers, and its
`artifact_size` must match the committed file it points at. No network, model, or `tlapm` is touched;
every file referenced is committed to the repo.

The file holds one JSON object per line (JSONL). Four records are expected, keyed by `record_id`:
`ewd998`, `ijcar2010-peterson`, `ijcar2010-bakery`, `ijcar2010-paxos`.

Record shape (fields asserted by the scenarios):

```json
{
  "kind": "human_prior_art",
  "record_id": "ewd998",
  "publication": {"title": "…", "authors": ["…"], "venue": "…", "url": "https://…"},
  "source": {"repo": "https://github.com/tlaplus/Examples",
             "commit": "3dfe0087a36ccfc6f8aae7de6621c68e06fab955",
             "ref": "ISoLA2022",
             "upstream_path": "specifications/ewd998/EWD998_proof.tla",
             "license": "MIT",
             "license_source": "…"},
  "machine_checked": false,
  "machine_checked_note": "…",
  "effort": {"unit": "person_days_and_proof_lines", "note": "…"},
  "figures": [
    {"kind": "person_days", "proof": "invariance", "value": 1.0,
     "quote": "The invariance proof itself was written in one person-day …"},
    {"kind": "tlc_distinct_states", "instance": "N=3, K=C=3, Q=9", "value": 1300000,
     "quote": "fixing N = 3, K = C = 3 and Q = 9, tlc finds 1.3 million distinct states and requires 42 seconds"}
  ],
  "artifact_size": [{"path": "specs/tla/ewd998/EWD998_proof.tla", "bytes": 37228, "lines": 863}],
  "line_count_disagreement": "…",
  "never_pooled_with": ["route_a_measured", "route_b_measured"]
}
```

`artifact_size.lines` is the count returned by `Path.read_text().splitlines()`; `bytes` is
`Path.read_bytes()` length. `lines` is a list because a record may span several upstream files.

The `ewd998` record's `figures` carry **both** the machine baseline (kinds `tlc_distinct_states`,
`tlc_wall_clock`, `apalache_wall_clock`) **and** the human effort (`person_days`, `proof_lines`),
each quoted verbatim; the IJCAR records carry `proof_lines` figures only (`effort.unit` is
`"lines_only"`). The Paxos second-refinement figure is `partial: true` ("somewhat over 1000 lines",
proof incomplete — "most of the proof").

The `ewd998` record additionally carries a `calibration` object recording how the published TLC
figures relate to two re-runs of this repo. The published figures (distinct 1.3 M, generated 10.1 M,
depth 60, 42 s) were taken from the pre-widening revision `75f2a7a7369d`; commit `dafe1e5c8a74`
(2023-07-28, `token.pos: {0}` → `Node`) widened `Init` afterwards. The object holds three snapshots,
a machine-checkable `cause`, and the prose `root_cause`:

- `published` — the paper's and the embedded 2021 table's figures (`distinct == 1300000`, …).
- `paper_era` — this repo's re-run of `75f2a7a7369d` (task `ewd998-paper`), which reproduces the
  published figures: `distinct` within ±10 % of 1 300 000.
- `branch_head` — this repo's run of the pinned head `3dfe0087…` (task `ewd998`), drifted larger.
- `cause` — the machine-checkable drift cause: `commit == "dafe1e5c8a742c0515d9477f982815adeae04580"`,
  `date == "2023-07-28"`, and `change == {field: "token.pos", before: "{0}", after: "Node"}` (the
  upstream `Init` widening). Asserted by equality; no prose is parsed.
- `root_cause` — the human-readable sentence documenting the same drift. Required present, but
  documentation only; it is not asserted for meaning (meaning is carried by `cause`).

`calibration` is a published-vs-measured note, not a measured field: it adds no measured key to the
record and does not affect its non-poolability.

## Scenario 1 — every record is a labelled, non-poolable prior-art record

- **Actor**: the researcher reading the baseline.
- **Boundary**: the committed `results/human.jsonl` file.
- **Given**: the file exists.
- **When**: each line is parsed as JSON.
- **Then**: the file holds exactly four records, with `record_id`s `ewd998`, `ijcar2010-peterson`,
  `ijcar2010-bakery`, `ijcar2010-paxos` and no others. Every record has `kind == "human_prior_art"`,
  `machine_checked is False`, a `source` with non-empty `repo`, `commit`, `upstream_path`, `license`,
  a non-empty `figures` list whose entries each have a `kind`, a `value`, and a non-empty `quote`, a
  non-empty `artifact_size`, and `never_pooled_with == ["route_a_measured", "route_b_measured"]`.
  No record contains any measured key — `route`, `tool`, `wall_clock_s`, `startup_s`, `peak_rss_mb`,
  `cost_usd`, `tlc`, `proof`, `outcome`, `repetition`, `tier`, `states_reached`, `cost_basis`,
  `negative_control`.
- **Why**: the baseline may be cited next to Route A/B but never pooled into their statistics; the
  structural marker (`kind` + `machine_checked: false` + the absence of every measured field) is what
  makes a mistaken pooling impossible rather than a matter of discipline.

## Scenario 2 — each recorded artifact size matches the committed file

- **Actor**: the researcher.
- **Boundary**: the committed `results/human.jsonl` and the committed spec files it names.
- **Given**: the file and the named artifacts exist.
- **When**: for every record, every `artifact_size` entry is checked against the file at that repo-relative `path`.
- **Then**: the file exists, and its `bytes` and `lines` equal the recorded values.
- **Why**: the record's own measured size is the durable trace that the figure was taken from a real,
  pinned artifact, not typed from memory.

## Scenario 3 — the published-vs-artifact line-count disagreement is preserved

- **Actor**: the researcher.
- **Boundary**: the same file.
- **Given**: the `ijcar2010-bakery` and `ijcar2010-peterson` records.
- **When**: their `proof_lines` figures are compared to their own `artifact_size` line counts.
- **Then**: the Bakery record's `proof_lines` figure is 800 while its artifact (path ending in
  `Bakery.tla`) has a different line count (383 in the source), and the Peterson record's `proof_lines`
  figure is 130 while its artifact (path ending in `Peterson.tla`) has a different line count (199 in
  the source); each record also has a non-empty `line_count_disagreement` note.
- **Why**: the paper's published line counts and the upstream artifact line counts disagree; both must
  be recorded and never silently reconciled, or a reader will believe one side of the comparison.

## Scenario 4 — person-days only for EWD998, and the TLC anchor is cited

- **Actor**: the researcher.
- **Boundary**: the same file.
- **Given**: the `ewd998` record and the three `ijcar2010-*` records.
- **When**: their figures are inspected.
- **Then**: `ewd998` has a figure of `kind == "person_days"` and a figure of `kind ==
  "tlc_distinct_states"` with `value == 1300000`; none of the `ijcar2010-*` records has a `person_days`
  figure (their `effort.unit` is `"lines_only"`); and the `ijcar2010-paxos` record's
  second-refinement figure (`proof == "second_refinement"`) is marked `partial: true`.
- **Why**: EWD998 is the only publication with effort data; the IJCAR paper reports line counts only,
  so no person-day may be invented for it. The cited 1.3 M figure is the anchor the Route A calibration
  (run separately) is compared against.

## Scenario 5 — the EWD998 TLC figures are reproduced at the paper-era revision and drifted at the pin

- **Actor**: the researcher.
- **Boundary**: the same file.
- **Given**: the `ewd998` record.
- **When**: its `calibration` object is inspected.
- **Then**: `published.distinct == 1300000`; `paper_era.distinct` is a positive integer within ±10 % of
  1 300 000 (the rig reproduces a published number); `branch_head.distinct` is a positive integer
  greater than or equal to `paper_era.distinct` (the widening can only enlarge); and the drift cause is
  carried structurally and machine-checked by equality — a `cause` object with `commit ==
  "dafe1e5c8a742c0515d9477f982815adeae04580"`, `date == "2023-07-28"`, and `change == {field:
  "token.pos", before: "{0}", after: "Node"}`. The `root_cause` prose must be present but is
  documentation only and is not asserted for meaning. The record still carries none of the measured
  keys (Scenario 1).
- **Why**: reproducing the published figures at the paper-era revision is what calibrates the rig
  against external data; the drift at the pin is a measured single-commit cause (`dafe1e5c8a74`), and
  both must be recorded, never reconciled.

## Expected failure before implementation

Scenarios 1–4 fail with `FileNotFoundError` (`results/human.jsonl` does not exist yet) — the
"does not exist yet" row. Scenario 5 fails first with `FileNotFoundError`, then with
`KeyError("calibration")` once the file exists but the paper-era run is not yet measured, and then
with `KeyError("cause")` once `calibration` exists but the structured drift cause is not yet written —
the "behavior exists but the data is missing" rows. After the data is written, the scenarios assert the
invariants above; a record that drops `machine_checked: false`, mis-records an artifact size,
reconciles a line-count disagreement, carries a wrong `cause` (a different commit, date, or
before/after pair), or fails to reproduce the published TLC figure fails.

## Observed red run

The red-run output for these scenarios is recorded in-tree at `docs/red-run-evidence.md`. That
document is a **reconstruction by replay** of the pre-implementation tree (not the original
transcript); its provenance, commands and tree states are stated there. What it records:

- **Stage A** — pre-implementation tree + the two new scenario files (no imported specs, no
  `results/human.jsonl`): Scenarios 1–5 fail with `FileNotFoundError: [Errno 2] No such file or
  directory: '…/results/human.jsonl'` (one failure per scenario; the two new contracts together show
  `7 failed, 1 passed`, the single pass being the cfg contract's token-ring regression scenario).
- **Stage B2** — records written, `calibration` not yet measured: Scenarios 1–4 pass; Scenario 5
  fails with `KeyError: 'calibration'` at `test_human_baseline.py:103` — the "behavior exists but the
  data is missing" row.

After implementation, `nix develop -c pytest -q` reported `15 passed` — the phase's own scenarios plus
the pre-existing suite. The full suite is red on the tree today only because it now also holds the next
slice's pre-implementation scenarios (`tests/test_p1_closeout.py`), which fail by design until that
slice implements.

Run with: `nix develop -c pytest tests/test_human_baseline.py`
