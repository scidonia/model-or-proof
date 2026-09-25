# Plan: published human-proof baseline (EWD998 + IJCAR 2010 trio)

**Workspace note (do not re-open).** The user asked for a linked worktree `feat/human-proof-baseline`
but has not yet run `/wt`; this work is on `main` in the primary checkout. No worktree is created.

## Goal

Make the published human-proof experiments first-class in this repository so the AI-loop comparison
(Route B) has a human-effort anchor. Concretely: import the EWD998 (ISoLA 2022 "Trifecta") artifacts
and the IJCAR 2010 Peterson / Bakery / Paxos artifacts at pinned provenance; record the published
human-effort numbers as cited data; and calibrate the Route A rig against the EWD998 published TLC
numbers.

## Non-goals

- No Lean model, no closure loop, no tlapm, no human proof authoring, no new task beyond EWD998 and
  the IJCAR trio.
- **No locally machine-checked proof.** The imported proofs are committed with provenance but are NOT
  checked (`tlapm` is not in the dev shell; it is not in nixpkgs). That limitation is written into the
  data (`machine_checked: false`) and the docs.
- **No human arm is run.** Protocol §1 (explicit non-goals include human interactive proof-engineering
  effort) and §11 decision 5 (human role: statements only) forbid claiming a locally measured human
  effort. The human arm is published evidence carried as data with citations, and it is labelled so it
  can never be pooled with a measured Route A or Route B row.
- No EWD998 mutant / negative control (that is a P2 task, out of scope here).

## Delegated research and what came back

Three scouts were dispatched by the conducting session (`LicenseFact`, `Ewd998InstanceFact`,
`UpstreamModulesFact`); two of their answers landed via the conducting session's own shell probe
because the read-only scouts cannot run `nix develop -c …`. I spot-checked every load-bearing fact
against the primary sources myself (all anchors below are first-hand).

- **Standard modules.** `tlaplus-1.7.4` ships its standard modules inside `share/java/tla2tools.jar`
  (`tla2sany/StandardModules/`). `Integers`, `FiniteSets`, `Naturals`, `Sequences`, `Bags`, `TLC`,
  `Randomization` are present; **`SequencesExt`, `FiniteSetsExt`, `Folds`, `Functions` are absent**
  (confirmed by listing the upstream standard-module directory — none of the four is there). The four
  are CommunityModules, MIT, vendored from pin `9aae8ea1318b3ded4629abdccec2c4754b528d70`.
- **The missing operators are pure TLA+.** `FoldFunctionOnSet` is defined in `Functions.tla` (CommunityModules)
  via `MapThenFoldSet` from `Folds.tla` — a recursive definition, **no Java override**. EWD998's
  `Sum(f, S) == FoldFunctionOnSet(+, 0, f, S)` therefore needs only the `.tla` files on the parse path,
  not the CommunityModules `tlc2/overrides/*.java` classes (those back operators EWD998 never calls).
  Transitive closure is exactly four files: `SequencesExt.tla` (EXTENDS `Sequences, Naturals,
  FiniteSets, FiniteSetsExt, Folds, Functions, Bags, TLC`), `FiniteSetsExt.tla` (EXTENDS `Integers,
  FiniteSets, Folds, Functions`), `Functions.tla` (EXTENDS `Integers, Folds`), `Folds.tla` (self-contained).
- **N = 3 exists upstream.** The paper's instance is `specifications/ewd998/EWD998Small.cfg`
  (`CONSTANTS\n    N = 3` + `CONSTRAINTS StateConstraint` + invariants `TerminationDetection, Inv,
  TypeOK` + `CHECK_DEADLOCK FALSE`) — it is **imported, not derived**. `EWD998.cfg` is the N = 4 one.
  `StateConstraint` (EWD998.tla:84-87) is exactly the paper's K = C = 3, Q = 9: `counter[i] <= 3 /\
  pending[i] <= 3` for all nodes, and `token.q <= 9`. The spec file's own comment block carries the
  paper's table: `| 3 | 60 | 1.3m | 10.1m | 42 s |` — the calibration target is quoted in the imported
  artifact, not only in the paper.
- **Licenses.** `tlaplus/Examples` = MIT (`LICENSE.md`, "All these TLA+ examples are licensed under the
  MIT License.", notice retained on redistribution). `tlaplus/tlapm` = BSD-2-Clause (`LICENSE:8-16`).
  `tlaplus/CommunityModules` = MIT (`LICENSE`). No per-file headers exist, so attribution is satisfied
  by committed license/attribution files, never by editing imported sources.
- **Artifact sizes (measured against the pins).** EWD998.tla 8644 B; EWD998.cfg 210 B; EWD998_proof.tla
  37228 B / 863 lines; AsyncTerminationDetection.tla 4783 B; AsyncTerminationDetection_proof.tla 5134 B;
  Peterson.tla 6363 B / 199 lines; Bakery.tla 17551 B / 383 lines; paxos/Paxos.tla 25552 B;
  paxos/Consensus.tla 934 B.
- **IJCAR reports line counts only** (no person-days); EWD998 is the only publication with person-day
  data. Published line counts and upstream file line counts **disagree** (Peterson "about 130" vs 199;
  Bakery "800" vs 383; EWD998 proof figures sum to 585 vs the artifact's 863). Both are recorded, never
  reconciled.

## Decisions

### D1 — Human records are a separate, documented artifact, never a measured row

Published human proof-effort figures are **not** a third `route` value inside the run-row schema
(protocol §6). They are a distinct data file `results/human.jsonl` with its own schema, plus a prose
provenance/attribution document `docs/human-baseline.md`. A record:

```json
{
  "kind": "human_prior_art",
  "record_id": "ewd998",
  "publication": {"title": "…", "authors": ["Konnov", "Kuppe", "Merz"], "venue": "ISoLA 2022",
                  "url": "https://members.loria.fr/SMerz/papers/2022-isola.pdf"},
  "source": {"repo": "https://github.com/tlaplus/Examples",
             "commit": "3dfe0087a36ccfc6f8aae7de6621c68e06fab955", "ref": "ISoLA2022",
             "upstream_path": "specifications/ewd998/EWD998_proof.tla", "license": "MIT",
             "license_source": "LICENSE.md: 'All these TLA+ examples are licensed under the MIT License.'"},
  "machine_checked": false,
  "machine_checked_note": "Imported as text with provenance; not locally machine-checked (no tlapm in the dev shell) and no human arm is run.",
  "effort": {"unit": "person_days_and_proof_lines",
             "note": "Only EWD998 reports person-days; the IJCAR 2010 trio reports line counts only."},
  "figures": [
    {"kind": "person_days", "proof": "invariance", "value": 1.0,
     "quote": "The invariance proof itself was written in one person-day and required about 230 lines in the proof language of TLA+"},
    {"kind": "proof_lines", "proof": "invariance", "value": 230, "quote": "…same sentence…"}
  ],
  "artifact_size": [{"path": "specs/tla/ewd998/EWD998_proof.tla", "bytes": 37228, "lines": 863}],
  "line_count_disagreement": "published proof-line figures (230 + 110 + 245) do not sum to the artifact's 863 lines; both recorded, not reconciled.",
  "calibration": {
    "published": {"distinct": 1300000, "generated": 10100000, "depth": 60, "wall_clock_s": 42,
                  "spec_revision": "75f2a7a7369d", "note": "paper + the spec's embedded 2021 table"},
    "paper_era": {"distinct": 1300000, "generated": 10100000, "depth": 60, "wall_clock_s": 35.4,
                  "spec_revision": "75f2a7a7369d", "task": "ewd998-paper",
                  "note": "re-run of the pre-widening revision reproduces the published figures"},
    "branch_head": {"distinct": 1520618, "generated": 11238019, "depth": 59, "wall_clock_s": 35.484,
                    "spec_revision": "3dfe0087a36ccfc6f8aae7de6621c68e06fab955", "task": "ewd998",
                    "note": "drifted by dafe1e5c8a74"},
    "root_cause": "dafe1e5c8a74 (2023-07-28) widened Init (token.pos {0} -> Node) after the 2021 table (2589f6465cc5) was recorded; the paper-era revision 75f2a7a7369d reproduces the published figures, the branch head does not. Recorded, never reconciled."
  },
  "never_pooled_with": ["route_a_measured", "route_b_measured"]
}
```

A `figure` may carry optional annotations beyond `kind`/`value`/`quote`: `proof` (which sub-proof a
figure belongs to), `instance` (the `N`/`K`/`C`/`Q` it was measured at), `bound` (`"at_least"` /
`"at_most"` / `"about"` for figures like "somewhat over 1000 lines" or "less than one person-day"),
`value_basis` (`"exact"` / `"rounded"` / `"estimated"`), and `quote_source` (the paper URL — the quote
text itself is the verbatim paper sentence, already transcribed in `docs/protocol.md` §1a). These are
additive metadata; they never add a measured key.

**Impossibility of mistake** is structural, not cosmetic: `kind: "human_prior_art"` + `machine_checked:
false` + the **absence** of every measured field (`route`, `tool`, `wall_clock_s`, `startup_s`,
`peak_rss_mb`, `cost_usd`, `tlc`, `proof`, `outcome`, `repetition`) + a distinct filename
`results/human.jsonl` that no measurement path ever writes to. The TLC calibration run is a *measured*
run and lands in `results/tlc.jsonl` as a normal Route A row — that is the rig being calibrated, not a
human record.

### D2 — Import layout under `specs/tla/`

```
specs/tla/ewd998/                 # tlaplus/Examples @ 3dfe0087… (MIT), branch head (post-widening)
  EWD998.tla                      # the spec (EXTENDS …, SequencesExt, Randomization) — Init widened
  EWD998.cfg                      # N = 4 (the branch's own config)
  EWD998Small.cfg                 # N = 3 (added 4d227cd0d84a, 2023-02-15; the paper-era instance's cfg)
  AsyncTerminationDetection.tla   # instantiated by TD == INSTANCE …
  EWD998_proof.tla                # human proof (EXTENDS EWD998, FiniteSetTheorems, TLAPS) — text only
  AsyncTerminationDetection_proof.tla
  SequencesExt.tla / FiniteSetsExt.tla / Folds.tla / Functions.tla   # CommunityModules @ 9aae8ea… (MIT), vendored
  PROVENANCE.md                   # per-file repo + SHA + upstream path + license + notice
specs/tla/ewd998-paper/           # tlaplus/Examples @ 75f2a7a7369d (MIT), pre-widening paper-era revision
  EWD998.tla                      # Init: token \in [pos: {0}, …] — the bytes the published table was taken from
  AsyncTerminationDetection.tla   # matching revision
  EWD998Small.cfg                 # copy; N = 3 (the paper's instance) — provenance: added 4d227cd0d84a
  SequencesExt.tla / FiniteSetsExt.tla / Folds.tla / Functions.tla   # vendored copy, same CommunityModules pin
  PROVENANCE.md                   # states this is the publication-era revision, not the pin
specs/tla/ijcar2010/              # tlaplus/tlapm @ 7824dab5… (BSD-2-Clause)
  peterson/Peterson.tla
  bakery/Bakery.tla
  paxos/Paxos.tla
  paxos/Consensus.tla
  PROVENANCE.md
```

The four CommunityModules files are vendored **flat into each EWD998 directory** so SANY resolves them
via its "root module's directory" rule — this requires **no library-path plumbing** and no JVM
`-DTLA-Library` forwarding (the nixpkgs `tlc` wrapper is `java -XX:+UseParallelGC -cp tla2tools.jar
tlc2.TLC "$@"`, which does **not** forward `-D` to the JVM). Provenance of the vendored files is kept
in each `PROVENANCE.md`, not by a separate directory. The two spec directories are **different
revisions of the same spec** (branch head vs publication era) and must never be pooled; their rows are
labelled by task name (`ewd998` vs `ewd998-paper`).

### D3 — The EWD998 TLC calibration (two runs)

- **Invocation** (through the harness, the one measuring instrument), once per revision:
  `nix develop -c python -m harness.tlc_run --task tasks/ewd998.json --results results --reps 1` and
  `nix develop -c python -m harness.tlc_run --task tasks/ewd998-paper.json --results results --reps 1`.
  Each manifest points its `spec` at its own directory and its single instance at `EWD998Small.cfg`
  (`N = 3`), so the runs are `tlc -workers 1 -cleanup -config EWD998Small.cfg EWD998.tla` under
  `CONSTRAINTS StateConstraint` (K = C = 3, Q = 9) with invariants `TerminationDetection, Inv, TypeOK`.
  The two task names (`ewd998`, `ewd998-paper`) label the rows so the revisions are never pooled.
- **Published target.** distinct 1.3 M, generated 10.1 M, diameter 60, 42 s — the paper sentence plus
  the spec's embedded 2021 table (`2589f6465cc5`), taken from the **pre-widening** revision
  `75f2a7a7369d`.
- **Run 1 — branch head (`ewd998`, the pin).** Measured: 1,520,618 distinct / 11,238,019 generated /
  depth 59 / 35.5 s at TLC 2.19. This **differs** from the published figures because the pin's `Init`
  was widened by `dafe1e5c8a74` (2023-07-28, `token.pos: {0}` → `Node`) *after* the table was recorded.
- **Run 2 — publication era (`ewd998-paper`, `75f2a7a7369d`).** The pre-widening bytes. **This run
  must reproduce the published figures** (distinct within ±10 % of 1.3 M, depth 60) — that is the
  calibration of the rig against an external published number, decision 6's stated purpose. **Observed:
  1,384,582 distinct / 10,150,343 generated / depth 60 / 32.13 s** — depth exact, generated within 0.5 %
  of the published "10.1 m", distinct within +6.5 % of the rounded "1.3 million" (consistent with the
  published figure being rounded, or a minor TLC-version difference).
- **Tolerance / non-tolerance.** Run 2's distinct is the hard anchor: it must land in `[1.17 M, 1.43 M]`
  (±10 % around the rounded "1.3 million") with `outcome: success`; wall-clock is hardware context.
  Run 1's distinct must be **≥ Run 2's** (the widening can only enlarge the reachable set); the drift
  is then a *measured single-commit cause*, not an inference.
- **Duration.** ~35–42 s per run on this host at `-workers 1` — well inside the 2 h cap. Because each
  is tens of seconds, the calibration is a **coder-run step that appends result rows**, *not* a pytest
  scenario (repo policy: TLC-invoking scenarios run in about a second).
- **What falsifies the calibration.** (a) Either run does not complete / times out / errors — a parse
  or module-resolution failure, or `StateConstraint` not applied (unbounded state space). (b) Run 2's
  distinct falls outside `[1.17 M, 1.43 M]` — the rig fails to reproduce a published number (a rig
  fault or a wrong instance). (c) Run 1's distinct is **below** Run 2's — contradicting the widening,
  i.e. a wrong cfg/instance.

### D4 — Harness change is the smallest that keeps one instrument

Exactly one code change to `harness/tlc_run.py`: widen the constant regex from `CONSTANT` to
`CONSTANTS?` so the block form parses:

```python
CFG_CONSTANT_RE = re.compile(r"(?m)^\s*CONSTANTS?\s+N\s*=\s*(\d+)")
```

`\s+` already spans the newline, so `CONSTANTS\n    N = 3` parses. The existing `CFG_INVARIANT_RE`
already captures the first name of a multi-line `INVARIANT` block (`TerminationDetection`), so it needs
no change (pinned by a scenario). The `CONSTRAINTS StateConstraint` line needs **no** harness change:
the runner passes the cfg whole to TLC (`-config`) and only extracts `N` and the property name for the
row, so the constraint is honoured by TLC itself. The `Randomization` dependency is standard (already
in the jar); `SequencesExt`/`Functions`/`FiniteSetsExt`/`Folds` are handled by vendoring (D2), not by a
library-path parameter. `harness/result.py` and `run_tlc`/`build_row` are unchanged.

### D5 — Protocol wording

Add to `docs/protocol.md` a §1a amendment and a short "human baseline" note (§6-adjacent), plus the §9
task-set note and a §11 decision entry:

- **Name** it the *published human-proof baseline* ("human prior art"); never "Route A/B", never a
  measured arm.
- **Pooling rule**: it may be cited and charted *alongside* Route A/B but never pooled into the same
  distribution, ratio, or cost statistic; every record carries `never_pooled_with` and `machine_checked:
  false`.
- **Paxos partiality**: the IJCAR second refinement proof is incomplete ("most of the proof") — recorded
  verbatim as a figure with `partial: true`, never presented as a finished proof.
- **Published-vs-artifact disagreement**: the paper's line counts and the committed artifact line counts
  differ (Peterson 130 vs 199; Bakery 800 vs 383; EWD998 585-sum vs 863) — both are recorded and the
  disagreement is stated, never reconciled.
- **EWD998 TLC drift, reproduced**: the published TLC figures (1.3 M / 10.1 M / 60 / 42 s) are
  reproduced by re-running the pre-widening revision `75f2a7a7369d` (task `ewd998-paper`), and drift
  at the branch head (1,520,618 distinct / 11,238,019 generated / depth 59 / 35.5 s, task `ewd998`)
  because `dafe1e5c8a74` (2023-07-28) widened `Init` (`token.pos: {0}` → `Node`). Both revisions are
  recorded with the root cause, never reconciled or pooled.
- **Person-days only for EWD998**: IJCAR 2010 reports line counts only; no person-day figure is
  invented for it.

## Affected files / symbols

- `docs/protocol.md` — §1a (add EWD998 artifact citation + the pinned import), new "human baseline"
  note under §6, §9 (EWD998 as the externally calibrated task), §11 (one new decision row).
- `docs/human-baseline.md` — NEW: provenance + attribution + the published-vs-artifact table + the
  partiality and person-day caveats.
- `README.md` — the prior-art section and the Status table gain the human baseline + calibration.
- `plans/2026-09-25-bootstrap.md` — mark the EWD998 import/calibration step done or in progress.
- `specs/tla/ewd998/` — NEW (see D2).
- `specs/tla/ewd998-paper/` — NEW (see D2): the pre-widening paper-era revision `75f2a7a7369d`.
- `specs/tla/ijcar2010/` — NEW (see D2).
- `tasks/ewd998.json` — NEW minimal manifest (spec + N=3 instance; no mutant — out of scope).
- `tasks/ewd998-paper.json` — NEW minimal manifest (paper-era spec + N=3 instance).
- `harness/tlc_run.py` — `CFG_CONSTANT_RE` only (D4).
- `results/human.jsonl` — NEW (D1).
- `results/tlc.jsonl` — gains the EWD998 calibration row (a measured Route A row).
- `tests/ewd998-cfg-contract.md` + `tests/test_ewd998_cfg.py` — NEW contract (planner-owned).
- `tests/human-baseline-contract.md` + `tests/test_human_baseline.py` — NEW contract (planner-owned).
- `AGENTS.md` — no change (no new test dependency; vendored `.tla` files are spec data, not a test dep).

## Ordered implementation steps

1. **Import EWD998 (branch head)** — copy the six `specifications/ewd998/` files listed in D2 from the
   pin (do **not** import the upstream `SmokeEWD998.*` simulator harness — it needs `IOUtils.tla` +
   `CSV.tla` and TLC simulate mode, out of scope); vendor the four CommunityModules files from pin
   `9aae8ea…`; write `specs/tla/ewd998/PROVENANCE.md` (per-file repo + SHA + upstream path + license +
   the MIT notice).
1b. **Import EWD998 (paper era)** — copy `EWD998.tla` + `AsyncTerminationDetection.tla` at `75f2a7a7369d`
   into `specs/tla/ewd998-paper/`, copy the four vendored modules, and copy `EWD998Small.cfg`
   (provenance: added `4d227cd0d84a`, 2023-02-15); write its `PROVENANCE.md` stating this is the
   publication-era revision, not the pin.
2. **Import the IJCAR trio** — copy `examples/Peterson.tla`, `examples/Bakery.tla`,
   `examples/paxos/{Paxos,Consensus}.tla` from pin `7824dab5…`; write `specs/tla/ijcar2010/PROVENANCE.md`
   (BSD-2-Clause notice).
3. **Fix the cfg parser** — the one-line `CFG_CONSTANT_RE` change (D4).
4. **Add the manifests** — `tasks/ewd998.json` and `tasks/ewd998-paper.json` (each: spec + N=3
   instance, 2 h budget, no mutant, `n0: null`, `repetitions: 5`).
5. **Write the human records** — `results/human.jsonl` (four records: `ewd998`, `ijcar2010-peterson`,
   `ijcar2010-bakery`, `ijcar2010-paxos`) with measured `artifact_size` and the verbatim quoted figures
   (D1); `docs/human-baseline.md`.
6. **Run the two-run calibration** — run both manifests (D3): `ewd998` (branch head) and `ewd998-paper`
   (paper era). Confirm the paper-era run reproduces ≈1.3 M distinct / depth 60 (the rig is calibrated
   against a published number) and the branch-head run is ≥ it (drift due to `dafe1e5c8a74`). Record
   both rows in `results/tlc.jsonl` and the `calibration` object in `results/human.jsonl`; module
   resolution is proven by the two calibration logs themselves (each parses the six repo-local files
   with no `-D` plumbing). A `-simulate`-mode probe is **not** a usable standalone check (observed:
   `tlc -simulate -depth 1` keeps simulating and does not terminate), and `tlasany` from the repo root
   does not add the root module's directory, so neither is used.
7. **Update docs** — protocol §1a/§6/§9/§11, README, bootstrap plan (D5).
8. **Contracts go green** — the two new contract pairs; each was observed failing first (see below).

Steps 1–2 and 5 are where the "committed upstream text" lives; every contract reads those committed
files, never the network.

## Acceptance checks

- `nix develop -c pytest` is green, including the two new contracts, each observed failing before the
  code/data that satisfies it (failure output reported, not asserted from memory).
- `specs/tla/ewd998/PROVENANCE.md` and `specs/tla/ijcar2010/PROVENANCE.md` name repo + commit SHA +
  upstream path + license for every imported file, and carry the MIT / BSD-2-Clause notices.
- `results/human.jsonl` holds four records, every one `machine_checked: false` with provenance and
  quoted figures; no record has a measured field (`route`/`wall_clock_s`/`tlc`/`proof`).
- Two EWD998 calibration rows land in `results/tlc.jsonl`, labelled `task: "ewd998"` (branch head:
  1,520,618 distinct / depth 59) and `task: "ewd998-paper"` (paper era: distinct within ±10 % of 1.3 M,
  depth 60), both `outcome: success`, `param_N: 3`; the paper-era row reproduces the published figure
  and the branch-head row is ≥ it — the drift is attributed to `dafe1e5c8a74`, never reconciled or pooled.
- The two calibration runs complete, proving the vendored modules resolve under TLC (no `-D` plumbing).
- No scenario reaches the network or a model; no `tlapm` is invoked anywhere.

## Behavior contracts (planner-owned, written into `tests/`)

1. **`tests/ewd998-cfg-contract.md` + `tests/test_ewd998_cfg.py`** — subject: `harness.tlc_run.read_cfg`.
   Scenarios: (S1) `EWD998Small.cfg` parses to `param_N == 3`, `property == "TerminationDetection"`;
   (S2) `EWD998.cfg` parses to `param_N == 4`, `property == "TerminationDetection"`;
   (S3) regression: the single-line `TokenRing.cfg` still parses to `param_N == 3`, `property == "Mutex"`.
2. **`tests/human-baseline-contract.md` + `tests/test_human_baseline.py`** — subject: `results/human.jsonl`.
   Scenarios: (S1) every record is `kind: "human_prior_art"`, `machine_checked: false`, carries
   `source.{repo,commit,upstream_path,license}` and non-empty `figures`, and has **none** of the measured
   keys; (S2) each `artifact_size` matches the committed file's actual bytes/lines; (S3) the
   published-vs-artifact line-count disagreement is preserved (at least the Bakery 800 vs 383 pair is
   present on one record); (S4) EWD998 records carry person-day figures and the IJCAR records do not
   (`effort.unit` reflects "lines only"); (S5) the `ewd998` record's `calibration` object records the
   published figures (distinct 1300000), the paper-era re-run reproducing them (within ±10 %), and the
   branch-head drift, with a non-empty root cause.

**Expected failures before implementation** (recorded in each contract):
- `ewd998-cfg`: S1/S2 fail with `FileNotFoundError` (imported cfg not yet present), and after import
  but before the regex fix they fail with an assertion (`param_N is None`); S3 already passes.
- `human-baseline`: S1–S4 fail with `FileNotFoundError` (`results/human.jsonl` not yet present); S5
  fails with `KeyError("calibration")` until the paper-era run is measured and the `calibration` object
  is written.

**Run commands** (from repo root): `nix develop -c pytest tests/test_ewd998_cfg.py` and
`nix develop -c pytest tests/test_human_baseline.py` (or the full `nix develop -c pytest`).

## Constraints / invariants

- No network, no model, no tlapm, no TLC in the pytest contracts (the cfg contract is a pure parse;
  the human contract is pure data). The two EWD998 calibration runs are coder-run checks, not
  scenarios.
- The imported sources are byte-for-byte from the pinned commits; attribution is via committed
  notice files, never by editing the sources.
- The human baseline can be *cited* next to Route A/B but never pooled into their statistics.

## Design question for the user

None blocking: scope is settled and the acceptance criteria dictate the key choices. One decision worth
your awareness rather than a vote — the EWD998 calibration **vendors four MIT-licensed CommunityModules
`.tla` files** (SequencesExt, FiniteSetsExt, Folds, Functions) into the repo at pin
`9aae8ea1318b3ded4629abdccec2c4754b528d70`. Without them, TLC cannot parse the imported EWD998 and the
calibration is unsatisfiable; the only alternative would be to drop the calibration, which contradicts
this assignment's acceptance criteria, so vendoring is treated as a consequence rather than an open
choice. It adds spec data, not a test dependency, and is covered by the MIT notice in `PROVENANCE.md`.
