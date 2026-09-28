# Contract: preparing independent Paxos proof attempts

Owner: planner. Subject: the researcher-facing `python -m harness.attempt_workspace prepare` command, before a `harness.route_b --mode file --reps 1` invocation. The original five-run Paxos pilot is **diagnostic**: later models read/copy earlier `.runs/Paxos-rN.lean` files, and the result is not an independent-cost cell (`plans/2026-09-27-paxos-agreement.md` §D3). This contract prevents that immediate leak without claiming a kernel read sandbox the host does not have.

**Contracted interface:**

```
python -m harness.attempt_workspace prepare \
  --template proofs/lean/paxos --seed Paxos.lean \
  --attempt 1 --workspace-root <private clean workspace root> \
  --results-root <separate results root>
```

It emits one JSON record with `attempt`, absolute `package`, `seed`, `results`, and the copied seed's `seed_sha256`. Attempts are uniquely named (`attempt-001`, `attempt-002`, …); an existing destination is refused, not overwritten. The package copies the exact allowlisted module seed, its `baseline/<seed>` and `seeds.json`, `lakefile.toml`, `lean-toolchain`, and `lake-manifest.json`, and links to the pinned dependency cache (`.lake/packages`) instead of copying ≈7 GB of Mathlib. It does **not** copy the template's `.runs/`, promoted/proved versions of the target, closure copies, results or OMP sessions. The per-attempt `results` directory is outside the prepared package and distinct for every attempt; `harness.route_b` still records one normal row and one OMP session *there*. The seed digest must match the committed source record for every attempt. A missing/dirty seed record fails before the live model starts, never silently re-pins it.

The **per-attempt destinations**, not necessarily the parent directory names supplied as roots,
must be disjoint: `--workspace-root /tmp/x/nest --results-root /tmp/x/nest/inner` is allowed
when the resulting `attempt-001` directories do not nest. The JSON receipt names the seed,
package, result destination and digest; it does not enumerate every metadata file the preparer
validated. A refusal from missing **or non-regular** pinned package metadata has CLI exit code **2**,
not the uncaught-I/O exit code **1**. When two refusal grounds apply at once — an existing destination
*and* an unusable configuration — the status and the absence of residue are what this contract pins;
which of the two reasons is reported is deliberately **not** contracted, so a caller keys off the exit
status rather than the message.

`prepare` is an executable **structural invariant** check rather than a full behavior scenario through a real model: the safety property here is the filesystem input boundary *before* any model session exists. Exercising the model would require a live external system, forbidden in pytest; the implementation session instead performs a throwaway local `lake env`/Lean import smoke on a prepared real Paxos package and later audits real transcripts. The executable scenarios use only pytest `tmp_path`, a local Python subprocess, and a tiny temporary package with a fake local dependency cache — no Lean build, model, network, clock or user filesystem.

## Scenario 1 — a researcher prepares a clean first attempt from a dirty source package

- **Actor**: the researcher starting an R≥5 general-theorem proof cell.
- **Boundary**: `python -m harness.attempt_workspace prepare` and its emitted package/results paths.
- **Given**: a temporary source package with one registered `Paxos.lean` seed/baseline and matching SHA-256, local pinned package metadata and a fake `.lake/packages` dependency directory; it also contains prior `PaxosProved.lean`, `.runs/Paxos-r1.lean`, `.runs/proof_body.txt` and `results/closures/old.lean` bearing a distinct prior-proof marker.
- **When**: the researcher prepares attempt 1 with separate temporary workspace and results roots.
- **Then**: the process succeeds with a JSON descriptor for `attempt-001`; the package's seed and baseline equal the recorded bytes and SHA-256, the pinned dependency cache is reused rather than duplicated, no prior-proof marker or old `.runs`/closure/module artifact exists in the prepared package, and the result root is outside that package.
- **Why**: a fresh `sorry` copy next to a completed proof is not an independent attempt.
- **Expected pre-implementation failure**: the `harness.attempt_workspace` module/CLI does not exist; the command exits nonzero with `No module named harness.attempt_workspace`, rather than producing an attempt descriptor.

## Scenario 2 — the next attempt cannot discover the earlier proof in its own package

- **Actor**: the researcher starting the *next* sample after an attempted closure.
- **Boundary**: the same preparation command for attempt 2.
- **Given**: attempt 1's prepared package has since acquired a completed `Paxos-r1.lean` and a `proof_body.txt` under `.runs/`, and attempt 1's results root holds its closure copy and transcript. The source template and recorded seed digest remain unchanged.
- **When**: the researcher prepares attempt 2 from that same source template, with the same cell/workspace and results roots but a new `--attempt 2`.
- **Then**: attempt 2 has a *different* empty `.runs` and result root; neither its package nor result root contains attempt 1's proof marker; attempt 1's artifacts remain intact for audit, and both attempt descriptors carry the **same** seed digest. A second invocation for the *same* attempt ID refuses rather than overwriting either existing attempt.
- **Why**: `--reps 1` alone sweeps only `<stem>-r*.lean` under the original shared package; it leaves helper files and old closure copies in reach.
- **Expected pre-implementation failure**: the preparer CLI does not exist, so the first attempted preparation exits nonzero before any second descriptor is available.

## Scenario 3 — incomplete pinned package metadata refuses cleanly

- **Actor**: the researcher preparing a proof cell from an incompletely or wrongly provisioned package.
- **Boundary**: the same preparation CLI and its exit status/output directories.
- **Given**: a temporary registered seed and dependency-cache fixture in which a member of the pinned
  package configuration — `lean-toolchain`, `lake-manifest.json` or `lakefile.toml` — has been either
  **removed**, or **replaced by a directory**, before the invocation.
- **When**: the researcher prepares attempt 1, once per (member, mode) pair.
- **Then**: the CLI refuses with exit **2** and its stderr names the offending configuration member;
  neither an attempted package nor an attempted results directory is left behind, and no seed digest is
  quietly re-pinned. An incompletely or wrongly provisioned package is a diagnosed refusal, not an
  unexpected traceback or a result row — and that holds for **every** member of the pinned
  configuration, including the one the package-name lookup reads before the copy step. Node:
  `tests/test_paxos_attempt_isolation.py::test_incomplete_pinned_package_metadata_refuses_cleanly`,
  parameterised over the (member, mode) pairs so each is its own collected node and its own reported
  outcome.
- **Why**: callers must distinguish an invalid source package from a failed run after it starts.
- **Expected pre-correction failure**: `lakefile.toml` is read by the package-name lookup *before* the
  configuration gate, so a **directory** in its place raises `IsADirectoryError` into the generic
  `OSError` handler — exit **1** — while a directory at the other two members is refused with exit
  **2**. The same class of provisioning error would be reported two ways, so the CLI-return-code
  assertion fails on that one node while the other five pass. (The earlier red this scenario carried —
  a *removed* member exiting 1 because it was copied inside the cleanup `try` — is fixed and recorded
  in the plan; a removed `lakefile.toml` already exits 2 through the package-name lookup.)

## Real-cell audit and acceptance, not a pytest mock

After the preparer passes all three scenarios, prepare **five separate packages** from the *same registered seed*, each in a different workspace with a different result/session root; run one detached `harness.route_b --mode file --tier 2 --arms proof+refutation --reps 1 --exploratory` per package under the unchanged 7200s/$50 per-run budgets. The conductor archives the five rows and source/package/seed digests as one named pilot cell without silently merging invocation-local `repetition: 1` values. No earlier result root or closure copy is placed in the new package. Before interpreting its median, an independent reader inspects **every** attempt's complete OMP tool-call transcript, naming the row, session path and every read/copy of an older same-tier working proof, closure copy, reference proof, result or transcript. An observed prior-proof read invalidates that attempt's independent-cost evidence even if `closure.verdict: true`; preserve the row and label it contaminated, **never** pool it or replace it with a cheapest clean closure. A tier-1 corollary intentionally importing the established general theorem is a different, allowed dependency. This gives an **operationally independent, transcript-audited** result, *not* a guarantee that an unsandboxed same-UID shell could not read arbitrary absolute paths (`harness/outside_watch.py:1-11`). Do not launch this cell until corrected-FQN verification and the offline real-package smoke are accepted — the smoke's commands and outputs, including the dead-port proxy run and the zero-`connect` syscall evidence on a prepared package, are recorded in `plans/2026-09-27-paxos-agreement.md`. Old pilot rows remain diagnostic.

**The audit is an acceptance gate, not a courtesy.** No attempt's wall time enters the cell's median,
and no `n0`, parity or ratio arithmetic may consume that median, until the per-attempt audit is
complete and recorded — one line per attempt naming the row, the OMP session path, the tool calls
scanned and a verdict (`clean`, or `contaminated` with the offending command). Because the session
store (`results/omp/`) is gitignored (`.gitignore:10`), the audit's evidence must be committed beside
the rows as a bounded extract — the `results/route-b-cell-reuse.md` precedent — *before* the claim is
published. A scan that only matches `.runs/`-shaped path strings does not satisfy this gate: bare
sibling filenames and dynamically generated shell reads must be matched too — this pilot's
contamination was an explicit `cp Paxos-r1.lean Paxos-r2.lean` inside the permitted `--prefix` area
(`plans/2026-09-27-paxos-agreement.md` §D3), and the published-cell audit's decisive commands were
bare relative filenames inside a `for` loop that the first path-shaped scan missed. An attempt whose
audit is missing or incomplete is *unaudited*, which is not the same as clean, and cannot be counted.
The scan covers **two** channels, not one: prior-proof **reads** of any older same-tier working proof,
promoted target, closure copy, reference proof, result or transcript, and **writes through the shared
`.lake/packages` cache**, which is linked rather than copied and is therefore shared mutable state —
a dependency rebuild or `lake update` by one attempt is visible to the template and to every other
attempt, so each attempt's audit line records whether it wrote there and the cell claims no isolation
from it.

### The audit as a runnable step

`scripts/audit_attempts.py` performs the scan, so the gate is executable and re-runnable rather than a
narrative:

```
python -m scripts.audit_attempts --sessions <root>          # one line per attempt
python -m scripts.audit_attempts --sessions <root> --json    # the committed report
```

`<root>` is either the session root whose direct children are the attempts, or the cell or results
root *above* them — the attempts are found by their `<stem>-<stamp>-r<k>` names, not by a fixed depth.

Exit status **0** means every attempt is clean, **1** means at least one is contaminated, and **2**
means at least one is unaudited — no readable transcript, a session directory whose name does not
identify the attempt, or a transcript that records **no tool calls at all**, since an empty scan is not
evidence of no reuse — with 2 taking precedence so that a missing audit can never be read as a clean
cell.

What is scanned: **every** `toolCall` block in every `*.jsonl` under each attempt directory, not a
search for path-shaped strings. Bare relative filenames, tokens inside dynamically generated shell
loops and tokens inside heredoc bodies all count. Failed calls are scanned too: an attempted read is
evidence about the attempt even when it errored, and a shell redirect creates its target even when the
command then fails.

What counts as a read: the effect of the leading verb on each artifact token. `cat`, `head`, `sed`,
`grep`, `diff`, `cmp` and `sha256sum` read or compare; `cp` and `mv` copy their sources and write their
last argument; `rm` deletes; `ls`, `find`, `stat` and `wc` merely enumerate. An **enumeration is not a
read** — seeing a predecessor's filename in an `ls` does not invalidate an attempt, which is why the
retired pilot's r3, which listed its predecessors and then failed its provider turn, is clean. An
unrecognised verb is reported as a read on purpose: the instrument fails loud, because a missed read is
the failure that matters and an over-reported one costs a human a glance.

An attempt is **contaminated** when a token classified as an earlier attempt's working copy
(`<stem>-r<j>` with `j` below its own repetition), a promoted or closure proof, or another attempt's
transcript is read, copied or compared. Everything else — its own working file, the registered seed and
`baseline/`, the pinned dependency cache, its own scratch files — is reported with its class and effect
and does not invalidate the attempt. Each attempt's line names the session directory and the transcript
paths it scanned; the auditor joins those to the cell's rows.

The committed evidence is the run's output beside the cell's rows — `<cell>/audit.txt` for the
per-attempt lines and `<cell>/audit.json` for the full report — both regenerated by the command above,
so a reviewer re-runs one line rather than trusting a narrative, and the bounded extract survives the
gitignored session store.

Validated against the retired pilot `results/paxos-calibration/omp`, which it reproduces exactly: r1
clean, r2 contaminated (`cat` and `cp Paxos-r1.lean`), r3 clean, r4 contaminated (`cp Paxos-r1.lean`),
r5 contaminated (`cp .runs/Paxos-r4.lean`), exit 1, with the tool-call count summing to 224 across the
five transcripts — the same chain the transcript audit established by hand, found by the matcher rather
than by a path-shaped grep.
