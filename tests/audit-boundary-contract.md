# Contract: the attempt audit's boundary rule

Subject: `scripts/audit_attempts.py`. Owner: planner. Implemented by: coder.

This contract owns the rule that decides, from a completed attempt's transcript, whether it **reused a
prior proof**. It lives here rather than in a contract of its own because the preparer's contract states
the same boundary from the other side (`tests/paxos-attempt-isolation-contract.md`, "The boundary rule,
recorded here because no other contract owns it"), and the two must agree: what the preparer *puts in*
the package is what the audit must *accept as declared*.

## The rule

An attempt is **contaminated** when a token classified `prior-copy`, `promoted-proof` or
`other-transcript` is read, copied or compared — with **one exception, which is the point of this
contract**:

> A `promoted-proof` token whose module is the attempt's **own declared dependency** is the intended
> dependency, not reuse. It is reported with its reason and does not invalidate the attempt.

The distinction is not stylistic. A tier-1 arm exists to instantiate the task's own general theorem: the
preparer copies `<Stem>Proved.lean` into the package precisely so the attempt can import it, and the plan
calls those rows *"intended dependency"* and does not rerun them. Reading **another** task's proved
module, or a tier-2 attempt reading any proved module, remains contamination — for a tier-2 attempt a
completed proof of the attempted theorem must not be in its tree at all.

**Where the declaration comes from, and why it fails closed.** The audit learns it from the attempt's own
row: `tier == 1`, and the `*Proved*.lean` module present in the package the row names
(`artifacts.baseline.seed`'s parent). No row, an unreadable row, `tier != 1`, or no such module in the
package ⇒ **nothing is declared**, and every `promoted-proof` hit invalidates as before. An attempt that
never wrote a row cannot claim a declaration, and a missing declaration is never assumed.

## Scenario 5 — a tier-1 attempt reading its declared dependency is clean, and only that

- **Actor**: the audit, over one attempt directory.
- **Boundary**: `scripts.audit_attempts.audit_attempt(directory) -> verdict`.
- **Given**: four synthetic attempts, each with a transcript whose only artifact-touching call reads a
  `*Proved*.lean` file — (a) tier 1, reading the module the row names as present in its package;
  (b) tier 1, reading a **different** task's proved module; (c) tier 2, reading its own task's proved
  module; (d) tier 1, with **no row at all**.
- **When**: each is audited.
- **Then**: (a) is **clean**, with the hit retained in the report and marked as the declared dependency so
  a reader can see why; (b) is **contaminated**; (c) is **contaminated** — the tier-2 asymmetry, where the
  prior proof must not be present at all; (d) is **contaminated**, because an attempt with no row declares
  nothing.
- **Expected pre-correction failure**: (a) reports `contaminated` today, because the classifier is lexical
  and `promoted-proof` is in `INVALIDATING_CLASSES` with no exception for a declared dependency — so a
  tier-1 cell's every row would be excluded for doing what the receipt told it to do.
- **Why**: the plan sanctions the tier-1 dependency and excludes only undeclared reuse; an audit that
  cannot tell them apart converts the design into an offence, which is the same defect class as a
  synthetic placeholder read as a hole and an absent signal read as a satisfied one.

## Scenario 6 — a prior attempt's row is metadata, and only a transcript is a transcript

- **Actor**: the audit, over one attempt directory.
- **Boundary**: `scripts.audit_attempts.audit_attempt(directory) -> verdict`.
- **Given**: two synthetic attempts, each whose only artifact-touching call reads a `.jsonl` belonging to
  another attempt — (a) that attempt's **row** (`proof.jsonl`), as a path or through a `*.jsonl` glob;
  (b) that attempt's **session transcript** (`<stamp>_<uuid>.jsonl` under its `file/` directory).
- **When**: each is audited.
- **Then**: (a) is **clean**, with the read still listed in the report so a reader can see it — a row is
  the run's *record* (verdict, axioms, paths), not its reasoning and not its proof text, so it is not one
  of the three reuse channels; and (b) is **contaminated**, because another attempt's transcript carries
  that attempt's reasoning, its tool calls and the proof text it worked on.
- **Expected pre-correction failure**: (a) reports `contaminated` today. The classifier returns
  `other-transcript` for **every** `.jsonl` that is not this attempt's own, so the suffix rather than the
  file's kind decides the class, and a model that reads its siblings' rows to understand why they were
  withheld is found to have reused a proof it never read.
- **Why**: the contract's own words are "a `.jsonl` that is not this attempt's own transcript" — the class
  is about transcripts. A rule that classes every `.jsonl` alike is the same over-reach as counting
  `?ident` as a hole and reading an absent signal as a satisfied one: a lexical test standing in for a
  distinction the caller is expected to make. The guard-rail is what keeps the exception honest — a read
  of another attempt's *transcript* must still invalidate, so the fix narrows the class to the file kind
  and does not simply drop it.
