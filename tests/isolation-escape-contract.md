# Contract: the isolation-escape test

Subject: the reachability of a prior proof from inside an attempt. Owner: planner. Authored here because the
escape test was commissioned outside the contract path and **no draft reached the tree** — no file, no
artifact, no registered transcript — so there was nothing to adopt.

## What this instrument is for

Both outcomes of the corpus decision need the same evidence: **can an attempt reach a proof it was not
given?** The leak is measured rather than hypothetical, twice over:

- a **tier-2** attempt in the six re-earned arms read **another task's** `TokenRingProved.lean` by absolute
  path — the package had withheld the module correctly, so what leaked was the reachable corpus;
- a **tier-1** attempt in the pilot read its own killed predecessor's working file, also by absolute path.

So this is a **control that fires**: a fixture that attempts the escapes from inside an attempt, a detector
that must catch each one, and a control that must **not** fire when the same reads are legitimate — because
a detector that reports everything is as useless as one that reports nothing.

## The pass condition, stated in three halves

The three are **not substitutes**: a layout blocks the *accidental* read, the audit catches what layout
cannot, and only a boundary makes an absolute path resolve to nothing.

1. **Impossible-by-layout.** A relative path from the attempt's working directory reaches none of the
   repository's templates or results. That is what a cell root outside the repository buys, and it is
   testable by resolving the candidate relative paths and requiring them not to exist.
2. **Detected-by-audit.** Every absolute-path or name-collision read that *can* still be made is classified
   as reuse — `promoted-proof`, `other-transcript`, `foreign-copy` — so the attempt is contaminated and
   excluded rather than pooled. That is what the classifier's path rules buy.
3. **Unreachable-by-boundary.** With the attempt's package mounted and the repository **not** mounted, no
   candidate path — relative walk, guessed absolute path, or a route through the `.lake` symlink — resolves,
   because none of them are there to resolve. **Measured, not assumed:** `docker run --rm --read-only -v
   <package>:/work -w /work alpine` reports `ls: /home/gavin/dev/model-or-proof: No such file or directory`
   while listing the package's own files, and with the repository added as a read-only mount the same probe
   reports it present.

**A layout claim of the weaker kind must never be written as the stronger one**, and neither may a boundary
claim be: the container's filesystem boundary is exactly its mount list plus `--read-only`, and it is *not* a
network boundary — the model call needs the network, so `--network=none` is not part of it. What it does
close is every filesystem route, including the absolute ones a layout cannot touch and the audit can only
catch after the fact.

## Scenario 1 — a relative traversal out of the package, and what the two layouts allow

- **Actor**: an attempt whose working directory is its own package.
- **Given**: the same relative walk — `../../../../proofs/lean/<task>/<Stem>Proved.lean` and the equivalent
  into `results/` — resolved from a package in the **current** in-repository layout and from a package in a
  cell root **outside** the repository.
- **When**: each candidate path is resolved and tested for existence.
- **Then**: in the current layout the walk **reaches the repository** (the escape is available, which is why
  the leak was measured rather than argued); in a rebuilt layout it reaches nothing that exists. This is the
  firing control for the layout half: the first half is only meaningful if it can fail.
- **Why**: it is the one half of the pass condition that a rebuild actually changes, so it is the half that
  grades the rebuild.

## Scenario 2 — an absolute read of another task's proved module is caught

- **Actor**: the audit, over one attempt directory.
- **Boundary**: `scripts.audit_attempts.audit_attempt(directory) -> verdict`.
- **Given**: a tier-2 attempt whose own package correctly withholds `TokenRingProved.lean`, and a transcript
  that reads `<repo>/proofs/lean/token-ring/TokenRingProved.lean` by absolute path — the measured leak.
- **When**: it is audited.
- **Then**: **contaminated**, class `promoted-proof`.
- **Note**: this is a regression test for a fix whose red was observed earlier, not a new red.

## Scenario 3 — a same-named working file in another cell is caught

- **Given**: a transcript reading another cell's `.runs/<stem>-r1.lean` by absolute path, with the reader's
  own `.runs/<stem>-r1.lean` present in its package — the name collision, in the shape the leak arrives in.
- **Then**: **contaminated**, class `foreign-copy`. This is Scenario 7 of the audit contract exercised
  against the leak it was written for rather than against a synthetic one.

## Scenario 4 — the control: the same shapes, legitimately, do not fire

- **Given**: an attempt reading **its own** package's `.runs/<stem>-r1.lean`, and the `<Task>Proved.lean` its
  tier-1 receipt declares, each by absolute path.
- **Then**: **clean**. Without this, Scenarios 2–3 would be satisfied by a classifier that calls any path
  reuse, and the cell's own attempts — which read their own working file constantly — would all be excluded.

## Scenario 5 — unreachable-by-boundary, and the control that makes it meaningful

- **Actor**: the container boundary, as a runner would use it.
- **Boundary**: `docker run --rm --read-only -v <package>:/work -w /work <image>`.
- **Given**: the attempt's package mounted at `/work` and nothing else; and, as the **control**, the same
  container with the repository additionally mounted read-only.
- **When**: the probe tests the candidate escape paths — the repository's absolute path, a relative walk
  upward from `/work`, and the package's own `.lake` symlink — for existence.
- **Then**: without the repository mount, every one of them **fails to resolve** (`No such file or
  directory`), while the package's own files are still readable, so the boundary did not simply hide
  everything; with the repository mounted, the same paths **do** resolve. The control is what distinguishes
  *the boundary hides it* from *the fixture never looked*.
- **Why it matters for the decision**: this is the half a containerised runner buys, and it is the only one
  that addresses the leaks actually measured — both were absolute-path reads, which a rebuilt layout leaves
  untouched and the audit catches only after the fact.
- **Note on the test's own honesty**: this half **asserts** that `docker` is present rather than skipping. A
  skipped boundary test is the blindness the arm exists to remove, and this host has a usable daemon
  (`Docker 28.5.1`, this user in the `docker` group).

## What this instrument cannot see

- It cannot see reachability as a fact about the world. Halves 1 and 3 are properties of the runner's
  configuration, so they are asserted by *constructing* that configuration; half 2 is detection **after** the
  fact — a read that happened is a read, whatever the layout allowed. A file the container does not have
  mounted is not reachable, and a file it does have mounted is, whatever the attempt's record says.
- It cannot distinguish an attempt that read a prior proof **once** from one that read it and failed to
  benefit. Contamination is a property of the transcript, not of the result.
- It says nothing about a read made through a path it cannot place — a relative token with no absolute
  recorded cwd resolves to nothing, and the name rule stands there (audit contract, Scenario 7).
- The container half says nothing about the **network** or about what a model does with a credential it is
  given. It bounds the filesystem only, and only as well as its mount list.
