# Contract: Paxos agreement's two-layer equivalence audit

Subject: `docs/equivalence-paxos.md`; owner: planner, filled in by the implementer after the finite projection and Lean models exist. The IJCAR import remains byte-for-byte unchanged. This audit has TWO correspondences, unlike the repository's one-layer audits: original Paxos → executable finite TLC projection → Lean unbounded-ballot model.

The executable checks below cover **structural completeness of the correspondence tables** (the admissible non-BDD case: the subject is an audit document). They do not prove semantic equivalence by matching strings. Semantic evidence comes from line-by-line review and real TLC/mutant observations, not a test that counts prose.

## Scenario 1 — a researcher can locate every safety-relevant semantic clause on both sides of the projection

- **Actor**: the researcher auditing the imported Paxos proof against its executable TLC input.
- **Boundary**: the committed `docs/equivalence-paxos.md` and the immutable imported files.
- **When**: the researcher reads the original-to-projection correspondence table.
- **Then**: the table maps **all 21 executable/operator-domain clauses** `Acceptors`, `Values`, `Quorums`, `QuorumAssumption`, `Ballots`, `vars`, `Send`, `None`, `Init`, `Phase1a`, `Phase1b`, `Phase2a`, `Phase2b`, `Next`, `Spec`, `VotedForIn`, `ChosenIn`, `Chosen`, `Consistency`, `Messages`, `TypeOK` to concrete lines in the projection, naming what is identical and what is restricted. The imported proof-only `WontVoteIn`, `SafeAt`, `MsgInv`, `AccInv`, `Inv`, `Invariant`, `Consistent`, and refinement definitions/theorem are separately classified as not part of the TLC checking predicate rather than silently dropped; `NoChoice` is a new diagnostic predicate only. In particular the audit states `Ballots = 0..B ⊆ Nat` at B=1 for Route A, finite majority quorums, two values, and the non-value sentinel: the projection removes transitions but admits no trace forbidden by the original when the original's constants take those values, and does not change agreement. The imported TLAPS proof text itself has not been TLC-checked.
- **Why**: otherwise a finite checker might solve an easier, different system while inheriting the IJCAR citation.
- **Expected failure before implementation**: `FileNotFoundError` for the missing audit file.

## Scenario 2 — a researcher can locate every projected action and the full unbounded Lean agreement claim

- **Actor**: the researcher auditing Route B against the reference transitions.
- **Boundary**: the same committed audit and the Lean theorem declarations.
- **When**: the researcher reads the projection-to-Lean correspondence table and the theorem statement.
- **Then**: each of the 21 executable clauses above has a Lean counterpart or explicit type/domain representation; imported auxiliary invariant *statements* are documented as not seeded into the Lean proof. Lean's ballot type remains `Nat`, the message set retains stale and duplicate-per-acceptor responses as the source permits, `Phase2a` keeps an existential response subset `S`, `Phase2b` uses `b ≥ maxBal[a]`, and `chosen` is *derived* from `2b` votes, never stored as a decision. The theorem `agreement` states for all reachable states that `Consistency` holds at arbitrary `N`, arbitrary value type, and any pairwise-intersecting quorum family; `agreement_n0` instantiates it at the eventually calibrated acceptor count with two values and majority quorums. The mutant has exactly the same weakened `Phase2a` guard as Route A; its false statement is never closed.
- **Why**: weakening agreement, shrinking the response subsets, or bounding Lean ballots would invalidate the same-claim comparison or the link to the imported theorem.
- **Expected failure before implementation**: `FileNotFoundError` for the missing audit file.

## Scenario 3 — the IJCAR figure is honestly labelled as human prior art, not a measured route

- **Actor**: the reader comparing machine and human results.
- **Boundary**: `docs/equivalence-paxos.md` and the existing `results/human.jsonl` record `ijcar2010-paxos`.
- **When**: the reader examines the audit's comparator section.
- **Then**: the 550 **lines** are for IJCAR's *first refinement proof*, not a runtime/cost measurement or a line count of agreement in Lean; the >1000-line second refinement is incomplete. The pinned `Paxos.tla` is 530 lines and `Consensus.tla` 22 lines (whole files, not proof-only counts). The audit does not convert lines to person-days or pool human data into Route A/B distributions; the first-refinement proof and the Lean safety theorem are related but **not identical claims**.
- **Why**: sharing a Paxos name does not make a prior-art refinement size a same-claim cost arm.
- **Expected failure before implementation**: `FileNotFoundError` for the missing audit (the human JSONL record already exists).

Run the focused executable contracts with `nix develop -c pytest tests/test_equivalence_paxos.py`; the implementer reports the observed red result BEFORE writing the projection or audit. Tests never invoke a real model, network, or unbounded TLC exploration.
