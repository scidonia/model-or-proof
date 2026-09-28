# Equivalence audit: Paxos agreement, imported reference ↔ TLC projection ↔ Lean model

Protocol §4.1 requires each port to be audited statement by statement against its reference, so that
Route B answers the same question Route A answered. Paxos has **two** correspondences rather than the
other tasks' one, because the reference is not executable as it stands: the imported IJCAR 2010 artifact
is TLAPS proof text whose constants are unbounded, so an executable finite projection sits between it and
the Lean model. This file is both correspondences.

- **Imported reference** — `specs/tla/ijcar2010/paxos/Paxos.tla` (530 lines) and its
  `Consensus.tla` (22 lines), committed byte-for-byte at pinned provenance
  (`specs/tla/ijcar2010/PROVENANCE.md`) and never edited here. It EXTENDS `TLAPS`, so it is not itself a
  TLC input; it has not been TLC-checked.
- **Finite TLC projection** — `specs/tla/paxos/PaxosFinite.tla` (Route A's spec, `tasks/paxos.json`),
  with the single-guard mutant `specs/tla/paxos/PaxosFiniteMutant.tla`.
- **Lean model** — `proofs/lean/paxos/Paxos.lean` (module `Paxos`), the unbounded-ballot tier-2 seed, and
  the matching mutant `proofs/lean/paxos/PaxosMutant.lean` (module `PaxosMutant`).
- **Toolchain** — `leanprover/lean4:v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`; the
  same pin as the sibling packages, whose resolved `lake-manifest.json` this package copies.
- **Property** — the imported `Consistency` (`Paxos.tla:140`), not the imported `Refinement`. `ChosenIn`
  is a quorum's `2b` votes, `Chosen` an existential over ballots, and `Consistency` says two chosen
  values are equal. No `chosen` state or action is invented.

The projection resolves the three things that keep the imported file out of a model checker — its
`TLAPS` import, `Ballots == Nat`, and the unbounded `None == CHOOSE v : v \notin Values` evaluated by
`Init` — by making `N` and `B` config constants (`Acceptors == 1..N`, `Ballots == 0..B`), fixing
`Values` to two literals, and replacing `None` with the explicit sentinel `"NoValue"`. The whole
restriction to `N ≥ 2`, `B ≥ 1` lives in the **configs** (`CONSTANT N`, `CONSTANT B`; the instances are
`PaxosN2.cfg` … `PaxosN8.cfg` with `B = 1`), not in any `DomainAssumption` predicate — the projection
carries none. Because the projection removes transitions the original still has, it admits **no trace
forbidden by the original** when the original's constants take the projection's values, and it does not
change the agreement property.

Status of this audit: the two tables below are the real mapping against the committed artifacts. The
Lean theorem is a statement with a `sorry` placeholder — the proof is the closure loop's, so this audit
is about the *statements*, not the tactics that close them (closure is asserted separately and
structurally by the harness: zero `sorry`/`Admitted`/`axiom` in the artifact, plan D6).

## 1. Imported Paxos → finite TLC projection

Each of the 21 executable/operator-domain clauses, against the projection's concrete lines. The
classification is for **this** direction: what the projection does to the imported clause.

| Clause | Imported `Paxos.tla` | Projection `PaxosFinite.tla` | Fidelity |
| --- | --- | --- | --- |
| Acceptors | `CONSTANTS Acceptors, Values, Quorums` (14) | `CONSTANTS N, B` (29), `Acceptors == 1..N` (31) | bounded restriction — an arbitrary constant set becomes the finite `1..N`; `N` is the config's instance count |
| Values | `CONSTANTS Acceptors, Values, Quorums` (14) | `Values == {"v0", "v1"}` (33) | bounded restriction — an arbitrary set becomes two symmetric literals, so a reachable choice of one has a renamed reachable choice of the other |
| Quorums | `CONSTANTS Acceptors, Values, Quorums` (14) | `Quorums == {Q \in SUBSET Acceptors : Cardinality(Q) > N \div 2}` (35) | bounded restriction — an arbitrary family becomes the strict majorities on the finite acceptors |
| QuorumAssumption | `ASSUME QuorumAssumption ==` (16–18): `Quorums \subseteq SUBSET Acceptors`, `\A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}` | `ASSUME QuorumAssumption ==` (37–39): the same two conjuncts | identical — the assumption is not weakened; `QuorumNonEmpty`'s consequence is kept by the majority definition |
| Ballots | `Ballots == Nat` (26) | `Ballots == 0..B` (41), `B = 1` in every config | bounded restriction — `Nat` becomes `{0,1}` at `B = 1`; this is the projection's bound, and the Lean model drops it again |
| vars | `vars == <<msgs, maxBal, maxVBal, maxVal>>` (35) | `vars == <<msgs, maxBal, maxVBal, maxVal>>` (50) | identical — the same four variables in the same order |
| Send | `Send(m) == msgs' = msgs \cup {m}` (37) | `Send(m) == msgs' = msgs \cup {m}` (52) | identical |
| None | `None == CHOOSE v : v \notin Values` (39) | `None == "NoValue"` (57) | idiomatic representation — the choice is replaced by an explicit literal outside `Values`; same meaning, and TLC can evaluate it |
| Init | `Init == ...` (44–47) | `Init == ...` (59–62) | identical — no messages, every `maxBal`/`maxVBal` at `-1`, every `maxVal` at the sentinel |
| Phase1a | `Phase1a(b) == ...` (54–56) | `Phase1a(b) == ...` (69–71) | identical — the no-earlier-`1a` guard, the `Send`, and the unchanged acceptor state |
| Phase1b | `Phase1b(a) == ...` (66–73) | `Phase1b(a) == ...` (81–88) | identical — the `1b` carries `maxVBal[a]`/`maxVal[a]`, and only `maxBal[a]` moves |
| Phase2a | `Phase2a(b) == ...` (83–95) | `Phase2a(b) == ...` (98–110) | identical — the no-earlier-`2a` guard, the existential quorum `Q`, the existential response subset `S` with one response per member of `Q`, the all-`-1`/highest-`maxVBal` value rule, and `Send`; only the referenced domains are restricted, and those are the Acceptors/Values/Quorums/Ballots/Messages rows |
| Phase2b | `Phase2b(a) == ...` (103–110) | `Phase2b(a) == ...` (118–125) | identical — the guard is `m.bal >= maxBal[a]`, and `maxBal`/`maxVBal`/`maxVal` all adopt the ballot and value |
| Next | `Next == ...` (112–113) | `Next == ...` (127–128) | identical — the two existentials and the four-way disjunction |
| Spec | `Spec == Init /\ [][Next]_vars` (115) | `Spec == Init /\ [][Next]_vars` (130) | identical |
| VotedForIn | `VotedForIn(a, v, b) == ...` (126–129) | `VotedForIn(a, v, b) == ...` (141–144) | identical — a `2b` in `msgs` with the value, ballot and acceptor |
| ChosenIn | `ChosenIn(v, b) == ...` (131–132) | `ChosenIn(v, b) == ...` (146–147) | identical — a quorum all of whose members voted for `v` in `b` |
| Chosen | `Chosen(v) == \E b \in Ballots : ChosenIn(v, b)` (134) | `Chosen(v) == \E b \in Ballots : ChosenIn(v, b)` (149) | identical — derived from votes, never stored |
| Consistency | `Consistency == ...` (140) | `Consistency == ...` (155) | identical — two chosen values are equal |
| Messages | `Messages == ...` (145–148) | `Messages == ...` (162–165) | bounded restriction — the four record shapes are identical; only the `bal` field's domain shrinks with the Ballots row |
| TypeOK | `TypeOK == ...` (152–156) | `TypeOK == ...` (168–172) | identical — the same five conjuncts over the projection's domains (it is available for the audit and is not the checked property of this task) |

### Proof-only declarations, classified as outside the TLC checking predicate

These imported declarations are not state generation and are **not** reproduced in the projection. They
are named here so that they are classified rather than silently dropped:

- `WontVoteIn` (`Paxos.tla:162–163`), `SafeAt` (`:169–172`), `MsgInv` (`:174–209`), `AccInv`
  (`:211–218`) and `Inv == TypeOK /\ MsgInv /\ AccInv` (`:223`) — TLAPS proof text, i.e. the inductive
  invariant the import's proof carries. They are **not** part of the TLC checking predicate, and the
  Lean model seeds none of them (see table 2).
- `LEMMA QuorumNonEmpty` (`:23`), `LEMMA NoneNotAValue` (`:41`), `LEMMA VotedInv` (`:200`),
  `LEMMA VotedOnce` (`:206`), `LEMMA SafeAtStable` (`:230`), `THEOREM Invariant` (`:282`) — lemmas and a
  theorem of the imported proof, likewise not state generation.
- `THEOREM Consistent == Spec => []Consistency` (`:465`) and `THEOREM Refinement == Spec => C!Spec`
  (`:506`) with `chosenBar` (`:498`) and the `Consensus` instance (`:500`), against `Consensus.tla`. The
  experimental property is the predicate `Consistency`, not these theorems, and the refinement claim's
  trivial specification (`Consensus.tla:8–17`) is not the task's property.
- `NoChoice` (`PaxosFinite.tla:185`) is a **new diagnostic predicate only**: a deliberately false
  invariant used to obtain a reachable-choice witness trace for Route A's non-vacuity check. It is not
  part of `Spec` and not part of `Consistency`, and its rows and traces are kept separate from the
  headline rows.

## 2. Finite projection → Lean model

Each of the same 21 clauses, against the Lean declarations. The classification is for **this** direction:
what `Paxos.lean` does with the projection's clause. The Lean model is the unbounded-ballot counterpart
of the projection, not a bounded instance of it.

| Clause | Projection `PaxosFinite.tla` | Lean `Paxos.lean` | Fidelity |
| --- | --- | --- | --- |
| Acceptors | `Acceptors == 1..N` (31) | the type `Fin N`, the domain of `State.maxBal`/`maxVBal`/`maxVal` (128) and of the `acc` field of `Message` (68) | idiomatic representation — `1..N` is `Fin N`, the same `N` acceptors; the bound is dropped and `N` is universally quantified by `agreement` (266) |
| Values | `Values == {"v0", "v1"}` (33) | the arbitrary type parameter `V`: `State.maxVal : Fin N → Option V` (128), and `Consistency` quantifies over all of `V` (237, 266) | idiomatic representation — the two values are generalized back to an arbitrary value type, so the Lean claim is not the two-value instance |
| Quorums | `Quorums == {Q \in SUBSET Acceptors : Cardinality(Q) > N \div 2}` (35) | the parameter `Quorums : Set (Set (Fin N))` of `Phase2a`/`Next`/`Reachable`/`ChosenIn`/`Chosen`/`Consistency` (178, 202, 213, 227, 232, 237) | idiomatic representation — any family is admitted; the strict-majority instance is what the tier-1 corollary fixes |
| QuorumAssumption | `ASSUME QuorumAssumption == ...` (37–39) | `QuorumAssumption` (144) and the `hQuorums` hypothesis of `agreement` (266): `∀ Q₁ ∈ Quorums, ∀ Q₂ ∈ Quorums, (Q₁ ∩ Q₂).Nonempty` | idiomatic representation — `Quorums ⊆ SUBSET Acceptors` is the type; the pairwise-intersection conjunct is stated as the theorem's hypothesis |
| Ballots | `Ballots == 0..B` (41) | `ℕ`: the `bal` field of `Message` (68, 90) and every action's ballot quantifier (161, 168, 178, 192, 202) | idiomatic representation — the projection's bound is dropped and the reference's `Nat` is restored; the Lean ballot type is **not** `Fin (B + 1)`, so the theorem is not the finite claim |
| vars | `vars == <<msgs, maxBal, maxVBal, maxVal>>` (50) | the structure `State N V` with the four fields (128) | idiomatic representation — a TLA+ tuple becomes a record with the same components; `UNCHANGED vars` is a structural equality |
| Send | `Send(m) == msgs' = msgs \cup {m}` (52) | `Send` (148): `t.msgs = insert m s.msgs` | identical |
| None | `None == "NoValue"` (57) | `Option.none`, the `none` of `maxVal : Fin N → Option V` (128) and of `Init` (153) | idiomatic representation — the sentinel outside `Values` is `none`, outside the image of `some` |
| Init | `Init == ...` (59–62) | `Init` (153) | identical — no messages, every `maxBal`/`maxVBal` at `-1`, every `maxVal` at `none` |
| Phase1a | `Phase1a(b) == ...` (69–71) | `Phase1a` (161) | identical — the no-earlier-`1a` guard, the `Send`, and the unchanged acceptor state |
| Phase1b | `Phase1b(a) == ...` (81–88) | `Phase1b` (168) | identical — the `1b` carries `maxVBal a`/`maxVal a`, and only `maxBal a` moves |
| Phase2a | `Phase2a(b) == ...` (98–110) | `Phase2a` (178) | identical — the guard is still `∃ Q ∈ Quorums, ∃ S ⊆ {1b messages for b}`, `S` is an arbitrary subset (so stale and duplicate-per-acceptor responses survive), and the value rule is the same all-`-1`/highest-`maxVBal` disjunction; only the ballot domain differs, per the Ballots row |
| Phase2b | `Phase2b(a) == ...` (118–125) | `Phase2b` (192) | identical — the guard `b >= maxBal[a]` is written `(b : ℤ) ≥ s.maxBal a`, and `maxBal`/`maxVBal`/`maxVal` all adopt the ballot and value |
| Next | `Next == ...` (127–128) | `Next` (202) | identical — the two existentials and the four-way disjunction |
| Spec | `Spec == Init /\ [][Next]_vars` (130) | `Step` (207) and `Reachable` (213) | idiomatic representation — the execution predicate is read as the state predicate it induces (the standard reading of a safety property); stuttering steps are kept (`t = s`), so no execution is excluded |
| VotedForIn | `VotedForIn(a, v, b) == ...` (141–144) | `VotedForIn` (223): a `2b` in `msgs` with `val = some v`, `ballot = b`, `acc = some a` | identical — read back out of the message set, nothing stored |
| ChosenIn | `ChosenIn(v, b) == ...` (146–147) | `ChosenIn` (227): `∃ Q ∈ Quorums, ∀ a ∈ Q, VotedForIn s a v b` | identical |
| Chosen | `Chosen(v) == \E b \in Ballots : ChosenIn(v, b)` (149) | `Chosen` (232): `∃ b : ℕ, ChosenIn Quorums s v b` | identical — derived from `2b` votes, never stored as a decision |
| Consistency | `Consistency == ...` (155) | `Consistency` (237): `∀ v₁ v₂ : V, Chosen ... v₁ → Chosen ... v₂ → v₁ = v₂` | identical |
| Messages | `Messages == ...` (162–165) | the inductive `Message N V` (68) with its accessors `tag`/`ballot`/`maxVBal`/`maxVal`/`val`/`acc` (83–118), and `msgs : Set (Message N V)` (128) | idiomatic representation — the union of record shapes becomes an inductive type; `msgs \in SUBSET Messages` is the field's type, and duplicate-per-acceptor responses are sets, as the source's are |
| TypeOK | `TypeOK == ...` (168–172) | the type of `State` plus the `TypeOK` predicate (251): `IsBallot (s.maxBal a)`, `IsBallot (s.maxVBal a)`, `s.maxBal a ≥ s.maxVBal a` | idiomatic representation — two conjuncts are carried by the types (`msgs ∈ SUBSET Messages`, `maxVal ∈ [Acceptors → Values ∪ {None}]`) and the remaining three are the explicit predicate; it is an inductive consequence of `Init`/`Next`, not a hypothesis of `agreement` |

### The theorem, and what is deliberately not in the Lean proof

The general statement is

```lean
-- proofs/lean/paxos/Paxos.lean:266
theorem agreement (Quorums : Set (Set (Fin N))) (hQuorums : QuorumAssumption Quorums)
    (s : State N V) (hs : Reachable Quorums s) : Consistency Quorums s
```

at **arbitrary `N`**, **arbitrary value type `V`**, and **any pairwise-intersecting quorum family**. It
is the reference's `Spec => []Consistency` (`Paxos.tla:465`) with the ballot bound removed, so it is
strictly stronger than anything the finite TLC instance establishes. The imported auxiliary invariant
*statements* `WontVoteIn`, `SafeAt`, `MsgInv`, `AccInv` and `Inv` are **not seeded** into this proof:
the file carries no `Inv`/`SafeAt`/`MsgInv`/`AccInv` definition or proof body, and the closure loop must
find its own strengthening. `agreement_n0` — the tier-1 corollary instantiating the theorem at the
calibrated acceptor count, with two values and the majority quorums — is a separate seed
(`PaxosN0.lean`), written once `tasks/paxos.json`'s `n0` is fixed; it is deliberately absent here.

The mutant `proofs/lean/paxos/PaxosMutant.lean` is the analogue of `PaxosFiniteMutant.tla`: the same
state and transition representation with the **one** `Phase2a` quorum-membership guard weakened to a
nonempty subset (`PaxosMutant.lean:142`, `∃ Q : Set (Fin N), Q.Nonempty ∧ ...` instead of
`∃ Q ∈ Quorums`). `ChosenIn` still requires a quorum (`PaxosMutant.lean:185`), as the TLC mutant's does,
so choosing still needs a majority while a proposal does not, and `agreement` (`PaxosMutant.lean:201`)
is false. The expected Route B outcome is `fail_to_close`; a `success` on this file is a broken rig whose
numbers are discarded (protocol §5).

A reader can walk the violation by hand at `N = 3` (acceptors `0,1,2`), `B = 1` (ballots `0,1`), two
values `v0 ≠ v1`, `Quorums` the strict majorities: `Phase1a(0)`, the three `Phase1b(a)`, then
`Phase2a(0)` with `Q = {0,1}` and all-`-1` responses proposing `v0`, then `Phase2b(0)` and `Phase2b(1)`
— so `ChosenIn(v0, 0)` holds with `Q = {0,1}` and `v0` is chosen. Then `Phase1a(1)`, `Phase1b(2)` (which
raises `maxBal[2]` to `1`), and the mutated `Phase2a(1)` with the **singleton** `Q = {2}`, which is
nonempty and so admitted, all-`-1` responses again allowing any value: propose `v1`. `Phase2b(0)` and
`Phase2b(2)` then vote `v1` in ballot `1`, so `ChosenIn(v1, 1)` holds with the quorum `{0,2}` and `v1` is
chosen too. Every step is one of the mutated module's own actions, and the step that fails in the
positive model is `Phase2a(1)`: `{2} ∉ Quorums`. The Route A mutant `PaxosFiniteMutant.tla` exhibits the
same violation at `N = 3`, `B = 1` in TLC.

## 3. The IJCAR 2010 figure is human prior art, not a measured route

The comparator recorded in `results/human.jsonl` under `ijcar2010-paxos`:

- The **550 lines** are the IJCAR 2010 first-refinement safety proof's line count — a published
  *first refinement* size, quoted from the paper, not a runtime or dollar measurement, and not a line
  count of agreement in Lean. The second refinement is published as "somewhat over 1000" lines and is
  **incomplete** ("most of the proof"); it is recorded with `partial: true`.
- The committed artifacts are the whole files `Paxos.tla` at **530** lines and `Consensus.tla` at **22**
  lines. The published line counts and these artifact sizes disagree and are both recorded, never
  reconciled into one figure.
- The first-refinement proof and the Lean safety theorem are related — same algorithm, same safety
  property — but they are **not identical** claims: the IJCAR development proves a refinement *into* the
  trivial `Consensus` specification, while `agreement` is the invariance of `Consistency` over the
  projection's transitions. The audit does not convert proof lines to person-days, and the human record
  is `kind: "human_prior_art"` with `machine_checked: false`, never pooled with Route A's or Route B's
  measured distributions.
