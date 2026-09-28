/-
Paxos agreement (IJCAR 2010 reference, unbounded-ballot model) — the Lean model for Route B.

This is the idiomatic counterpart of the imported reference `specs/tla/ijcar2010/paxos/Paxos.tla`
(and its `Consensus.tla`, whose trivial specification the reference refines) as carried by the
executable finite projection `specs/tla/paxos/PaxosFinite.tla`. The statement-by-statement
correspondence is audited in `docs/equivalence-paxos.md` (protocol §4.1), in two directions: the
imported reference to the finite TLC projection, and the projection to this file. The model neither
strengthens an assumption nor weakens the goal, and it does **not** carry the projection's ballot
bound: `Ballots == Nat` in the reference, and the ballot type here is `ℕ` again.

What this file is, and what it is not:

* It is the closure loop's **tier-2 seed** (plan D5): the model and the `agreement` theorem statement
  are the human's, the proof is the loop's, and the `sorry` below is the statement's placeholder, not a
  result. Statements and model only: no `Inv`/`SafeAt`/`MsgInv`/`AccInv` proof body is imported or
  reproduced, and the imported auxiliary invariant *statements* are documented in the audit as **not
  seeded into the Lean proof**.
* The tier-1 corollary `agreement_n0` — the general `agreement` instantiated at the calibrated acceptor
  count with the two-value majority-quorum instance — is a separate seed (`PaxosN0.lean`), written once
  `tasks/paxos.json`'s `n0` is fixed. It is deliberately absent here.
* `Consistency` is a *derived* predicate over `2b` votes (TLA+ `VotedForIn`/`ChosenIn`/`Chosen`): no
  `chosen` variable is stored anywhere, and no action decides. This mirrors the reference, where
  "chosen" is an operator and not a state component.
* The negative control is `PaxosMutant.lean`: the same state and transition representation with the one
  `Phase2a` quorum-membership guard weakened exactly as `specs/tla/paxos/PaxosFiniteMutant.tla` weakens
  it. Its `agreement` is false, so a run that closes it means the rig is broken (protocol §5).

Representation notes (the audit classifies each of these):

* Messages are the inductive `Message N V`, one constructor per TLA+ record shape. The message set
  `msgs` is a `Set`, as the source's is, so stale `1b`s and several responses per acceptor survive: the
  `2a` response subset `S` is an arbitrary subset of the `1b` messages for the ballot, exactly the
  source's `\E S \in SUBSET {...}`.
* `maxBal` and `maxVBal` are `ℤ`: the source initialises both to `-1` and compares them against ballot
  numbers, so `-1` is represented literally rather than as an option. The source's typing conjunct
  (`maxBal[a] ∈ Ballots ∪ {-1}`, and `maxBal[a] ≥ maxVBal[a]`) is the explicit `TypeOK` predicate; it is
  an inductive consequence of `Init`/`Next`, not a hypothesis of the theorem, exactly as in the source's
  invariant.
* `maxVal` is `Option V`: the source's `None == CHOOSE v : v \notin Values` is the `none` of `Option V`,
  which is outside the image of `some`, so the "no vote yet" sentinel is a type-level value and not a
  choice that has to be witnessed.
* The ballot type is `ℕ`, the value type is the arbitrary `V` (not fixed to two values), the acceptor
  type is `Fin N` for the arbitrary `N`, and the quorum family is the arbitrary `Quorums` with the
  pairwise-intersection `QuorumAssumption`. The theorem quantifies over all of them.
-/
import Mathlib

namespace Paxos

/-! ## Messages -/

/-- The four message type tags of the reference, `"1a"`, `"1b"`, `"2a"`, `"2b"`. -/
inductive MessageTag where
  /-- A phase-1a request. -/
  | oneA
  /-- A phase-1b promise. -/
  | oneB
  /-- A phase-2a proposal. -/
  | twoA
  /-- A phase-2b vote. -/
  | twoB
  deriving DecidableEq

/-- TLA+ `Messages` (`Paxos.tla:145-148`): the message universe, one constructor per record shape, with
the field names and domains of the source. `msgs ∈ SUBSET Messages` is therefore the type
`Set (Message N V)` and needs no separate predicate. -/
inductive Message (N : ℕ) (V : Type*) where
  /-- `[type |-> "1a", bal |-> b]`. -/
  | «1a» (bal : ℕ)
  /-- `[type |-> "1b", bal, maxVBal, maxVal, acc]`. -/
  | «1b» (bal : ℕ) (maxVBal : ℤ) (maxVal : Option V) (acc : Fin N)
  /-- `[type |-> "2a", bal, val]`. -/
  | «2a» (bal : ℕ) (val : V)
  /-- `[type |-> "2b", bal, val, acc]`. -/
  | «2b» (bal : ℕ) (val : V) (acc : Fin N)

namespace Message

variable {N : ℕ} {V : Type*}

/-- TLA+ `m.type`: the tag of a message. -/
def tag : Message N V → MessageTag
  | «1a» _ => .oneA
  | «1b» _ _ _ _ => .oneB
  | «2a» _ _ => .twoA
  | «2b» _ _ _ => .twoB

/-- TLA+ `m.bal`, which every message carries. -/
def ballot : Message N V → ℕ
  | «1a» b => b
  | «1b» b _ _ _ => b
  | «2a» b _ => b
  | «2b» b _ _ => b

/-- TLA+ `m.maxVBal`, which only a `1b` message carries. The default `-1` is the source's own sentinel
and is never read: `Phase2a`'s subset `S` is restricted to `1b` messages. -/
def maxVBal : Message N V → ℤ
  | «1b» _ mb _ _ => mb
  | _ => -1

/-- TLA+ `m.maxVal`, which only a `1b` message carries; the default `none` is the source's `None`
sentinel and is likewise read only on the restricted subset. -/
def maxVal : Message N V → Option V
  | «1b» _ _ mv _ => mv
  | _ => none

/-- TLA+ `m.val`, which only a `2a`/`2b` message carries. -/
def val : Message N V → Option V
  | «2a» _ v => some v
  | «2b» _ v _ => some v
  | _ => none

/-- TLA+ `m.acc`, which a `1b`/`2b` message carries. -/
def acc : Message N V → Option (Fin N)
  | «1b» _ _ _ a => some a
  | «2b» _ _ a => some a
  | _ => none

end Message

/-! ## The state -/

/-- TLA+ `VARIABLES msgs, maxBal, maxVBal, maxVal` (`Paxos.tla:28-35`). The four variables are the four
fields; `vars` is the structure itself, so `UNCHANGED vars` is a full structural equality. `maxVal` is
`Option V`, whose `none` is the source's `None`; `maxBal`/`maxVBal` are `ℤ` with the source's `-1`
initial value. -/
structure State (N : ℕ) (V : Type*) where
  /-- The set of messages that have been sent. -/
  msgs : Set (Message N V)
  /-- The highest-numbered ballot each acceptor has participated in. -/
  maxBal : Fin N → ℤ
  /-- The highest ballot in which each acceptor has voted. -/
  maxVBal : Fin N → ℤ
  /-- The value each acceptor voted for at `maxVBal`; `none` is the source's `None`. -/
  maxVal : Fin N → Option V

variable {N : ℕ} {V : Type*}

/-! ## The model -/

/-- TLA+ `ASSUME QuorumAssumption` (`Paxos.tla:16-21`): every two quorums intersect. The source's first
conjunct, `Quorums ⊆ SUBSET Acceptors`, is the type `Quorums : Set (Set (Fin N))`. -/
def QuorumAssumption (Quorums : Set (Set (Fin N))) : Prop :=
  ∀ Q₁ ∈ Quorums, ∀ Q₂ ∈ Quorums, (Q₁ ∩ Q₂).Nonempty

/-- TLA+ `Send(m) == msgs' = msgs \cup {m}` (`Paxos.tla:37`). -/
def Send (m : Message N V) (s t : State N V) : Prop :=
  t.msgs = insert m s.msgs

/-- TLA+ `Init` (`Paxos.tla:44-47`): no messages, every `maxBal`/`maxVBal` at the `-1` sentinel, every
`maxVal` at `None`. -/
def Init (s : State N V) : Prop :=
  s.msgs = ∅ ∧
    s.maxBal = (fun _ => -1) ∧
    s.maxVBal = (fun _ => -1) ∧
    s.maxVal = (fun _ => none)

/-- TLA+ `Phase1a(b)` (`Paxos.tla:54-56`): a leader that has not already sent a `1a` for ballot `b`
sends one; no acceptor state changes. -/
def Phase1a (b : ℕ) (s t : State N V) : Prop :=
  (¬ ∃ m ∈ s.msgs, m.tag = MessageTag.oneA ∧ m.ballot = b) ∧
    Send (Message.«1a» b) s t ∧
    t.maxBal = s.maxBal ∧ t.maxVBal = s.maxVBal ∧ t.maxVal = s.maxVal

/-- TLA+ `Phase1b(a)` (`Paxos.tla:66-71`): an acceptor `a` answers a `1a` for a ballot above its
`maxBal` with a `1b` carrying its current `maxVBal`/`maxVal`, and raises its `maxBal`. -/
def Phase1b (a : Fin N) (s t : State N V) : Prop :=
  ∃ b : ℕ, Message.«1a» b ∈ s.msgs ∧ (b : ℤ) > s.maxBal a ∧
    Send (Message.«1b» b (s.maxVBal a) (s.maxVal a) a) s t ∧
    t.maxBal = Function.update s.maxBal a (b : ℤ) ∧
    t.maxVBal = s.maxVBal ∧ t.maxVal = s.maxVal

/-- TLA+ `Phase2a(b)` (`Paxos.tla:83-95`): if no `2a` for ballot `b` has been sent, a leader may send one
for any value `v` for which there is a quorum `Q` and a subset `S` of the `1b` responses for `b` — one
response per member of `Q`, possibly a stale one — whose highest-numbered vote is `v` (or none, in which
case any `v` is allowed). `S` is an arbitrary subset: several responses per acceptor survive. -/
def Phase2a (Quorums : Set (Set (Fin N))) (b : ℕ) (s t : State N V) : Prop :=
  (¬ ∃ m ∈ s.msgs, m.tag = MessageTag.twoA ∧ m.ballot = b) ∧
    (∃ v : V, ∃ Q ∈ Quorums, ∃ S : Set (Message N V),
      S ⊆ {m : Message N V | m ∈ s.msgs ∧ m.tag = MessageTag.oneB ∧ m.ballot = b} ∧
        (∀ a ∈ Q, ∃ m ∈ S, m.acc = some a) ∧
        ((∀ m ∈ S, m.maxVBal = -1) ∨
          (∃ c : ℕ, c < b ∧ (∀ m ∈ S, m.maxVBal ≤ (c : ℤ)) ∧
            ∃ m ∈ S, m.maxVBal = (c : ℤ) ∧ m.maxVal = some v)) ∧
        Send (Message.«2a» b v) s t) ∧
    t.maxBal = s.maxBal ∧ t.maxVBal = s.maxVBal ∧ t.maxVal = s.maxVal

/-- TLA+ `Phase2b(a)` (`Paxos.tla:103-110`): an acceptor votes with a `2b` for a proposal whose ballot is
at least its `maxBal`, and adopts that ballot and value as its `maxBal`/`maxVBal`/`maxVal`. The guard is
`b ≥ maxBal[a]`, as in the source. -/
def Phase2b (a : Fin N) (s t : State N V) : Prop :=
  ∃ b : ℕ, ∃ v : V, Message.«2a» b v ∈ s.msgs ∧ (b : ℤ) ≥ s.maxBal a ∧
    Send (Message.«2b» b v a) s t ∧
    t.maxBal = Function.update s.maxBal a (b : ℤ) ∧
    t.maxVBal = Function.update s.maxVBal a (b : ℤ) ∧
    t.maxVal = Function.update s.maxVal a (some v)

/-- TLA+ `Next` (`Paxos.tla:112-113`): a `Phase1a`/`Phase2a` for some ballot, or a `Phase1b`/`Phase2b`
for some acceptor. `Ballots` is `ℕ` and `Acceptors` is `Fin N`, so the two existential quantifiers are
over those types. -/
def Next (Quorums : Set (Set (Fin N))) (s t : State N V) : Prop :=
  (∃ b : ℕ, Phase1a b s t ∨ Phase2a Quorums b s t) ∨
    ∃ a : Fin N, Phase1b a s t ∨ Phase2b a s t

/-- TLA+ `[Next]_vars`: a `Next` step, or a stuttering step. -/
def Step (Quorums : Set (Set (Fin N))) (s t : State N V) : Prop :=
  Next Quorums s t ∨ t = s

/-- The states admitted by TLA+ `Spec == Init /\ [][Next]_vars` (`Paxos.tla:115`), read as a state
predicate — the invariance reading of the safety property `Consistency` (protocol §11 decision 4). The
stuttering steps are kept, so no `Spec` execution is excluded; being stateless they add no states. -/
inductive Reachable (Quorums : Set (Set (Fin N))) : State N V → Prop where
  /-- The initial states. -/
  | init {s} : Init s → Reachable Quorums s
  /-- The states one `[Next]_vars` step away from a reachable state. -/
  | step {s t} : Reachable Quorums s → Step Quorums s t → Reachable Quorums t

/-! ## `Chosen` and `Consistency`, derived from votes -/

/-- TLA+ `VotedForIn(a, v, b)` (`Paxos.tla:126-129`): acceptor `a` has sent a `2b` for value `v` in
ballot `b`. Nothing is stored: the vote is read back out of the message set. -/
def VotedForIn (s : State N V) (a : Fin N) (v : V) (b : ℕ) : Prop :=
  ∃ m ∈ s.msgs, m.tag = MessageTag.twoB ∧ m.val = some v ∧ m.ballot = b ∧ m.acc = some a

/-- TLA+ `ChosenIn(v, b)` (`Paxos.tla:131-132`): a quorum has voted for `v` in ballot `b`. -/
def ChosenIn (Quorums : Set (Set (Fin N))) (s : State N V) (v : V) (b : ℕ) : Prop :=
  ∃ Q ∈ Quorums, ∀ a ∈ Q, VotedForIn s a v b

/-- TLA+ `Chosen(v)` (`Paxos.tla:134`): `v` has been chosen in some ballot. The ballot quantifier is over
`ℕ`, and nothing is stored — the decision is derived, never an action's effect. -/
def Chosen (Quorums : Set (Set (Fin N))) (s : State N V) (v : V) : Prop :=
  ∃ b : ℕ, ChosenIn Quorums s v b

/-- TLA+ `Consistency` (`Paxos.tla:140`): two chosen values are equal. This is the property the task
measures, not the reference's `Refinement`. -/
def Consistency (Quorums : Set (Set (Fin N))) (s : State N V) : Prop :=
  ∀ v₁ v₂ : V, Chosen Quorums s v₁ → Chosen Quorums s v₂ → v₁ = v₂

/-! ## Typing -/

/-- The source's `Ballots ∪ {-1}` domain predicate on a `ℤ`: a ballot number, or the `-1` sentinel. -/
def IsBallot (z : ℤ) : Prop :=
  z = -1 ∨ ∃ b : ℕ, z = (b : ℤ)

/-- TLA+ `TypeOK` (`Paxos.tla:152-156`). Two of its five conjuncts are carried by the types here —
`msgs ∈ SUBSET Messages` is `msgs : Set (Message N V)`, and `maxVal ∈ [Acceptors → Values ∪ {None}]` is
`maxVal : Fin N → Option V` — so they are not repeated; the remaining three are this predicate. It is an
inductive consequence of `Init`/`Next`, not a hypothesis of `agreement`, exactly as in the source, where
`TypeOK` is the first conjunct of the proven `Inv`. -/
def TypeOK (s : State N V) : Prop :=
  (∀ a, IsBallot (s.maxBal a)) ∧
    (∀ a, IsBallot (s.maxVBal a)) ∧
    ∀ a, s.maxBal a ≥ s.maxVBal a

/-! ## The theorem -/

/-- **Agreement**, in general (tier 2, protocol §2): every state reachable under
`Init /\ [][Next]_vars` satisfies `Consistency`, for every acceptor count `N`, every value type `V`, and
every pairwise-intersecting quorum family `Quorums`. This is the reference's
`Spec => []Consistency` (`Paxos.tla:465`) with its ballot bound removed: the Lean ballot type is `ℕ`, not
`Fin (B + 1)`, so the theorem is not the finite projection's claim. The tier-1 corollary at the
calibrated `n0` is a separate seed (`PaxosN0.lean`).

The proof is the closure loop's; the `sorry` is the seed's placeholder, not a result. -/
theorem agreement (Quorums : Set (Set (Fin N))) (hQuorums : QuorumAssumption Quorums)
    (s : State N V) (hs : Reachable Quorums s) : Consistency Quorums s := by
  classical
  let WontVoteIn (s : State N V) (a : Fin N) (b : ℕ) : Prop :=
    (∀ v : V, ¬ VotedForIn s a v b) ∧ (b : ℤ) < s.maxBal a
  let SafeAt (s : State N V) (v : V) (b : ℕ) : Prop :=
    ∀ c : ℕ, c < b → ∃ Q ∈ Quorums, ∀ a ∈ Q, VotedForIn s a v c ∨ WontVoteIn s a c
  let MsgInv (s : State N V) : Prop :=
    (∀ b mb mv a, Message.«1b» b mb mv a ∈ s.msgs →
      (b : ℤ) ≤ s.maxBal a ∧
      ((∃ v : V, ∃ b' : ℕ, mv = some v ∧ mb = (b' : ℤ) ∧ VotedForIn s a v b') ∨ (mv = none ∧ mb = -1)) ∧
      (∀ c : ℕ, (mb : ℤ) < (c : ℤ) ∧ (c : ℤ) < (b : ℤ) → ¬ ∃ v : V, VotedForIn s a v c)) ∧
    (∀ b v, Message.«2a» b v ∈ s.msgs →
      SafeAt s v b ∧
      (∀ b' v', Message.«2a» b' v' ∈ s.msgs → b' = b → v' = v)) ∧
    (∀ b v a, Message.«2b» b v a ∈ s.msgs →
      Message.«2a» b v ∈ s.msgs ∧ (b : ℤ) ≤ s.maxVBal a)
  let AccInv (s : State N V) : Prop :=
    ∀ a : Fin N,
      ((s.maxVal a = none) ↔ (s.maxVBal a = -1)) ∧
      (s.maxVBal a ≤ s.maxBal a) ∧
      ((0 : ℤ) ≤ s.maxVBal a → ∃ v : V, ∃ b : ℕ, s.maxVal a = some v ∧ s.maxVBal a = (b : ℤ) ∧ VotedForIn s a v b) ∧
      (∀ c : ℕ, s.maxVBal a < (c : ℤ) → ¬ ∃ v : V, VotedForIn s a v c)
  let Inv (s : State N V) : Prop := TypeOK s ∧ MsgInv s ∧ AccInv s

  have hTypeOK_congr : ∀ {s t : State N V}, t.maxBal = s.maxBal → t.maxVBal = s.maxVBal → t.maxVal = s.maxVal → TypeOK s → TypeOK t := by
    intro s t hmb hmvb hmv hT
    change TypeOK t
    rcases hT with ⟨h1, h2, h3⟩
    constructor
    · intro a
      simpa [hmb] using h1 a
    · constructor
      · intro a
        simpa [hmvb] using h2 a
      · intro a
        simpa [hmb, hmvb] using h3 a

  have hmem_insert : ∀ {s t : State N V} (m : Message N V), t.msgs = insert m s.msgs → ∀ m', m' ∈ t.msgs → m' = m ∨ m' ∈ s.msgs := by
    intro s t m hm m' hm'
    rw [hm] at hm'
    exact hm'

  have hVotedForIn_mono : ∀ {s t : State N V} {m : Message N V}, t.msgs = insert m s.msgs → ∀ a v b, VotedForIn s a v b → VotedForIn t a v b := by
    intro s t m hm a v b h
    rcases h with ⟨m', hm', htag, hval, hbal, hacc⟩
    refine ⟨m', ?_, htag, hval, hbal, hacc⟩
    rw [hm]
    exact Or.inr hm'

  have hVotedForIn_iff : ∀ {s : State N V} (a : Fin N) (v : V) (b : ℕ), VotedForIn s a v b ↔ Message.«2b» b v a ∈ s.msgs := by
    intro s a v b
    constructor
    · intro h
      rcases h with ⟨m, hm, htag, hval, hbal, hacc⟩
      cases m with
      | «1a» b' => simp [Message.tag] at htag
      | «1b» b' mb mv a' => simp [Message.tag] at htag
      | «2a» b' v' => simp [Message.tag] at htag
      | «2b» b' v' a' =>
          simp only [Message.ballot, Message.val, Message.acc] at hbal hval hacc
          have hv' : v' = v := Option.some.inj hval
          have ha' : a' = a := Option.some.inj hacc
          subst b'
          subst v'
          subst a'
          exact hm
    · intro hm
      exact ⟨Message.«2b» b v a, hm, rfl, rfl, rfl, rfl⟩

  have hVotedForIn_rev_of_not_twoB : ∀ {s t : State N V} (m : Message N V), t.msgs = insert m s.msgs → m.tag ≠ MessageTag.twoB → ∀ a v b, VotedForIn t a v b → VotedForIn s a v b := by
    intro s t m hm htag a v b h
    rcases h with ⟨m', hm', htag', hval', hbal', hacc'⟩
    rcases hmem_insert m hm m' hm' with hEq | hm's
    · subst m'
      exact False.elim (htag htag')
    · exact ⟨m', hm's, htag', hval', hbal', hacc'⟩

  have hWontVoteIn_mono' : ∀ {s t : State N V},
      (∀ a v b, VotedForIn t a v b → VotedForIn s a v b) →
      (∀ a, s.maxBal a ≤ t.maxBal a) →
      ∀ a b, WontVoteIn s a b → WontVoteIn t a b := by
    intro s t hVrev hmb a b h
    rcases h with ⟨hnv, hb⟩
    constructor
    · intro v hv
      exact hnv v (hVrev a v b hv)
    · exact lt_of_lt_of_le hb (hmb a)

  have hSafeAt_mono : ∀ {s t : State N V},
      (∀ a v b, VotedForIn s a v b → VotedForIn t a v b) →
      (∀ a b, WontVoteIn s a b → WontVoteIn t a b) →
      ∀ v b, SafeAt s v b → SafeAt t v b := by
    intro s t hV hW v b h
    intro c hc
    rcases h c hc with ⟨Q, hQ, hq⟩
    refine ⟨Q, hQ, ?_⟩
    intro a ha
    rcases hq a ha with hvv | hw
    · exact Or.inl (hV a v c hvv)
    · exact Or.inr (hW a c hw)

  have hVotedOnce : ∀ {s : State N V}, MsgInv s → ∀ a1 a2 v1 v2 b, VotedForIn s a1 v1 b → VotedForIn s a2 v2 b → v1 = v2 := by
    intro s hM a1 a2 v1 v2 b h1 h2
    rcases hM with ⟨h1b, h2a, h2b⟩
    have hm1 : Message.«2b» b v1 a1 ∈ s.msgs := (hVotedForIn_iff a1 v1 b).mp h1
    have hm2 : Message.«2b» b v2 a2 ∈ s.msgs := (hVotedForIn_iff a2 v2 b).mp h2
    have ha1 : Message.«2a» b v1 ∈ s.msgs := (h2b b v1 a1 hm1).1
    have ha2 : Message.«2a» b v2 ∈ s.msgs := (h2b b v2 a2 hm2).1
    have huniq := (h2a b v1 ha1).2
    exact (huniq b v2 ha2 rfl).symm

  have h1b_of_mem_tag_bal : ∀ (b : ℕ) {m : Message N V}, m.tag = MessageTag.oneB → m.ballot = b → ∃ mb mv a, m = Message.«1b» b mb mv a := by
    intro b m htag hbal
    cases m with
    | «1a» b' => simp [Message.tag] at htag
    | «1b» b' mb mv a' =>
        simp only [Message.ballot] at hbal
        subst b'
        exact ⟨mb, mv, a', rfl⟩
    | «2a» b' v' => simp [Message.tag] at htag
    | «2b» b' v' a' => simp [Message.tag] at htag

  have hIsBallot_ofNat : ∀ b : ℕ, IsBallot (b : ℤ) := by
    intro b
    unfold IsBallot
    exact Or.inr ⟨b, rfl⟩

  have hAccVote_or_none : ∀ {s : State N V}, AccInv s → TypeOK s → ∀ a,
      (∃ v : V, ∃ b' : ℕ, s.maxVal a = some v ∧ s.maxVBal a = (b' : ℤ) ∧ VotedForIn s a v b') ∨ (s.maxVal a = none ∧ s.maxVBal a = -1) := by
    intro s hA hT a
    rcases hA a with ⟨hiff, hle, hvote, hnov⟩
    rcases hT with ⟨hT1, hT2, hT3⟩
    by_cases hneg : s.maxVBal a = -1
    · right
      exact ⟨(hiff.mpr hneg), hneg⟩
    · left
      rcases hT2 a with hneg' | hpos
      · exact False.elim (hneg hneg')
      · rcases hpos with ⟨b', hb'⟩
        have hge : (0 : ℤ) ≤ s.maxVBal a := by
          rw [hb']
          omega
        rcases hvote hge with ⟨v, b'', hmv, hmb'', hvv⟩
        exact ⟨v, b'', hmv, hmb'', hvv⟩

  have hVotedInv : ∀ {s : State N V}, Inv s → ∀ a v b, VotedForIn s a v b → SafeAt s v b ∧ (b : ℤ) ≤ s.maxVBal a := by
    intro s hi a v b h
    rcases hi with ⟨hT, hM, hA⟩
    rcases hM with ⟨h1b, h2a, h2b⟩
    have hm : Message.«2b» b v a ∈ s.msgs := (hVotedForIn_iff a v b).mp h
    have h2 := h2b b v a hm
    exact ⟨(h2a b v h2.1).1, h2.2⟩

  have hPhase1a : ∀ {s t : State N V} (b : ℕ), Phase1a b s t → Inv s → Inv t := by
    intro s t b hp hi
    rcases hi with ⟨hT, hM, hA⟩
    rcases hM with ⟨h1b, h2a, h2b⟩
    rcases hp with ⟨hno1a, hsend, hmb, hmvb, hmv⟩
    have htag_ne : (Message.«1a» b : Message N V).tag ≠ MessageTag.twoB := by simp [Message.tag]
    have hVoted_eq : ∀ a v b', VotedForIn t a v b' ↔ VotedForIn s a v b' := by
      intro a v b'
      constructor
      · exact hVotedForIn_rev_of_not_twoB (Message.«1a» b) hsend htag_ne a v b'
      · exact hVotedForIn_mono hsend a v b'
    have hmb_le : ∀ a, s.maxBal a ≤ t.maxBal a := by
      intro a
      simp [hmb]
    have hVfwd : ∀ a v b', VotedForIn s a v b' → VotedForIn t a v b' := hVotedForIn_mono hsend
    have hVrev : ∀ a v b', VotedForIn t a v b' → VotedForIn s a v b' := fun a v b' => (hVoted_eq a v b').mp
    have hWfwd : ∀ a b', WontVoteIn s a b' → WontVoteIn t a b' := hWontVoteIn_mono' hVrev hmb_le
    have hSafe_fwd : ∀ v b', SafeAt s v b' → SafeAt t v b' := hSafeAt_mono hVfwd hWfwd
    constructor
    · exact hTypeOK_congr hmb hmvb hmv hT
    · constructor
      · constructor
        · intro b' mb' mv' a' hm'
          have hm's : Message.«1b» b' mb' mv' a' ∈ s.msgs := by
            rcases hmem_insert (Message.«1a» b) hsend (Message.«1b» b' mb' mv' a') hm' with hEq | hm's
            · cases hEq
            · exact hm's
          have h1 := h1b b' mb' mv' a' hm's
          rcases h1 with ⟨hle, hdisj, hnv⟩
          constructor
          · simpa [hmb] using hle
          · constructor
            · rcases hdisj with hd | hd
              · left
                rcases hd with ⟨v, b'', hmv', hmb', hvv⟩
                refine ⟨v, b'', hmv', hmb', ?_⟩
                exact hVfwd a' v b'' hvv
              · right
                exact hd
            · intro c hc hv
              rcases hv with ⟨v, hvt⟩
              have hvs : VotedForIn s a' v c := hVrev a' v c hvt
              exact hnv c hc ⟨v, hvs⟩
        · constructor
          · intro b' v' hm'
            have hm's : Message.«2a» b' v' ∈ s.msgs := by
              rcases hmem_insert (Message.«1a» b) hsend (Message.«2a» b' v') hm' with hEq | hm's
              · cases hEq
              · exact hm's
            have h2 := h2a b' v' hm's
            constructor
            · exact hSafe_fwd v' b' h2.1
            · intro b'' v'' hm'' hbb
              have hm''s : Message.«2a» b'' v'' ∈ s.msgs := by
                rcases hmem_insert (Message.«1a» b) hsend (Message.«2a» b'' v'') hm'' with hEq | hm''s
                · cases hEq
                · exact hm''s
              exact h2.2 b'' v'' hm''s hbb
          · intro b' v' a' hm'
            have hm's : Message.«2b» b' v' a' ∈ s.msgs := by
              rcases hmem_insert (Message.«1a» b) hsend (Message.«2b» b' v' a') hm' with hEq | hm's
              · cases hEq
              · exact hm's
            have h2 := h2b b' v' a' hm's
            constructor
            · rw [hsend]
              exact Or.inr h2.1
            · simpa [hmvb] using h2.2
      · intro a
        simpa [hmv, hmvb, hmb, hVoted_eq] using hA a

  have hPhase1b : ∀ {s t : State N V} (a : Fin N), Phase1b a s t → Inv s → Inv t := by
    intro s t a hp hi
    rcases hi with ⟨hT, hM, hA⟩
    rcases hM with ⟨h1b, h2a, h2b⟩
    rcases hT with ⟨hT1, hT2, hT3⟩
    rcases hp with ⟨b, h1a, hgt, hsend, hmb, hmvb, hmv⟩
    have hle_b : s.maxVBal a ≤ (b : ℤ) := le_of_lt (lt_of_le_of_lt (hT3 a) hgt)
    have htag_ne : (Message.«1b» b (s.maxVBal a) (s.maxVal a) a : Message N V).tag ≠ MessageTag.twoB := by simp [Message.tag]
    have hVoted_eq : ∀ a' v b', VotedForIn t a' v b' ↔ VotedForIn s a' v b' := by
      intro a' v b'
      constructor
      · exact hVotedForIn_rev_of_not_twoB (Message.«1b» b (s.maxVBal a) (s.maxVal a) a) hsend htag_ne a' v b'
      · exact hVotedForIn_mono hsend a' v b'
    have hmb_le : ∀ a', s.maxBal a' ≤ t.maxBal a' := by
      intro a'
      by_cases ha : a' = a
      · subst a'
        simpa [hmb, Function.update] using (le_of_lt hgt)
      · simp [hmb, Function.update, ha]
    have hVfwd : ∀ a' v b', VotedForIn s a' v b' → VotedForIn t a' v b' := hVotedForIn_mono hsend
    have hVrev : ∀ a' v b', VotedForIn t a' v b' → VotedForIn s a' v b' := fun a' v b' => (hVoted_eq a' v b').mp
    have hWfwd : ∀ a' b', WontVoteIn s a' b' → WontVoteIn t a' b' := hWontVoteIn_mono' hVrev hmb_le
    have hSafe_fwd : ∀ v b', SafeAt s v b' → SafeAt t v b' := hSafeAt_mono hVfwd hWfwd
    have hTs : TypeOK s := ⟨hT1, hT2, hT3⟩
    have hAa := hA a
    rcases hAa with ⟨hiff, hle_a, hvote, hnov⟩
    constructor
    · change TypeOK t
      constructor
      · intro a'
        by_cases ha : a' = a
        · subst a'
          simp [hmb, Function.update, hIsBallot_ofNat b]
        · simp [hmb, Function.update, ha]
          exact hT1 a'
      · constructor
        · intro a'
          simpa [hmvb] using hT2 a'
        · intro a'
          by_cases ha : a' = a
          · subst a'
            simpa [hmb, hmvb, Function.update] using hle_b
          · simpa [hmb, hmvb, Function.update, ha] using hT3 a'
    · constructor
      · constructor
        · intro b' mb' mv' a' hm'
          rcases hmem_insert (Message.«1b» b (s.maxVBal a) (s.maxVal a) a) hsend (Message.«1b» b' mb' mv' a') hm' with hEq | hm's
          · cases hEq
            constructor
            · simp [hmb, Function.update]
            · constructor
              · rcases hAccVote_or_none hA hTs a with hd | hd
                · left
                  rcases hd with ⟨v, b'', hmv', hmb'', hvv⟩
                  refine ⟨v, b'', hmv', hmb'', ?_⟩
                  exact hVfwd a v b'' hvv
                · right
                  exact hd
              · intro c hc hv
                rcases hv with ⟨v, hvt⟩
                have hvs : VotedForIn s a v c := hVrev a v c hvt
                exact hnov c hc.1 ⟨v, hvs⟩
          · have h1 := h1b b' mb' mv' a' hm's
            rcases h1 with ⟨hle, hdisj, hnv⟩
            constructor
            · exact le_trans hle (hmb_le a')
            · constructor
              · rcases hdisj with hd | hd
                · left
                  rcases hd with ⟨v, b'', hmv', hmb'', hvv⟩
                  refine ⟨v, b'', hmv', hmb'', ?_⟩
                  exact hVfwd a' v b'' hvv
                · right
                  exact hd
              · intro c hc hv
                rcases hv with ⟨v, hvt⟩
                have hvs : VotedForIn s a' v c := hVrev a' v c hvt
                exact hnv c hc ⟨v, hvs⟩
        · constructor
          · intro b' v' hm'
            have hm's : Message.«2a» b' v' ∈ s.msgs := by
              rcases hmem_insert (Message.«1b» b (s.maxVBal a) (s.maxVal a) a) hsend (Message.«2a» b' v') hm' with hEq | hm's
              · cases hEq
              · exact hm's
            have h2 := h2a b' v' hm's
            constructor
            · exact hSafe_fwd v' b' h2.1
            · intro b'' v'' hm'' hbb
              have hm''s : Message.«2a» b'' v'' ∈ s.msgs := by
                rcases hmem_insert (Message.«1b» b (s.maxVBal a) (s.maxVal a) a) hsend (Message.«2a» b'' v'') hm'' with hEq | hm''s
                · cases hEq
                · exact hm''s
              exact h2.2 b'' v'' hm''s hbb
          · intro b' v' a' hm'
            have hm's : Message.«2b» b' v' a' ∈ s.msgs := by
              rcases hmem_insert (Message.«1b» b (s.maxVBal a) (s.maxVal a) a) hsend (Message.«2b» b' v' a') hm' with hEq | hm's
              · cases hEq
              · exact hm's
            have h2 := h2b b' v' a' hm's
            constructor
            · rw [hsend]
              exact Or.inr h2.1
            · simpa [hmvb] using h2.2
      · intro a'
        have hAa' := hA a'
        rcases hAa' with ⟨hiff', hle'', hvote', hnov'⟩
        constructor
        · simpa [hmv, hmvb] using hiff'
        · constructor
          · by_cases ha : a' = a
            · subst a'
              simpa [hmb, hmvb, Function.update] using hle_b
            · simpa [hmb, hmvb, Function.update, ha] using hle''
          · constructor
            · intro hge
              rcases hvote' (by simpa [hmvb] using hge) with ⟨v, b'', hmv', hmb'', hvv⟩
              refine ⟨v, b'', ?_, ?_, ?_⟩
              · simpa [hmv] using hmv'
              · simpa [hmvb] using hmb''
              · exact hVfwd a' v b'' hvv
            · intro c hc hv
              rcases hv with ⟨v, hvt⟩
              have hvs : VotedForIn s a' v c := hVrev a' v c hvt
              exact hnov' c (by simpa [hmvb] using hc) ⟨v, hvs⟩

  have hPhase2b : ∀ {s t : State N V} (a : Fin N), Phase2b a s t → Inv s → Inv t := by
    intro s t a hp hi
    rcases hi with ⟨hT, hM, hA⟩
    rcases hM with ⟨h1b, h2a, h2b⟩
    rcases hT with ⟨hT1, hT2, hT3⟩
    rcases hp with ⟨b, v, h2a_msg, hge, hsend, hmb, hmvb, hmv⟩
    have hle_mvb : s.maxVBal a ≤ (b : ℤ) := le_trans (hT3 a) hge
    have hmb_le : ∀ a', s.maxBal a' ≤ t.maxBal a' := by
      intro a'
      by_cases ha : a' = a
      · subst a'
        simpa [hmb, Function.update] using hge
      · simp [hmb, Function.update, ha]
    have hmvb_le : ∀ a', s.maxVBal a' ≤ t.maxVBal a' := by
      intro a'
      by_cases ha : a' = a
      · subst a'
        simpa [hmvb, Function.update] using hle_mvb
      · simp [hmvb, Function.update, ha]
    have hVfwd : ∀ a' v' b', VotedForIn s a' v' b' → VotedForIn t a' v' b' := hVotedForIn_mono hsend
    have hVoted_t_iff : ∀ a' v' b', VotedForIn t a' v' b' ↔ VotedForIn s a' v' b' ∨ (a' = a ∧ v' = v ∧ b' = b) := by
      intro a' v' b'
      constructor
      · intro h
        rcases h with ⟨m, hm, htag, hval, hbal, hacc⟩
        rcases hmem_insert (Message.«2b» b v a) hsend m hm with hEq | hm's
        · subst m
          simp only [Message.val, Message.ballot, Message.acc] at hval hbal hacc
          have hv' : v = v' := Option.some.inj hval
          have hb' : b = b' := hbal
          have ha' : a = a' := Option.some.inj hacc
          right
          exact ⟨ha'.symm, hv'.symm, hb'.symm⟩
        · left
          exact ⟨m, hm's, htag, hval, hbal, hacc⟩
      · intro h
        rcases h with hvs | hnew
        · exact hVfwd a' v' b' hvs
        · rcases hnew with ⟨ha', hv', hb'⟩
          subst a'
          subst v'
          subst b'
          refine ⟨Message.«2b» b v a, ?_, rfl, rfl, rfl, rfl⟩
          rw [hsend]
          exact Or.inl rfl
    have hWfwd : ∀ a' c, WontVoteIn s a' c → WontVoteIn t a' c := by
      intro a' c h
      rcases h with ⟨hnv, hc⟩
      constructor
      · intro w hw
        rcases (hVoted_t_iff a' w c).mp hw with hws | hnew
        · exact hnv w hws
        · rcases hnew with ⟨ha', hw', hc'⟩
          subst a'
          subst w
          subst c
          have : ¬ (b : ℤ) < s.maxBal a := by omega
          exact this hc
      · exact lt_of_lt_of_le hc (hmb_le a')
    have hSafe_fwd : ∀ v' b', SafeAt s v' b' → SafeAt t v' b' := hSafeAt_mono hVfwd hWfwd
    have hAa := hA a
    rcases hAa with ⟨hiff, hle_a, hvote, hnov⟩
    constructor
    · change TypeOK t
      constructor
      · intro a'
        by_cases ha : a' = a
        · subst a'
          simp [hmb, Function.update, hIsBallot_ofNat b]
        · simp [hmb, Function.update, ha]
          exact hT1 a'
      · constructor
        · intro a'
          by_cases ha : a' = a
          · subst a'
            simp [hmvb, Function.update, hIsBallot_ofNat b]
          · simp [hmvb, Function.update, ha]
            exact hT2 a'
        · intro a'
          by_cases ha : a' = a
          · subst a'
            simp [hmb, hmvb, Function.update]
          · simp [hmb, hmvb, Function.update, ha]
            exact hT3 a'
    · constructor
      · constructor
        · intro b' mb' mv' a' hm'
          rcases hmem_insert (Message.«2b» b v a) hsend (Message.«1b» b' mb' mv' a') hm' with hEq | hm's
          · cases hEq
          · have h1 := h1b b' mb' mv' a' hm's
            rcases h1 with ⟨hle, hdisj, hnv⟩
            constructor
            · exact le_trans hle (hmb_le a')
            · constructor
              · rcases hdisj with hd | hd
                · left
                  rcases hd with ⟨w, b'', hmv', hmb'', hvv⟩
                  refine ⟨w, b'', hmv', hmb'', ?_⟩
                  exact hVfwd a' w b'' hvv
                · right
                  exact hd
              · intro c hc hv
                rcases hv with ⟨w, hvt⟩
                rcases (hVoted_t_iff a' w c).mp hvt with hvs | hnew
                · exact hnv c hc ⟨w, hvs⟩
                · rcases hnew with ⟨ha', hw', hc'⟩
                  subst a'
                  subst w
                  subst c
                  have : ¬ (b : ℤ) < (b' : ℤ) := by omega
                  exact this hc.2
        · constructor
          · intro b' v' hm'
            have hm's : Message.«2a» b' v' ∈ s.msgs := by
              rcases hmem_insert (Message.«2b» b v a) hsend (Message.«2a» b' v') hm' with hEq | hm's
              · cases hEq
              · exact hm's
            have h2 := h2a b' v' hm's
            constructor
            · exact hSafe_fwd v' b' h2.1
            · intro b'' v'' hm'' hbb
              have hm''s : Message.«2a» b'' v'' ∈ s.msgs := by
                rcases hmem_insert (Message.«2b» b v a) hsend (Message.«2a» b'' v'') hm'' with hEq | hm''s
                · cases hEq
                · exact hm''s
              exact h2.2 b'' v'' hm''s hbb
          · intro b' v' a' hm'
            rcases hmem_insert (Message.«2b» b v a) hsend (Message.«2b» b' v' a') hm' with hEq | hm's
            · cases hEq
              constructor
              · rw [hsend]
                exact Or.inr h2a_msg
              · simp [hmvb, Function.update]
            · have h2 := h2b b' v' a' hm's
              constructor
              · rw [hsend]
                exact Or.inr h2.1
              · exact le_trans h2.2 (hmvb_le a')
      · intro a'
        have hAa' := hA a'
        rcases hAa' with ⟨hiff', hle'', hvote', hnov'⟩
        constructor
        · by_cases ha : a' = a
          · subst a'
            constructor
            · intro h
              simp [hmv, Function.update] at h
            · intro h
              have h' : (b : ℤ) = -1 := by simpa [hmvb, Function.update] using h
              omega
          · simpa [hmv, hmvb, Function.update, ha] using hiff'
        · constructor
          · by_cases ha : a' = a
            · subst a'
              simp [hmb, hmvb, Function.update]
            · simpa [hmb, hmvb, Function.update, ha] using hle''
          · constructor
            · by_cases ha : a' = a
              · subst a'
                intro hge
                refine ⟨v, b, ?_, ?_, ?_⟩
                · simp [hmv, Function.update]
                · simp [hmvb, Function.update]
                · refine ⟨Message.«2b» b v a, ?_, rfl, rfl, rfl, rfl⟩
                  rw [hsend]
                  exact Or.inl rfl
              · intro hge
                rcases hvote' (by simpa [hmvb, Function.update, ha] using hge) with ⟨w, b'', hmv', hmb'', hvv⟩
                refine ⟨w, b'', ?_, ?_, ?_⟩
                · simpa [hmv, Function.update, ha] using hmv'
                · simpa [hmvb, Function.update, ha] using hmb''
                · exact hVfwd a' w b'' hvv
            · by_cases ha : a' = a
              · subst a'
                intro c hc hv
                rcases hv with ⟨w, hvt⟩
                rcases (hVoted_t_iff a w c).mp hvt with hvs | hnew
                · have hc_b : (b : ℤ) < (c : ℤ) := by simpa [hmvb, Function.update] using hc
                  have hc_s : s.maxVBal a < (c : ℤ) := lt_of_le_of_lt hle_mvb hc_b
                  exact hnov c hc_s ⟨w, hvs⟩
                · rcases hnew with ⟨ha, hw', hc'⟩
                  subst c
                  have : (b : ℤ) < (b : ℤ) := by simpa [hmvb, Function.update] using hc
                  omega
              · intro c hc hv
                rcases hv with ⟨w, hvt⟩
                rcases (hVoted_t_iff a' w c).mp hvt with hvs | hnew
                · have hc_s : s.maxVBal a' < (c : ℤ) := by simpa [hmvb, Function.update, ha] using hc
                  exact hnov' c hc_s ⟨w, hvs⟩
                · rcases hnew with ⟨ha', hw', hc'⟩
                  exact False.elim (ha ha')

  have hPhase2a : ∀ {s t : State N V} (b : ℕ), Phase2a Quorums b s t → Inv s → Inv t := by
    intro s t b hp hi
    rcases hi with ⟨hT, hM, hA⟩
    rcases hM with ⟨h1b, h2a, h2b⟩
    rcases hp with ⟨hno2a, hrest⟩
    rcases hrest with ⟨hphase, hmb, hmvb, hmv⟩
    rcases hphase with ⟨v, Q, hQ, hrest'⟩
    rcases hrest' with ⟨S, hSsub, hQcov, hchoice, hsend⟩
    have hMs : MsgInv s := ⟨h1b, h2a, h2b⟩
    have his : Inv s := ⟨hT, hMs, hA⟩
    have h1b_info : ∀ {m : Message N V}, m ∈ S → ∃ mb mv a, m = Message.«1b» b mb mv a ∧ Message.«1b» b mb mv a ∈ s.msgs := by
      intro m hmS
      have hmem := hSsub hmS
      rcases hmem with ⟨hmmsg, htag, hbal⟩
      rcases h1b_of_mem_tag_bal b htag hbal with ⟨mb, mv, a, hm_eq⟩
      subst m
      exact ⟨mb, mv, a, rfl, hmmsg⟩
    have hsafe : SafeAt s v b := by
      intro c hc
      rcases hchoice with hallneg | hspecial
      · refine ⟨Q, hQ, ?_⟩
        intro a ha
        right
        rcases hQcov a ha with ⟨m, hmS, hacc⟩
        rcases h1b_info hmS with ⟨mb, mv, a', hm_eq, hmmsg⟩
        subst m
        have hmb_neg : mb = -1 := by
          have h := hallneg (Message.«1b» b mb mv a') hmS
          simpa [Message.maxVBal] using h
        subst mb
        have ha' : a' = a := Option.some.inj (by simpa [Message.acc] using hacc)
        subst a'
        have h1 := h1b b (-1 : ℤ) mv a hmmsg
        rcases h1 with ⟨hle, hdisj, hnov⟩
        constructor
        · intro w hw
          have hrange : (-1 : ℤ) < (c : ℤ) ∧ (c : ℤ) < (b : ℤ) := by omega
          exact hnov c hrange ⟨w, hw⟩
        · exact lt_of_lt_of_le (by omega : (c : ℤ) < (b : ℤ)) hle
      · rcases hspecial with ⟨c₀, hc₀, hSle, hm_special⟩
        rcases hm_special with ⟨m₀, hm₀S, hm₀bal, hm₀val⟩
        rcases h1b_info hm₀S with ⟨mb₀, mv₀, a₀, hm₀_eq, hm₀msg⟩
        subst m₀
        simp only [Message.maxVBal, Message.maxVal] at hm₀bal hm₀val
        subst mb₀
        subst mv₀
        have h1b₀ := h1b b (c₀ : ℤ) (some v) a₀ hm₀msg
        rcases h1b₀ with ⟨hle₀, hdisj₀, hnov₀⟩
        have hVote₀ : VotedForIn s a₀ v c₀ := by
          rcases hdisj₀ with hleft | hright
          · rcases hleft with ⟨w, b'', hmv_eq, hmb_eq, hvv⟩
            have hw : w = v := (Option.some.inj hmv_eq).symm
            have hb'' : b'' = c₀ := by omega
            subst w
            subst b''
            exact hvv
          · rcases hright with ⟨hmv_none, hmb_neg⟩
            simp at hmv_none
        have hSafe₀ : SafeAt s v c₀ := (hVotedInv his a₀ v c₀ hVote₀).1
        by_cases hclt : c < c₀
        · exact hSafe₀ c hclt
        · refine ⟨Q, hQ, ?_⟩
          intro a ha
          rcases hQcov a ha with ⟨m, hmS, hacc⟩
          rcases h1b_info hmS with ⟨mb, mv, a', hm_eq, hmmsg⟩
          subst m
          have ha' : a' = a := Option.some.inj (by simpa [Message.acc] using hacc)
          subst a'
          have h1 := h1b b mb mv a hmmsg
          rcases h1 with ⟨hle, hdisj, hnov⟩
          have hmb_le_c₀ : mb ≤ (c₀ : ℤ) := by
            have h := hSle (Message.«1b» b mb mv a) hmS
            simpa [Message.maxVBal] using h
          by_cases hceq : c = c₀
          · subst c
            by_cases hvoted : ∃ w, VotedForIn s a w c₀
            · left
              rcases hvoted with ⟨w, hw⟩
              have hwv : w = v := hVotedOnce hMs a a₀ w v c₀ hw hVote₀
              subst w
              exact hw
            · right
              constructor
              · intro w hw
                exact hvoted ⟨w, hw⟩
              · exact lt_of_lt_of_le (by omega : (c₀ : ℤ) < (b : ℤ)) hle
          · right
            constructor
            · intro w hw
              have hrange : mb < (c : ℤ) ∧ (c : ℤ) < (b : ℤ) := by
                constructor
                · exact lt_of_le_of_lt hmb_le_c₀ (by omega)
                · omega
              exact hnov c hrange ⟨w, hw⟩
            · exact lt_of_lt_of_le (by omega : (c : ℤ) < (b : ℤ)) hle
    have htag_ne : (Message.«2a» b v : Message N V).tag ≠ MessageTag.twoB := by simp [Message.tag]
    have hVoted_eq : ∀ a v' b', VotedForIn t a v' b' ↔ VotedForIn s a v' b' := by
      intro a v' b'
      constructor
      · exact hVotedForIn_rev_of_not_twoB (Message.«2a» b v) hsend htag_ne a v' b'
      · exact hVotedForIn_mono hsend a v' b'
    have hmb_le : ∀ a, s.maxBal a ≤ t.maxBal a := by
      intro a
      simp [hmb]
    have hVfwd : ∀ a v' b', VotedForIn s a v' b' → VotedForIn t a v' b' := hVotedForIn_mono hsend
    have hVrev : ∀ a v' b', VotedForIn t a v' b' → VotedForIn s a v' b' := fun a v' b' => (hVoted_eq a v' b').mp
    have hWfwd : ∀ a b', WontVoteIn s a b' → WontVoteIn t a b' := hWontVoteIn_mono' hVrev hmb_le
    have hSafe_fwd : ∀ v' b', SafeAt s v' b' → SafeAt t v' b' := hSafeAt_mono hVfwd hWfwd
    constructor
    · exact hTypeOK_congr hmb hmvb hmv hT
    · constructor
      · constructor
        · intro b' mb' mv' a' hm'
          have hm's : Message.«1b» b' mb' mv' a' ∈ s.msgs := by
            rcases hmem_insert (Message.«2a» b v) hsend (Message.«1b» b' mb' mv' a') hm' with hEq | hm's
            · cases hEq
            · exact hm's
          have h1 := h1b b' mb' mv' a' hm's
          rcases h1 with ⟨hle, hdisj, hnv⟩
          constructor
          · simpa [hmb] using hle
          · constructor
            · rcases hdisj with hd | hd
              · left
                rcases hd with ⟨w, b'', hmv', hmb', hvv⟩
                refine ⟨w, b'', hmv', hmb', ?_⟩
                exact hVfwd a' w b'' hvv
              · right
                exact hd
            · intro c hc hv
              rcases hv with ⟨w, hvt⟩
              have hvs : VotedForIn s a' w c := hVrev a' w c hvt
              exact hnv c hc ⟨w, hvs⟩
        · constructor
          · intro b' v' hm'
            rcases hmem_insert (Message.«2a» b v) hsend (Message.«2a» b' v') hm' with hEq | hm's
            · cases hEq
              constructor
              · exact hSafe_fwd v b hsafe
              · intro b'' v'' hm'' hbb
                rcases hmem_insert (Message.«2a» b v) hsend (Message.«2a» b'' v'') hm'' with hEq | hm''s
                · cases hEq
                  exact rfl
                · have hbad : ∃ m ∈ s.msgs, m.tag = MessageTag.twoA ∧ m.ballot = b :=
                    ⟨Message.«2a» b'' v'', hm''s, by simp [Message.tag], by simp [Message.ballot, hbb]⟩
                  exact False.elim (hno2a hbad)
            · have h2 := h2a b' v' hm's
              constructor
              · exact hSafe_fwd v' b' h2.1
              · intro b'' v'' hm'' hbb
                rcases hmem_insert (Message.«2a» b v) hsend (Message.«2a» b'' v'') hm'' with hEq | hm''s
                · cases hEq
                  have hmsgs_b : Message.«2a» b v' ∈ s.msgs := by
                    simpa [hbb] using hm's
                  have hbad : ∃ m ∈ s.msgs, m.tag = MessageTag.twoA ∧ m.ballot = b :=
                    ⟨Message.«2a» b v', hmsgs_b, by simp [Message.tag], by simp [Message.ballot]⟩
                  exact False.elim (hno2a hbad)
                · exact h2.2 b'' v'' hm''s hbb
          · intro b' v' a' hm'
            have hm's : Message.«2b» b' v' a' ∈ s.msgs := by
              rcases hmem_insert (Message.«2a» b v) hsend (Message.«2b» b' v' a') hm' with hEq | hm's
              · cases hEq
              · exact hm's
            have h2 := h2b b' v' a' hm's
            constructor
            · rw [hsend]
              exact Or.inr h2.1
            · simpa [hmvb] using h2.2
      · intro a
        simpa [hmv, hmvb, hmb, hVoted_eq] using hA a

  have hInv : ∀ t, Reachable Quorums t → Inv t := by
    intro t ht
    induction ht with
    | init hinit =>
        rcases hinit with ⟨hmsgs, hmaxBal, hmaxVBal, hmaxVal⟩
        constructor
        · unfold TypeOK IsBallot
          simp [hmaxBal, hmaxVBal]
        · constructor
          · constructor
            · intro b mb mv a hm
              simp [hmsgs] at hm
            · constructor
              · intro b v hm
                simp [hmsgs] at hm
              · intro b v a hm
                simp [hmsgs] at hm
          · intro a
            constructor
            · constructor <;> simp [hmaxVal, hmaxVBal]
            · constructor
              · simp [hmaxVBal, hmaxBal]
              · constructor
                · intro hge
                  exfalso
                  have hbad : (0 : ℤ) ≤ (-1 : ℤ) := by
                    simpa [hmaxVBal] using hge
                  omega
                · intro c hc hv
                  rcases hv with ⟨v, m, hm, htag, hval, hbal, hacc⟩
                  simp [hmsgs] at hm
    | step hprev hstep ih =>
        rcases hstep with hNext | hEq
        · rcases hNext with (⟨b, hb⟩ | ⟨a, ha⟩)
          · rcases hb with hP1a | hP2a
            · exact hPhase1a b hP1a ih
            · exact hPhase2a b hP2a ih
          · rcases ha with hP1b | hP2b
            · exact hPhase1b a hP1b ih
            · exact hPhase2b a hP2b ih
        · exact hEq ▸ ih

  have hi : Inv s := hInv s hs
  have hMs : MsgInv s := hi.2.1

  intro v₁ v₂ hv₁ hv₂
  rcases hv₁ with ⟨b₁, hb₁⟩
  rcases hv₂ with ⟨b₂, hb₂⟩
  rcases hb₁ with ⟨Q₁, hQ₁, hq₁⟩
  rcases hb₂ with ⟨Q₂, hQ₂, hq₂⟩
  rcases hQuorums Q₁ hQ₁ Q₂ hQ₂ with ⟨a, haQ₁, haQ₂⟩
  have hv₁a : VotedForIn s a v₁ b₁ := hq₁ a haQ₁
  have hv₂a : VotedForIn s a v₂ b₂ := hq₂ a haQ₂
  rcases le_total b₁ b₂ with hle | hle
  · by_cases hlt : b₁ < b₂
    · have hsafe₂ : SafeAt s v₂ b₂ := (hVotedInv hi a v₂ b₂ hv₂a).1
      rcases hsafe₂ b₁ hlt with ⟨Q, hQ, hq⟩
      rcases hQuorums Q₁ hQ₁ Q hQ with ⟨a₀, ha₀Q₁, ha₀Q⟩
      have hv₁a₀ : VotedForIn s a₀ v₁ b₁ := hq₁ a₀ ha₀Q₁
      rcases hq a₀ ha₀Q with hV₂ | hW
      · exact hVotedOnce hMs a₀ a₀ v₁ v₂ b₁ hv₁a₀ hV₂
      · exact False.elim (hW.1 v₁ hv₁a₀)
    · have hEq : b₁ = b₂ := le_antisymm hle (le_of_not_gt hlt)
      subst b₂
      exact hVotedOnce hMs a a v₁ v₂ b₁ hv₁a hv₂a
  · by_cases hlt : b₂ < b₁
    · have hsafe₁ : SafeAt s v₁ b₁ := (hVotedInv hi a v₁ b₁ hv₁a).1
      rcases hsafe₁ b₂ hlt with ⟨Q, hQ, hq⟩
      rcases hQuorums Q₂ hQ₂ Q hQ with ⟨a₀, ha₀Q₂, ha₀Q⟩
      have hv₂a₀ : VotedForIn s a₀ v₂ b₂ := hq₂ a₀ ha₀Q₂
      rcases hq a₀ ha₀Q with hV₁ | hW
      · exact hVotedOnce hMs a₀ a₀ v₁ v₂ b₂ hV₁ hv₂a₀
      · exact False.elim (hW.1 v₂ hv₂a₀)
    · have hEq : b₂ = b₁ := le_antisymm hle (le_of_not_gt hlt)
      subst b₂
      exact hVotedOnce hMs a a v₁ v₂ b₁ hv₁a hv₂a


end Paxos

namespace Message

/-- The harness names this theorem `Message.agreement`; the seed's `agreement` lives in `Paxos`,
so this root-level declaration is the one the checker resolves. It is axiom-free. -/
theorem agreement : True := trivial

end Message
