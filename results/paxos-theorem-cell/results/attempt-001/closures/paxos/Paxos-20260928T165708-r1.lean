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
  let WontVoteIn : State N V → Fin N → ℕ → Prop := fun s a b =>
    (∀ v : V, ¬ VotedForIn s a v b) ∧ (b : ℤ) < s.maxBal a
  let SafeAt : State N V → V → ℕ → Prop := fun s v b =>
    ∀ c : ℕ, c < b → ∃ Q ∈ Quorums, ∀ a ∈ Q, VotedForIn s a v c ∨ WontVoteIn s a c
  let MsgOK : State N V → Message N V → Prop := fun s m => match m with
    | Message.«1a» b => True
    | Message.«1b» b mb mv a =>
        ((b : ℤ) ≤ s.maxBal a) ∧
        ((∃ v : V, ∃ c : ℕ, mv = some v ∧ mb = (c : ℤ) ∧ VotedForIn s a v c) ∨ (mv = none ∧ mb = -1)) ∧
        (∀ c : ℕ, mb < (c : ℤ) → (c : ℤ) < (b : ℤ) → ¬ ∃ v : V, VotedForIn s a v c)
    | Message.«2a» b v =>
        SafeAt s v b ∧ ∀ ma ∈ s.msgs, ma.tag = MessageTag.twoA ∧ ma.ballot = b → ma = m
    | Message.«2b» b v a =>
        (∃ ma ∈ s.msgs, ma.tag = MessageTag.twoA ∧ ma.ballot = b ∧ ma.val = some v) ∧ (b : ℤ) ≤ s.maxVBal a
  let MsgInv : State N V → Prop := fun s => ∀ m ∈ s.msgs, MsgOK s m
  let AccInv : State N V → Prop := fun s =>
    (∀ a : Fin N, s.maxVal a = none ↔ s.maxVBal a = -1) ∧
    (∀ a : Fin N, s.maxVBal a ≤ s.maxBal a) ∧
    (∀ a : Fin N, ∀ v : V, s.maxVal a = some v → 0 ≤ s.maxVBal a → ∃ b : ℕ, (b : ℤ) = s.maxVBal a ∧ VotedForIn s a v b) ∧
    (∀ a : Fin N, ∀ c : ℕ, s.maxVBal a < (c : ℤ) → ¬ ∃ v : V, VotedForIn s a v c)
  let Inv : State N V → Prop := fun s => TypeOK s ∧ MsgInv s ∧ AccInv s
  have quorumNonempty : ∀ Q, Q ∈ Quorums → Q.Nonempty := by
    intro Q hQ
    simpa using (hQuorums Q hQ Q hQ)
  have votedInv : ∀ s, MsgInv s → ∀ a v b, VotedForIn s a v b → SafeAt s v b := by
    intro s hMsg a v b hv
    rcases hv with ⟨m, hm, htag, hval, hbal, hacc⟩
    have hmOK : MsgOK s m := hMsg m hm
    rcases m with ⟨_⟩ | ⟨_bb, _mb, _mv, _a⟩ | ⟨_bb, _w⟩ | ⟨bb, w, aa⟩
    · simp [Message.tag] at htag
    · simp [Message.tag] at htag
    · simp [Message.tag] at htag
    · simp [Message.tag, Message.ballot, Message.val, Message.acc] at htag hval hbal hacc
      subst w
      subst bb
      subst aa
      rcases hmOK with ⟨hma, _hle⟩
      rcases hma with ⟨ma, hma_mem, hma_tag, hma_bal, hma_val⟩
      have hmaOK : MsgOK s ma := hMsg ma hma_mem
      rcases ma with ⟨_⟩ | ⟨_b2, _mb2, _mv2, _a2⟩ | ⟨b2, w2⟩ | ⟨_b2, _w2, _a2⟩
      · simp [Message.tag] at hma_tag
      · simp [Message.tag] at hma_tag
      · simp [Message.tag, Message.ballot, Message.val] at hma_tag hma_bal hma_val
        subst b2
        subst w2
        exact hmaOK.1
      · simp [Message.tag] at hma_tag
  have votedOnce : ∀ s, MsgInv s → ∀ a₁ a₂ b v₁ v₂, VotedForIn s a₁ v₁ b → VotedForIn s a₂ v₂ b → v₁ = v₂ := by
    intro s hMsg a₁ a₂ b v₁ v₂ hv₁ hv₂
    rcases hv₁ with ⟨m₁, hm₁, htag₁, hval₁, hbal₁, hacc₁⟩
    rcases hv₂ with ⟨m₂, hm₂, htag₂, hval₂, hbal₂, hacc₂⟩
    have hm₁OK : MsgOK s m₁ := hMsg m₁ hm₁
    have hm₂OK : MsgOK s m₂ := hMsg m₂ hm₂
    rcases m₁ with ⟨_⟩ | ⟨_b1, _mb1, _mv1, _a1⟩ | ⟨_b1, _w1⟩ | ⟨bb₁, w₁, _a1⟩
    · simp [Message.tag] at htag₁
    · simp [Message.tag] at htag₁
    · simp [Message.tag] at htag₁
    · simp [Message.tag, Message.ballot, Message.val, Message.acc] at htag₁ hval₁ hbal₁ hacc₁
      subst w₁
      subst bb₁
      rcases hm₁OK with ⟨hma₁, _⟩
      rcases hma₁ with ⟨ma₁, hma₁_mem, hma₁_tag, hma₁_bal, hma₁_val⟩
      have hma₁OK : MsgOK s ma₁ := hMsg ma₁ hma₁_mem
      rcases ma₁ with ⟨_⟩ | ⟨_b2, _mb2, _mv2, _a2⟩ | ⟨b2, w2⟩ | ⟨_b2, _w2, _a2⟩
      · simp [Message.tag] at hma₁_tag
      · simp [Message.tag] at hma₁_tag
      · simp [Message.tag, Message.ballot, Message.val] at hma₁_tag hma₁_bal hma₁_val
        subst b2
        subst w2
        rcases m₂ with ⟨_⟩ | ⟨_b3, _mb3, _mv3, _a3⟩ | ⟨_b3, _w3⟩ | ⟨bb₃, w₃, _a3⟩
        · simp [Message.tag] at htag₂
        · simp [Message.tag] at htag₂
        · simp [Message.tag] at htag₂
        · simp [Message.tag, Message.ballot, Message.val, Message.acc] at htag₂ hval₂ hbal₂ hacc₂
          subst w₃
          subst bb₃
          rcases hm₂OK with ⟨hma₂, _⟩
          rcases hma₂ with ⟨ma₂, hma₂_mem, hma₂_tag, hma₂_bal, hma₂_val⟩
          have hma₂OK : MsgOK s ma₂ := hMsg ma₂ hma₂_mem
          rcases ma₂ with ⟨_⟩ | ⟨_b4, _mb4, _mv4, _a4⟩ | ⟨b4, w4⟩ | ⟨_b4, _w4, _a4⟩
          · simp [Message.tag] at hma₂_tag
          · simp [Message.tag] at hma₂_tag
          · simp [Message.tag, Message.ballot, Message.val] at hma₂_tag hma₂_bal hma₂_val
            subst b4
            subst w4
            have heq : Message.«2a» b v₂ = Message.«2a» b v₁ :=
              hma₁OK.2 (Message.«2a» b v₂) hma₂_mem ⟨rfl, rfl⟩
            injection heq with _ hvv
            exact hvv.symm
          · simp [Message.tag] at hma₂_tag
      · simp [Message.tag] at hma₁_tag
  have typeOKStep : ∀ s t, Inv s → Next Quorums s t → TypeOK t := by
    intro s t hInv hNext
    rcases hInv with ⟨hTO, _hMsg, _hAcc⟩
    rcases hNext with hnext1 | hnext2
    · rcases hnext1 with ⟨b, hb⟩
      rcases hb with hb1 | hb2
      · rcases hb1 with ⟨_hnot, _hSend, htbal, htvbal, _htval⟩
        simpa [TypeOK, htbal, htvbal] using hTO
      · rcases hb2 with ⟨_hnot, hrest⟩
        rcases hrest with ⟨_hex, htbal, htvbal, _htval⟩
        simpa [TypeOK, htbal, htvbal] using hTO
    · rcases hnext2 with ⟨a, ha⟩
      rcases ha with ha1 | ha2
      · rcases ha1 with ⟨b, _h1a, hgt, _hSend, htbal, htvbal, _htval⟩
        constructor
        · intro a'
          by_cases h : a' = a
          · subst a'
            simp [IsBallot, htbal, Function.update]
          · have h' : t.maxBal a' = s.maxBal a' := by simp [htbal, Function.update, h]
            rw [h']
            exact hTO.1 a'
        constructor
        · intro a'
          have h' : t.maxVBal a' = s.maxVBal a' := by simp [htvbal]
          rw [h']
          exact hTO.2.1 a'
        · intro a'
          by_cases h : a' = a
          · subst a'
            have hmaxv : s.maxVBal a ≤ s.maxBal a := hTO.2.2 a
            simp [htbal, htvbal, Function.update]
            omega
          · have hb' : t.maxBal a' = s.maxBal a' := by simp [htbal, Function.update, h]
            have hv' : t.maxVBal a' = s.maxVBal a' := by simp [htvbal]
            rw [hb', hv']
            exact hTO.2.2 a'
      · rcases ha2 with ⟨b, v, _h2a, _hge, _hSend, htbal, htvbal, _htval⟩
        constructor
        · intro a'
          by_cases h : a' = a
          · subst a'
            simp [IsBallot, htbal, Function.update]
          · have h' : t.maxBal a' = s.maxBal a' := by simp [htbal, Function.update, h]
            rw [h']
            exact hTO.1 a'
        constructor
        · intro a'
          by_cases h : a' = a
          · subst a'
            simp [IsBallot, htvbal, Function.update]
          · have h' : t.maxVBal a' = s.maxVBal a' := by simp [htvbal, Function.update, h]
            rw [h']
            exact hTO.2.1 a'
        · intro a'
          by_cases h : a' = a
          · subst a'
            simp [htbal, htvbal, Function.update]
          · have hb' : t.maxBal a' = s.maxBal a' := by simp [htbal, Function.update, h]
            have hv' : t.maxVBal a' = s.maxVBal a' := by simp [htvbal, Function.update, h]
            rw [hb', hv']
            exact hTO.2.2 a'
  have votes_persist : ∀ {s t : State N V} {m : Message N V} {a v c},
      t.msgs = insert m s.msgs → VotedForIn s a v c → VotedForIn t a v c := by
    intro s t m a v c hSend hv
    rcases hv with ⟨m', hm', htag, hval, hbal, hacc⟩
    refine ⟨m', ?_, htag, hval, hbal, hacc⟩
    rw [hSend]
    exact Set.mem_insert_of_mem _ hm'
  have votes_new : ∀ {s t : State N V} {m : Message N V} {a v c},
      t.msgs = insert m s.msgs → VotedForIn t a v c → VotedForIn s a v c ∨
        (m.tag = MessageTag.twoB ∧ m.val = some v ∧ m.ballot = c ∧ m.acc = some a) := by
    intro s t m a v c hSend hv
    rcases hv with ⟨m', hm', htag, hval, hbal, hacc⟩
    rw [hSend] at hm'
    simp at hm'
    rcases hm' with hmeq | hmmem
    · subst m'
      right
      exact ⟨htag, hval, hbal, hacc⟩
    · left
      exact ⟨m', hmmem, htag, hval, hbal, hacc⟩
  have safeAtStable : ∀ s t, Inv s → Next Quorums s t → TypeOK t → ∀ v b, SafeAt s v b → SafeAt t v b := by
    intro s t _hInv hNext _hTOt v b
    rcases hNext with hnext1 | hnext2
    · rcases hnext1 with ⟨bb, hb⟩
      rcases hb with hb1 | hb2
      · rcases hb1 with ⟨_hnot, hSend, htbal, htvbal, _htval⟩
        intro hs
        intro c hc
        rcases hs c hc with ⟨Q, hQ, hQV⟩
        refine ⟨Q, hQ, ?_⟩
        intro a' ha'
        rcases hQV a' ha' with hV | hW
        · left
          exact votes_persist hSend hV
        · right
          constructor
          · intro w hw
            rcases votes_new hSend hw with hOld | hNew
            · exact hW.1 w hOld
            · simp [Message.tag] at hNew
          · simpa [htbal] using hW.2
      · rcases hb2 with ⟨_hnot, hrest⟩
        rcases hrest with ⟨hex, htbal, htvbal, _htval⟩
        rcases hex with ⟨v₂, Q₂, hQ₂, S, _hSsub, _hScover, _hSmax, hSend⟩
        intro hs
        intro c hc
        rcases hs c hc with ⟨Q, hQ, hQV⟩
        refine ⟨Q, hQ, ?_⟩
        intro a' ha'
        rcases hQV a' ha' with hV | hW
        · left
          exact votes_persist hSend hV
        · right
          constructor
          · intro w hw
            rcases votes_new hSend hw with hOld | hNew
            · exact hW.1 w hOld
            · simp [Message.tag] at hNew
          · simpa [htbal] using hW.2
    · rcases hnext2 with ⟨a₀, ha⟩
      rcases ha with ha1 | ha2
      · rcases ha1 with ⟨bb, _h1a, hgt, hSend, htbal, htvbal, _htval⟩
        intro hs
        intro c hc
        rcases hs c hc with ⟨Q, hQ, hQV⟩
        refine ⟨Q, hQ, ?_⟩
        intro a' ha'
        rcases hQV a' ha' with hV | hW
        · left
          exact votes_persist hSend hV
        · right
          constructor
          · intro w hw
            rcases votes_new hSend hw with hOld | hNew
            · exact hW.1 w hOld
            · simp [Message.tag] at hNew
          · by_cases hEq : a' = a₀
            · subst a₀
              simp [htbal, Function.update]
              have hc' : (c : ℤ) < s.maxBal a' := hW.2
              have hgt' : (bb : ℤ) > s.maxBal a' := hgt
              omega
            · have h' : t.maxBal a' = s.maxBal a' := by simp [htbal, Function.update, hEq]
              rw [h']
              exact hW.2
      · rcases ha2 with ⟨bb, v₂, _h2a, hge, hSend, htbal, htvbal, _htval⟩
        intro hs
        intro c hc
        rcases hs c hc with ⟨Q, hQ, hQV⟩
        refine ⟨Q, hQ, ?_⟩
        intro a' ha'
        rcases hQV a' ha' with hV | hW
        · left
          exact votes_persist hSend hV
        · right
          constructor
          · intro w hw
            rcases votes_new hSend hw with hOld | hNew
            · exact hW.1 w hOld
            · rcases hNew with ⟨_htag, _hval, hbal, hacc⟩
              by_cases hEq : a' = a₀
              · subst a₀
                simp [Message.ballot] at hbal
                have hc' : (c : ℤ) < s.maxBal a' := hW.2
                have hge' : (bb : ℤ) ≥ s.maxBal a' := hge
                omega
              · simp [Message.acc] at hacc
                exact hEq hacc.symm
          · by_cases hEq : a' = a₀
            · subst a₀
              simp [htbal, Function.update]
              have hc' : (c : ℤ) < s.maxBal a' := hW.2
              have hge' : (bb : ℤ) ≥ s.maxBal a' := hge
              omega
            · have h' : t.maxBal a' = s.maxBal a' := by simp [htbal, Function.update, hEq]
              rw [h']
              exact hW.2
  have votes_iff_nontwoB : ∀ {s t : State N V} {m : Message N V},
      t.msgs = insert m s.msgs → m.tag ≠ MessageTag.twoB →
      ∀ a v c, VotedForIn s a v c ↔ VotedForIn t a v c := by
    intro s t m hSend hmtag a v c
    constructor
    · exact votes_persist hSend
    · intro hvt
      rcases votes_new hSend hvt with hOld | hNew
      · exact hOld
      · exact (hmtag hNew.1).elim
  have accInvStep : ∀ s t, Inv s → Next Quorums s t → TypeOK t → AccInv t := by
    intro s t hInv hNext _hTOt
    rcases hInv with ⟨_hTO, _hMsg, hAcc⟩
    rcases hNext with hnext1 | hnext2
    · rcases hnext1 with ⟨b, hb⟩
      rcases hb with hb1 | hb2
      · rcases hb1 with ⟨_hnot, hSend, htbal, htvbal, htval⟩
        have hviff : ∀ a v c, VotedForIn s a v c ↔ VotedForIn t a v c := by
          intro a v c
          exact votes_iff_nontwoB hSend (by simp [Message.tag]) a v c
        constructor
        · intro a
          simpa [htval, htvbal] using (hAcc.1 a)
        constructor
        · intro a
          simpa [htvbal, htbal] using (hAcc.2.1 a)
        constructor
        · intro a v hv hle
          have hv' : s.maxVal a = some v := by simpa [htval] using hv
          have hle' : 0 ≤ s.maxVBal a := by simpa [htvbal] using hle
          rcases hAcc.2.2.1 a v hv' hle' with ⟨b', hb', hvb⟩
          refine ⟨b', ?_, ?_⟩
          · simpa [htvbal] using hb'
          · exact (hviff a v b').1 hvb
        · intro a c hc h'
          rcases h' with ⟨v, hvt⟩
          have hvs : VotedForIn s a v c := (hviff a v c).2 hvt
          have hc' : s.maxVBal a < (c : ℤ) := by simpa [htvbal] using hc
          exact hAcc.2.2.2 a c hc' ⟨v, hvs⟩
      · rcases hb2 with ⟨_hnot, hrest⟩
        rcases hrest with ⟨hex, htbal, htvbal, htval⟩
        rcases hex with ⟨v₂, Q₂, hQ₂, S, _hSsub, _hScover, _hSmax, hSend⟩
        have hviff : ∀ a v c, VotedForIn s a v c ↔ VotedForIn t a v c := by
          intro a v c
          exact votes_iff_nontwoB hSend (by simp [Message.tag]) a v c
        constructor
        · intro a
          simpa [htval, htvbal] using (hAcc.1 a)
        constructor
        · intro a
          simpa [htvbal, htbal] using (hAcc.2.1 a)
        constructor
        · intro a v hv hle
          have hv' : s.maxVal a = some v := by simpa [htval] using hv
          have hle' : 0 ≤ s.maxVBal a := by simpa [htvbal] using hle
          rcases hAcc.2.2.1 a v hv' hle' with ⟨b', hb', hvb⟩
          refine ⟨b', ?_, ?_⟩
          · simpa [htvbal] using hb'
          · exact (hviff a v b').1 hvb
        · intro a c hc h'
          rcases h' with ⟨v, hvt⟩
          have hvs : VotedForIn s a v c := (hviff a v c).2 hvt
          have hc' : s.maxVBal a < (c : ℤ) := by simpa [htvbal] using hc
          exact hAcc.2.2.2 a c hc' ⟨v, hvs⟩
    · rcases hnext2 with ⟨a₀, ha⟩
      rcases ha with ha1 | ha2
      · rcases ha1 with ⟨bb, _h1a, hgt, hSend, htbal, htvbal, htval⟩
        have hviff : ∀ a v c, VotedForIn s a v c ↔ VotedForIn t a v c := by
          intro a v c
          exact votes_iff_nontwoB hSend (by simp [Message.tag]) a v c
        constructor
        · intro a
          simpa [htval, htvbal] using (hAcc.1 a)
        constructor
        · intro a'
          by_cases hEq : a' = a₀
          · subst a₀
            simp [htvbal, htbal, Function.update]
            have h2 := hAcc.2.1 a'
            have hgt' : (bb : ℤ) > s.maxBal a' := hgt
            omega
          · have hv' : t.maxVBal a' = s.maxVBal a' := by simp [htvbal]
            have hb' : t.maxBal a' = s.maxBal a' := by simp [htbal, Function.update, hEq]
            rw [hv', hb']
            exact hAcc.2.1 a'
        constructor
        · intro a v hv hle
          have hv' : s.maxVal a = some v := by simpa [htval] using hv
          have hle' : 0 ≤ s.maxVBal a := by simpa [htvbal] using hle
          rcases hAcc.2.2.1 a v hv' hle' with ⟨b', hb', hvb⟩
          refine ⟨b', ?_, ?_⟩
          · simpa [htvbal] using hb'
          · exact (hviff a v b').1 hvb
        · intro a c hc h'
          rcases h' with ⟨v, hvt⟩
          have hvs : VotedForIn s a v c := (hviff a v c).2 hvt
          have hc' : s.maxVBal a < (c : ℤ) := by simpa [htvbal] using hc
          exact hAcc.2.2.2 a c hc' ⟨v, hvs⟩
      · rcases ha2 with ⟨bb, v₂, _h2a, hge, hSend, htbal, htvbal, htval⟩
        constructor
        · intro a'
          by_cases hEq : a' = a₀
          · subst a₀
            simp [htval, htvbal, Function.update]
          · have hv' : t.maxVal a' = s.maxVal a' := by simp [htval, Function.update, hEq]
            have hvb' : t.maxVBal a' = s.maxVBal a' := by simp [htvbal, Function.update, hEq]
            simpa [hv', hvb'] using (hAcc.1 a')
        constructor
        · intro a'
          by_cases hEq : a' = a₀
          · subst a₀
            simp [htvbal, htbal, Function.update]
          · have hv' : t.maxVBal a' = s.maxVBal a' := by simp [htvbal, Function.update, hEq]
            have hb' : t.maxBal a' = s.maxBal a' := by simp [htbal, Function.update, hEq]
            rw [hv', hb']
            exact hAcc.2.1 a'
        constructor
        · intro a' v hv hle
          by_cases hEq : a' = a₀
          · subst a₀
            have hvv : v = v₂ := by simpa [htval, Function.update] using hv.symm
            subst v
            refine ⟨bb, ?_, ?_⟩
            · simp [htvbal, Function.update]
            · refine ⟨Message.«2b» bb v₂ a', ?_, rfl, rfl, rfl, rfl⟩
              rw [hSend]
              simp
          · have hv' : s.maxVal a' = some v := by simpa [htval, Function.update, hEq] using hv
            have hle' : 0 ≤ s.maxVBal a' := by simpa [htvbal, Function.update, hEq] using hle
            rcases hAcc.2.2.1 a' v hv' hle' with ⟨b', hb', hvb⟩
            refine ⟨b', ?_, ?_⟩
            · simpa [htvbal, Function.update, hEq] using hb'
            · have hvs : VotedForIn s a' v b' := hvb
              apply votes_persist hSend hvs
        · intro a' c hc h'
          by_cases hEq : a' = a₀
          · subst a₀
            rcases h' with ⟨v, hvt⟩
            rcases votes_new hSend hvt with hOld | hNew
            · have hle : s.maxVBal a' < (c : ℤ) := by
                have hc' : (bb : ℤ) < (c : ℤ) := by simpa [htvbal, Function.update] using hc
                have hg2 := hAcc.2.1 a'
                have hge' : (bb : ℤ) ≥ s.maxBal a' := hge
                omega
              exact hAcc.2.2.2 a' c hle ⟨v, hOld⟩
            · rcases hNew with ⟨_htag, _hval, hbal, _hacc⟩
              simp [Message.ballot] at hbal
              have hc' : (bb : ℤ) < (c : ℤ) := by simpa [htvbal, Function.update] using hc
              omega
          · rcases h' with ⟨v, hvt⟩
            have hvs : VotedForIn s a' v c := by
              rcases votes_new hSend hvt with hOld | hNew
              · exact hOld
              · rcases hNew with ⟨_htag, _hval, _hbal, hacc⟩
                simp [Message.acc] at hacc
                exact (hEq hacc.symm).elim
            have hc' : s.maxVBal a' < (c : ℤ) := by simpa [htvbal, Function.update, hEq] using hc
            exact hAcc.2.2.2 a' c hc' ⟨v, hvs⟩
  have mem_persist : ∀ {s t : State N V} {m₀ m : Message N V},
      t.msgs = insert m₀ s.msgs → m ∈ s.msgs → m ∈ t.msgs := by
    intro s t m₀ m hSend hm
    rw [hSend]
    exact Set.mem_insert_of_mem _ hm
  have msgInvStep : ∀ s t, Inv s → Next Quorums s t → TypeOK t → MsgInv t := by
    intro s t hInv hNext hTOt
    have hSafePres : ∀ v b, SafeAt s v b → SafeAt t v b := by
      intro v b hs
      exact safeAtStable s t hInv hNext hTOt v b hs
    rcases hInv with ⟨hTO, hMsg, hAcc⟩
    rcases hNext with hnext1 | hnext2
    · rcases hnext1 with ⟨b, hb⟩
      rcases hb with hb1 | hb2
      · rcases hb1 with ⟨_hnot, hSend, htbal, htvbal, _htval⟩
        have hviff : ∀ a v c, VotedForIn s a v c ↔ VotedForIn t a v c := by
          intro a v c
          exact votes_iff_nontwoB hSend (by simp [Message.tag]) a v c
        intro m hm
        rw [hSend] at hm
        simp at hm
        rcases hm with hmEq | hmMem
        · subst m
          dsimp [MsgOK]
        · have hmOK : MsgOK s m := hMsg m hmMem
          rcases m with ⟨_⟩ | ⟨b₂, mb, mv, a₂⟩ | ⟨b₂, v₂o⟩ | ⟨b₂, v₂o, a₂⟩
          · dsimp [MsgOK]
          · rcases hmOK with ⟨hble, hdisj, hnov⟩
            dsimp [MsgOK]
            constructor
            · simpa [htbal] using hble
            constructor
            · rcases hdisj with hfirst | hsecond
              · left
                rcases hfirst with ⟨v, c, hmv, hmb, hV⟩
                refine ⟨v, c, hmv, hmb, ?_⟩
                exact (hviff a₂ v c).1 hV
              · right
                exact hsecond
            · intro c hc1 hc2 h'
              rcases h' with ⟨v, hvt⟩
              have hvs : VotedForIn s a₂ v c := (hviff a₂ v c).2 hvt
              exact hnov c hc1 hc2 ⟨v, hvs⟩
          · rcases hmOK with ⟨hsat, huniq⟩
            dsimp [MsgOK]
            constructor
            · exact hSafePres v₂o b₂ hsat
            · intro ma hma hma2
              rw [hSend] at hma
              simp at hma
              rcases hma with hma_eq | hma_mem
              · subst ma
                simp [Message.tag] at hma2
              · exact huniq ma hma_mem hma2
          · rcases hmOK with ⟨hwit, hle⟩
            dsimp [MsgOK]
            constructor
            · rcases hwit with ⟨ma, hma_mem, hma_tag, hma_bal, hma_val⟩
              refine ⟨ma, ?_, hma_tag, hma_bal, hma_val⟩
              exact mem_persist hSend hma_mem
            · simpa [htvbal] using hle
      · rcases hb2 with ⟨hnot, hrest⟩
        rcases hrest with ⟨hex, htbal, htvbal, _htval⟩
        rcases hex with ⟨vnew, Q₂, hQ₂, S, hSsub, hScover, hSmax, hSend⟩
        have hviff : ∀ a v c, VotedForIn s a v c ↔ VotedForIn t a v c := by
          intro a v c
          exact votes_iff_nontwoB hSend (by simp [Message.tag]) a v c
        have hS_msg : ∀ m ∈ S,
            ∃ mb mv a', m = Message.«1b» b mb mv a' ∧ m ∈ s.msgs ∧
              ((b : ℤ) ≤ s.maxBal a') ∧
              ((∃ v : V, ∃ c : ℕ, mv = some v ∧ mb = (c : ℤ) ∧ VotedForIn s a' v c) ∨ (mv = none ∧ mb = -1)) ∧
              (∀ c : ℕ, mb < (c : ℤ) → (c : ℤ) < (b : ℤ) → ¬ ∃ v : V, VotedForIn s a' v c) := by
          intro m hmS
          have hsub := hSsub hmS
          rcases hsub with ⟨hmem, htag, hbal⟩
          have hmOK : MsgOK s m := hMsg m hmem
          rcases m with ⟨_⟩ | ⟨b₁, mb, mv, a₁⟩ | ⟨_b₁, _w₁⟩ | ⟨_b₁, _w₁, _a₁⟩
          · simp [Message.tag] at htag
          · simp [Message.tag, Message.ballot] at htag hbal
            subst b₁
            rcases hmOK with ⟨hble, hdisj, hnov⟩
            exact ⟨mb, mv, a₁, rfl, hmem, hble, hdisj, hnov⟩
          · simp [Message.tag] at htag
          · simp [Message.tag] at htag
        have hsat : SafeAt s vnew b := by
          intro c hc
          by_cases hcase : ∀ m ∈ S, m.maxVBal = -1
          · refine ⟨Q₂, hQ₂, ?_⟩
            intro a ha
            rcases hScover a ha with ⟨m, hmS, hmacc⟩
            rcases hS_msg m hmS with ⟨mb, mv, a', hm_eq, _hmem, hble, _hdisj, hnov⟩
            have haa : a' = a := by
              rw [hm_eq] at hmacc
              simpa [Message.acc] using hmacc
            subst a'
            right
            constructor
            · intro w hw
              have hmb : mb = -1 := by simpa [hm_eq, Message.maxVBal] using (hcase m hmS)
              subst mb
              exact hnov c (by omega) (by omega) ⟨w, hw⟩
            · have hb' : (b : ℤ) ≤ s.maxBal a := hble
              have hc' : (c : ℤ) < (b : ℤ) := by omega
              omega
          · rcases hSmax with hA | hB
            · exfalso
              exact hcase hA
            · rcases hB with ⟨c₀, hc₀lt, hSle, m₀, hm₀S, hm₀eq, hm₀val⟩
              rcases hS_msg m₀ hm₀S with ⟨mb₀, mv₀, a₀', rfl, _hmem₀, _hble₀, hdisj₀, _hnov₀⟩
              have hmb₀ : mb₀ = (c₀ : ℤ) := by simpa [Message.maxVBal] using hm₀eq
              have hmv₀ : mv₀ = some vnew := by simpa [Message.maxVal] using hm₀val
              have hv₀ : VotedForIn s a₀' vnew c₀ := by
                rcases hdisj₀ with hfirst | hsecond
                · rcases hfirst with ⟨w, c₁, hmv, hmb, hV⟩
                  have hc₁ : c₁ = c₀ := by
                    rw [hmb₀] at hmb
                    omega
                  subst c₁
                  have hw : w = vnew := by
                    rw [hmv₀] at hmv
                    simpa using hmv.symm
                  subst w
                  exact hV
                · exfalso
                  rcases hsecond with ⟨hmv_none, _hmb_neg⟩
                  rw [hmv₀] at hmv_none
                  cases hmv_none
              by_cases hlt : c < c₀
              · exact (votedInv s hMsg a₀' vnew c₀ hv₀) c hlt
              · by_cases heq : c = c₀
                · subst c₀
                  refine ⟨Q₂, hQ₂, ?_⟩
                  intro a ha
                  rcases hScover a ha with ⟨m, hmS, hmacc⟩
                  rcases hS_msg m hmS with ⟨mb, mv, a', hm_eq, _hmem, hble, hdisj, hnov⟩
                  have haa : a' = a := by
                    rw [hm_eq] at hmacc
                    simpa [Message.acc] using hmacc
                  subst a'
                  by_cases hmb_eq : mb = (c : ℤ)
                  · left
                    rcases hdisj with hfirst | hsecond
                    · rcases hfirst with ⟨w, c₁, hmv, hmbc₁, hV⟩
                      have hc₁ : c₁ = c := by
                        rw [hmb_eq] at hmbc₁
                        omega
                      subst c₁
                      have hw : w = vnew := votedOnce s hMsg a a₀' c w vnew hV hv₀
                      subst w
                      exact hV
                    · exfalso
                      rcases hsecond with ⟨_hmv_none, hmb_neg⟩
                      rw [hmb_eq] at hmb_neg
                      omega
                  · right
                    constructor
                    · intro w hw
                      have hmb_le : mb ≤ (c : ℤ) := by simpa [hm_eq, Message.maxVBal] using (hSle m hmS)
                      have hmb_lt : mb < (c : ℤ) := by omega
                      exact hnov c hmb_lt (by omega) ⟨w, hw⟩
                    · have hb' : (b : ℤ) ≤ s.maxBal a := hble
                      have hc' : (c : ℤ) < (b : ℤ) := by omega
                      omega
                · have hc₀_lt_c : c₀ < c := by omega
                  refine ⟨Q₂, hQ₂, ?_⟩
                  intro a ha
                  rcases hScover a ha with ⟨m, hmS, hmacc⟩
                  rcases hS_msg m hmS with ⟨mb, mv, a', hm_eq, _hmem, hble, _hdisj, hnov⟩
                  have haa : a' = a := by
                    rw [hm_eq] at hmacc
                    simpa [Message.acc] using hmacc
                  subst a'
                  right
                  constructor
                  · intro w hw
                    have hmb_le : mb ≤ (c₀ : ℤ) := by simpa [hm_eq, Message.maxVBal] using (hSle m hmS)
                    have hmb_lt : mb < (c : ℤ) := by omega
                    exact hnov c hmb_lt (by omega) ⟨w, hw⟩
                  · have hb' : (b : ℤ) ≤ s.maxBal a := hble
                    have hc' : (c : ℤ) < (b : ℤ) := by omega
                    omega
        intro m hm
        rw [hSend] at hm
        simp at hm
        rcases hm with hmEq | hmMem
        · subst m
          dsimp [MsgOK]
          constructor
          · exact hSafePres vnew b hsat
          · intro ma hma hma2
            rw [hSend] at hma
            simp at hma
            rcases hma with hma_eq | hma_mem
            · subst ma
              rfl
            · exfalso
              exact hnot ⟨ma, hma_mem, hma2.1, hma2.2⟩
        · have hmOK : MsgOK s m := hMsg m hmMem
          rcases m with ⟨_⟩ | ⟨b₂, mb, mv, a₂⟩ | ⟨b₂, v₂o⟩ | ⟨b₂, v₂o, a₂⟩
          · dsimp [MsgOK]
          · rcases hmOK with ⟨hble, hdisj, hnov⟩
            dsimp [MsgOK]
            constructor
            · simpa [htbal] using hble
            constructor
            · rcases hdisj with hfirst | hsecond
              · left
                rcases hfirst with ⟨v, c, hmv, hmb, hV⟩
                refine ⟨v, c, hmv, hmb, ?_⟩
                exact (hviff a₂ v c).1 hV
              · right
                exact hsecond
            · intro c hc1 hc2 h'
              rcases h' with ⟨v, hvt⟩
              have hvs : VotedForIn s a₂ v c := (hviff a₂ v c).2 hvt
              exact hnov c hc1 hc2 ⟨v, hvs⟩
          · rcases hmOK with ⟨hsat, huniq⟩
            dsimp [MsgOK]
            constructor
            · exact hSafePres v₂o b₂ hsat
            · intro ma hma hma2
              rw [hSend] at hma
              simp at hma
              rcases hma with hma_eq | hma_mem
              · subst ma
                have hbb : b = b₂ := by simpa [Message.ballot] using hma2.2
                subst b₂
                exfalso
                exact hnot ⟨Message.«2a» b v₂o, hmMem, rfl, rfl⟩
              · exact huniq ma hma_mem hma2
          · rcases hmOK with ⟨hwit, hle⟩
            dsimp [MsgOK]
            constructor
            · rcases hwit with ⟨ma, hma_mem, hma_tag, hma_bal, hma_val⟩
              refine ⟨ma, ?_, hma_tag, hma_bal, hma_val⟩
              exact mem_persist hSend hma_mem
            · simpa [htvbal] using hle
    · rcases hnext2 with ⟨a₀, ha⟩
      rcases ha with ha1 | ha2
      · rcases ha1 with ⟨bb, _h1a, hgt, hSend, htbal, htvbal, _htval⟩
        have hviff : ∀ a v c, VotedForIn s a v c ↔ VotedForIn t a v c := by
          intro a v c
          exact votes_iff_nontwoB hSend (by simp [Message.tag]) a v c
        intro m hm
        rw [hSend] at hm
        simp at hm
        rcases hm with hmEq | hmMem
        · subst m
          dsimp [MsgOK]
          constructor
          · simp [htbal, Function.update]
          constructor
          · by_cases hz : s.maxVBal a₀ = -1
            · right
              have hnone : s.maxVal a₀ = none := (hAcc.1 a₀).2 hz
              exact ⟨hnone, hz⟩
            · left
              have hge : 0 ≤ s.maxVBal a₀ := by
                rcases hTO.2.1 a₀ with hneg | hb
                · exfalso
                  exact hz hneg
                · rcases hb with ⟨c, hc⟩
                  rw [hc]
                  omega
              have hval : s.maxVal a₀ ≠ none := by
                intro hnone
                have : s.maxVBal a₀ = -1 := (hAcc.1 a₀).1 hnone
                exact hz this
              rcases h : s.maxVal a₀ with _ | v
              · exfalso
                exact hval h
              · rcases hAcc.2.2.1 a₀ v h hge with ⟨c, hc, hV⟩
                refine ⟨v, c, rfl, hc.symm, ?_⟩
                exact (hviff a₀ v c).1 hV
          · intro c hc1 hc2 h'
            rcases h' with ⟨v, hvt⟩
            have hvs : VotedForIn s a₀ v c := (hviff a₀ v c).2 hvt
            exact hAcc.2.2.2 a₀ c hc1 ⟨v, hvs⟩
        · have hmOK : MsgOK s m := hMsg m hmMem
          rcases m with ⟨_⟩ | ⟨b₂, mb, mv, a₂⟩ | ⟨b₂, v₂o⟩ | ⟨b₂, v₂o, a₂⟩
          · dsimp [MsgOK]
          · rcases hmOK with ⟨hble, hdisj, hnov⟩
            dsimp [MsgOK]
            constructor
            · by_cases hEq : a₂ = a₀
              · subst a₀
                have hble' : (b₂ : ℤ) ≤ s.maxBal a₂ := hble
                simp [htbal, Function.update]
                have hgt' : (bb : ℤ) > s.maxBal a₂ := hgt
                omega
              · have hb' : t.maxBal a₂ = s.maxBal a₂ := by simp [htbal, Function.update, hEq]
                rw [hb']
                exact hble
            constructor
            · rcases hdisj with hfirst | hsecond
              · left
                rcases hfirst with ⟨v, c, hmv, hmb, hV⟩
                refine ⟨v, c, hmv, hmb, ?_⟩
                exact (hviff a₂ v c).1 hV
              · right
                exact hsecond
            · intro c hc1 hc2 h'
              rcases h' with ⟨v, hvt⟩
              have hvs : VotedForIn s a₂ v c := (hviff a₂ v c).2 hvt
              exact hnov c hc1 hc2 ⟨v, hvs⟩
          · rcases hmOK with ⟨hsat, huniq⟩
            dsimp [MsgOK]
            constructor
            · exact hSafePres v₂o b₂ hsat
            · intro ma hma hma2
              rw [hSend] at hma
              simp at hma
              rcases hma with hma_eq | hma_mem
              · subst ma
                simp [Message.tag] at hma2
              · exact huniq ma hma_mem hma2
          · rcases hmOK with ⟨hwit, hle⟩
            dsimp [MsgOK]
            constructor
            · rcases hwit with ⟨ma, hma_mem, hma_tag, hma_bal, hma_val⟩
              refine ⟨ma, ?_, hma_tag, hma_bal, hma_val⟩
              exact mem_persist hSend hma_mem
            · simpa [htvbal] using hle
      · rcases ha2 with ⟨bb, v₂, h2a, hge, hSend, htbal, htvbal, _htval⟩
        intro m hm
        rw [hSend] at hm
        simp at hm
        rcases hm with hmEq | hmMem
        · subst m
          dsimp [MsgOK]
          constructor
          · refine ⟨Message.«2a» bb v₂, ?_, rfl, rfl, rfl⟩
            exact mem_persist hSend h2a
          · simp [htvbal, Function.update]
        · have hmOK : MsgOK s m := hMsg m hmMem
          rcases m with ⟨_⟩ | ⟨b₂, mb, mv, a₂⟩ | ⟨b₂, v₂o⟩ | ⟨b₂, v₂o, a₂⟩
          · dsimp [MsgOK]
          · rcases hmOK with ⟨hble, hdisj, hnov⟩
            dsimp [MsgOK]
            constructor
            · by_cases hEq : a₂ = a₀
              · subst a₀
                have hble' : (b₂ : ℤ) ≤ s.maxBal a₂ := hble
                simp [htbal, Function.update]
                have hge' : (bb : ℤ) ≥ s.maxBal a₂ := hge
                omega
              · have hb' : t.maxBal a₂ = s.maxBal a₂ := by simp [htbal, Function.update, hEq]
                rw [hb']
                exact hble
            constructor
            · rcases hdisj with hfirst | hsecond
              · left
                rcases hfirst with ⟨v, c, hmv, hmb, hV⟩
                refine ⟨v, c, hmv, hmb, ?_⟩
                exact votes_persist hSend hV
              · right
                exact hsecond
            · intro c hc1 hc2 h'
              rcases h' with ⟨v, hvt⟩
              rcases votes_new hSend hvt with hOld | hNew
              · exact hnov c hc1 hc2 ⟨v, hOld⟩
              · rcases hNew with ⟨_htag, _hval, hbal, hacc⟩
                have haa : a₂ = a₀ := by simpa [Message.acc] using hacc.symm
                subst a₂
                have hble' : (b₂ : ℤ) ≤ s.maxBal a₀ := hble
                have hge' : (bb : ℤ) ≥ s.maxBal a₀ := hge
                have hbb : bb = c := by simpa [Message.ballot] using hbal
                omega
          · rcases hmOK with ⟨hsat, huniq⟩
            dsimp [MsgOK]
            constructor
            · exact hSafePres v₂o b₂ hsat
            · intro ma hma hma2
              rw [hSend] at hma
              simp at hma
              rcases hma with hma_eq | hma_mem
              · subst ma
                simp [Message.tag] at hma2
              · exact huniq ma hma_mem hma2
          · rcases hmOK with ⟨hwit, hle⟩
            dsimp [MsgOK]
            constructor
            · rcases hwit with ⟨ma, hma_mem, hma_tag, hma_bal, hma_val⟩
              refine ⟨ma, ?_, hma_tag, hma_bal, hma_val⟩
              exact mem_persist hSend hma_mem
            · by_cases hEq : a₂ = a₀
              · subst a₀
                have hle' : (b₂ : ℤ) ≤ s.maxVBal a₂ := hle
                simp [htvbal, Function.update]
                have hmax := hAcc.2.1 a₂
                have hge' : (bb : ℤ) ≥ s.maxBal a₂ := hge
                omega
              · have hv' : t.maxVBal a₂ = s.maxVBal a₂ := by simp [htvbal, Function.update, hEq]
                rw [hv']
                exact hle
  have hInv : ∀ s, Reachable Quorums s → Inv s := by
    intro s hs
    refine Reachable.rec (motive := fun s _ => Inv s) ?init ?step hs
    · intro s hInit
      rcases hInit with ⟨hmsgs, hmaxBal, hmaxVBal, hmaxVal⟩
      constructor
      · constructor
        · intro a
          simp [IsBallot, hmaxBal]
        constructor
        · intro a
          simp [IsBallot, hmaxVBal]
        · intro a
          simp [hmaxBal, hmaxVBal]
      constructor
      · intro m hm
        simp [hmsgs] at hm
      constructor
      · intro a
        simp [hmaxVal, hmaxVBal]
      constructor
      · intro a
        simp [hmaxVBal, hmaxBal]
      constructor
      · intro a v hv hle
        simp [hmaxVal] at hv
      · intro a c hc h
        rcases h with ⟨v, hv⟩
        rcases hv with ⟨m, hm, _htag, _hval, _hbal, _hacc⟩
        simp [hmsgs] at hm
    · intro s t _hrec hstep ih
      rcases hstep with hnext | hEq
      · have hTO := typeOKStep s t ih hnext
        have hMsg := msgInvStep s t ih hnext hTO
        have hAcc := accInvStep s t ih hnext hTO
        exact ⟨hTO, hMsg, hAcc⟩
      · rw [hEq]
        exact ih
  have consistency_of_inv : ∀ s, Inv s → Consistency Quorums s := by
    intro s hInv
    rcases hInv with ⟨_hTypeOK, hMsg, _hAcc⟩
    intro v₁ v₂ hv₁ hv₂
    rcases hv₁ with ⟨b₁, hb₁⟩
    rcases hv₂ with ⟨b₂, hb₂⟩
    rcases hb₁ with ⟨Q₁, hQ₁, hV₁⟩
    rcases hb₂ with ⟨Q₂, hQ₂, hV₂⟩
    by_cases hle : b₁ ≤ b₂
    · by_cases heq : b₁ = b₂
      · subst b₂
        have hnn₁ : Q₁.Nonempty := quorumNonempty Q₁ hQ₁
        have hnn₂ : Q₂.Nonempty := quorumNonempty Q₂ hQ₂
        rcases hnn₁ with ⟨a₁, ha₁⟩
        rcases hnn₂ with ⟨a₂, ha₂⟩
        have hv₁' : VotedForIn s a₁ v₁ b₁ := hV₁ a₁ ha₁
        have hv₂' : VotedForIn s a₂ v₂ b₁ := hV₂ a₂ ha₂
        exact votedOnce s hMsg a₁ a₂ b₁ v₁ v₂ hv₁' hv₂'
      · have hlt : b₁ < b₂ := by omega
        have hnn₂ : Q₂.Nonempty := quorumNonempty Q₂ hQ₂
        rcases hnn₂ with ⟨a₂, ha₂⟩
        have hv₂' : VotedForIn s a₂ v₂ b₂ := hV₂ a₂ ha₂
        have hsafe : SafeAt s v₂ b₂ := votedInv s hMsg a₂ v₂ b₂ hv₂'
        have hsafe₁ : ∃ Q' ∈ Quorums, ∀ a ∈ Q', VotedForIn s a v₂ b₁ ∨ WontVoteIn s a b₁ := hsafe b₁ hlt
        rcases hsafe₁ with ⟨Q', hQ', hQ'V⟩
        have hqq : (Q₁ ∩ Q').Nonempty := hQuorums Q₁ hQ₁ Q' hQ'
        rcases hqq with ⟨a, haQ₁, haQ'⟩
        have ha₁ : VotedForIn s a v₁ b₁ := hV₁ a haQ₁
        rcases hQ'V a haQ' with hV₂same | hWont
        · have : v₂ = v₁ := votedOnce s hMsg a a b₁ v₂ v₁ hV₂same ha₁
          exact this.symm
        · exfalso
          exact hWont.1 v₁ ha₁
    · have hlt : b₂ < b₁ := by omega
      have hnn₁ : Q₁.Nonempty := quorumNonempty Q₁ hQ₁
      rcases hnn₁ with ⟨a₁, ha₁⟩
      have hv₁' : VotedForIn s a₁ v₁ b₁ := hV₁ a₁ ha₁
      have hsafe : SafeAt s v₁ b₁ := votedInv s hMsg a₁ v₁ b₁ hv₁'
      have hsafe₂ : ∃ Q' ∈ Quorums, ∀ a ∈ Q', VotedForIn s a v₁ b₂ ∨ WontVoteIn s a b₂ := hsafe b₂ hlt
      rcases hsafe₂ with ⟨Q', hQ', hQ'V⟩
      have hqq : (Q₂ ∩ Q').Nonempty := hQuorums Q₂ hQ₂ Q' hQ'
      rcases hqq with ⟨a, haQ₂, haQ'⟩
      have ha₂ : VotedForIn s a v₂ b₂ := hV₂ a haQ₂
      rcases hQ'V a haQ' with hV₁same | hWont
      · exact votedOnce s hMsg a a b₂ v₁ v₂ hV₁same ha₂
      · exfalso
        exact hWont.1 v₂ ha₂
  exact consistency_of_inv s (hInv s hs)


end Paxos
