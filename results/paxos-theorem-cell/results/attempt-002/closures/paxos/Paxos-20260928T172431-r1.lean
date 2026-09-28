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
  let WontVoteIn : State N V → Fin N → ℕ → Prop := fun s a b =>
    (∀ v : V, ¬ VotedForIn s a v b) ∧ (s.maxBal a > (b : ℤ))
  let SafeAt : State N V → V → ℕ → Prop := fun s v b =>
    ∀ c : ℕ, c < b → ∃ Q ∈ Quorums, ∀ a ∈ Q, VotedForIn s a v c ∨ WontVoteIn s a c
  let OneBInv : State N V → Prop := fun s =>
    ∀ m ∈ s.msgs, m.tag = MessageTag.oneB → ∀ a : Fin N, m.acc = some a →
      (m.ballot : ℤ) ≤ s.maxBal a ∧
      ((∃ v : V, ∃ b0 : ℕ, m.maxVal = some v ∧ m.maxVBal = (b0 : ℤ) ∧ VotedForIn s a v b0)
        ∨ (m.maxVal = none ∧ m.maxVBal = -1)) ∧
      (∀ c : ℕ, m.maxVBal < (c : ℤ) → c < m.ballot → ∀ v : V, ¬ VotedForIn s a v c)
  let TwoAInv : State N V → Prop := fun s =>
    ∀ m ∈ s.msgs, m.tag = MessageTag.twoA → ∀ v : V, m.val = some v →
      SafeAt s v m.ballot ∧
      (∀ m2 ∈ s.msgs, m2.tag = MessageTag.twoA → m2.ballot = m.ballot → m2 = m)
  let TwoBInv : State N V → Prop := fun s =>
    ∀ m ∈ s.msgs, m.tag = MessageTag.twoB → ∀ a : Fin N, ∀ v : V,
      m.acc = some a → m.val = some v →
      ∃ ma ∈ s.msgs, ma.tag = MessageTag.twoA ∧ ma.ballot = m.ballot ∧ ma.val = some v
  let AccInv : State N V → Prop := fun s =>
    ∀ a : Fin N,
      (s.maxVal a = none ↔ s.maxVBal a = -1) ∧
      s.maxVBal a ≤ s.maxBal a ∧
      (0 ≤ s.maxVBal a →
         ∃ v : V, ∃ b0 : ℕ, s.maxVal a = some v ∧ s.maxVBal a = (b0 : ℤ) ∧ VotedForIn s a v b0) ∧
      (∀ c : ℕ, (c : ℤ) > s.maxVBal a → ∀ v : V, ¬ VotedForIn s a v c)
  let Inv : State N V → Prop := fun s => TypeOK s ∧ OneBInv s ∧ TwoAInv s ∧ TwoBInv s ∧ AccInv s
  have hVotedMono : ∀ {s t : State N V}, Next Quorums s t → ∀ {a : Fin N} {v : V} {b : ℕ},
      VotedForIn s a v b → VotedForIn t a v b := by
    intro s t hNext a v b hv
    rcases hv with ⟨m, hm, htag, hval, hb, hacc⟩
    rcases hNext with (⟨b0, h1a | h2a⟩ | ⟨a0, h1b | h2b⟩)
    · rcases h1a with ⟨hno, hsend, hmb, hmvb, hmv⟩
      simp [Send] at hsend
      exact ⟨m, by rw [hsend]; exact Or.inr hm, htag, hval, hb, hacc⟩
    · rcases h2a with ⟨hno, hcore, hmb, hmvb, hmv⟩
      rcases hcore with ⟨v0, Q, hQ, S, hsub, haccQ, hchoose, hsend⟩
      simp [Send] at hsend
      exact ⟨m, by rw [hsend]; exact Or.inr hm, htag, hval, hb, hacc⟩
    · rcases h1b with ⟨b0, h1aIn, hgt, hsend, hmb, hmvb, hmv⟩
      simp [Send] at hsend
      exact ⟨m, by rw [hsend]; exact Or.inr hm, htag, hval, hb, hacc⟩
    · rcases h2b with ⟨b0, v0, h2aIn, hge, hsend, hmb, hmvb, hmv⟩
      simp [Send] at hsend
      exact ⟨m, by rw [hsend]; exact Or.inr hm, htag, hval, hb, hacc⟩
  have hVotedEq : ∀ {s t : State N V} {m0 : Message N V},
      t.msgs = insert m0 s.msgs → m0.tag ≠ MessageTag.twoB →
      ∀ {a : Fin N} {v : V} {b : ℕ}, VotedForIn t a v b ↔ VotedForIn s a v b := by
    intro s t m0 hmsgs hnot a v b
    constructor
    · intro hv
      rcases hv with ⟨m, hm, htag, hval, hb, hacc⟩
      rw [hmsgs] at hm
      rcases hm with hmnew | hmold
      · subst m
        exact (hnot htag).elim
      · exact ⟨m, hmold, htag, hval, hb, hacc⟩
    · intro hv
      rcases hv with ⟨m, hm, htag, hval, hb, hacc⟩
      exact ⟨m, by rw [hmsgs]; exact Or.inr hm, htag, hval, hb, hacc⟩
  have hVotedEqNe : ∀ {s t : State N V} {b : ℕ} {v : V} {a : Fin N},
      t.msgs = insert (@Message.«2b» N V b v a) s.msgs →
      ∀ {a' : Fin N} {v' : V} {c : ℕ}, c ≠ b → (VotedForIn t a' v' c ↔ VotedForIn s a' v' c) := by
    rintro s t b v a hmsgs a' v' c hc
    constructor
    · intro hv
      rcases hv with ⟨m, hm, htag, hval, hb', hacc⟩
      rw [hmsgs] at hm
      rcases hm with hmnew | hmold
      · subst m
        simp [Message.tag, Message.val, Message.ballot, Message.acc] at htag hval hb' hacc
        omega
      · exact ⟨m, hmold, htag, hval, hb', hacc⟩
    · intro hv
      rcases hv with ⟨m, hm, htag, hval, hb', hacc⟩
      exact ⟨m, by rw [hmsgs]; exact Or.inr hm, htag, hval, hb', hacc⟩
  have hVotedEqAccNot : ∀ {s t : State N V} {b : ℕ} {v : V} {a : Fin N},
      t.msgs = insert (@Message.«2b» N V b v a) s.msgs →
      ∀ {a' : Fin N}, a' ≠ a → ∀ {v' : V} {c : ℕ}, (VotedForIn t a' v' c ↔ VotedForIn s a' v' c) := by
    rintro s t b v a hmsgs a' haa' v' c
    constructor
    · intro hv
      rcases hv with ⟨m, hm, htag, hval, hb', hacc⟩
      rw [hmsgs] at hm
      rcases hm with hmnew | hmold
      · subst m
        simp [Message.tag, Message.val, Message.ballot, Message.acc] at htag hval hb' hacc
        have : a = a' := by simpa using hacc
        exact (haa' this.symm).elim
      · exact ⟨m, hmold, htag, hval, hb', hacc⟩
    · intro hv
      rcases hv with ⟨m, hm, htag, hval, hb', hacc⟩
      exact ⟨m, by rw [hmsgs]; exact Or.inr hm, htag, hval, hb', hacc⟩
  have hWontMono : ∀ {s t : State N V}, Next Quorums s t → ∀ {a : Fin N} {b : ℕ},
      WontVoteIn s a b → WontVoteIn t a b := by
    intro s t hNext a b hw
    rcases hw with ⟨hnovote, hmax⟩
    rcases hNext with (⟨b0, h1a | h2a⟩ | ⟨a0, h1b | h2b⟩)
    · rcases h1a with ⟨hno, hsend, hmb, hmvb, hmv⟩
      simp [Send] at hsend
      constructor
      · intro v hv
        rcases hv with ⟨m, hm, htag, hval, hb', hacc⟩
        rw [hsend] at hm
        rcases hm with hmnew | hmold
        · subst m
          simp [Message.tag] at htag
        · exact hnovote v ⟨m, hmold, htag, hval, hb', hacc⟩
      · rw [hmb]
        exact hmax
    · rcases h2a with ⟨hno, hcore, hmb, hmvb, hmv⟩
      rcases hcore with ⟨v0, Q, hQ, S, hsub, haccQ, hchoose, hsend⟩
      simp [Send] at hsend
      constructor
      · intro v hv
        rcases hv with ⟨m, hm, htag, hval, hb', hacc⟩
        rw [hsend] at hm
        rcases hm with hmnew | hmold
        · subst m
          simp [Message.tag] at htag
        · exact hnovote v ⟨m, hmold, htag, hval, hb', hacc⟩
      · rw [hmb]
        exact hmax
    · rcases h1b with ⟨b1, h1aIn, hgt, hsend, hmb, hmvb, hmv⟩
      simp [Send] at hsend
      constructor
      · intro v hv
        rcases hv with ⟨m, hm, htag, hval, hb', hacc⟩
        rw [hsend] at hm
        rcases hm with hmnew | hmold
        · subst m
          simp [Message.tag] at htag
        · exact hnovote v ⟨m, hmold, htag, hval, hb', hacc⟩
      · by_cases haa : a = a0
        · subst a0
          rw [hmb]
          simp
          omega
        · rw [hmb]
          simp [haa]
          exact hmax
    · rcases h2b with ⟨b1, v0, h2aIn, hge, hsend, hmb, hmvb, hmv⟩
      simp [Send] at hsend
      constructor
      · intro v hv
        rcases hv with ⟨m, hm, htag, hval, hb', hacc⟩
        rw [hsend] at hm
        rcases hm with hmnew | hmold
        · subst m
          simp [Message.tag, Message.val, Message.ballot, Message.acc] at htag hval hb' hacc
          have hbb : b1 = b := by omega
          have haa : a0 = a := by simpa using hacc
          subst b1
          subst a0
          omega
        · exact hnovote v ⟨m, hmold, htag, hval, hb', hacc⟩
      · by_cases haa : a = a0
        · subst a0
          rw [hmb]
          simp
          omega
        · rw [hmb]
          simp [haa]
          exact hmax
  have hSafeAtStable : ∀ {s t : State N V}, Next Quorums s t → ∀ {v : V} {b : ℕ},
      SafeAt s v b → SafeAt t v b := by
    intro s t hNext v b hs
    dsimp [SafeAt] at hs ⊢
    intro c hc
    rcases hs c hc with ⟨Q, hQ, hq⟩
    refine ⟨Q, hQ, ?_⟩
    intro a ha
    rcases hq a ha with hv | hw
    · exact Or.inl (hVotedMono hNext hv)
    · exact Or.inr (hWontMono hNext hw)
  have hSafeAtOfVote : ∀ s : State N V, Inv s → ∀ a : Fin N, ∀ v : V, ∀ b : ℕ,
      VotedForIn s a v b → SafeAt s v b := by
    intro s hInv a v b hv
    rcases hInv with ⟨hTO, hOB, hTA, hTB, hAcc⟩
    rcases hv with ⟨m, hm, htag, hval, hb, hacc⟩
    rcases hTB m hm htag a v hacc hval with ⟨ma, hma, htagma, hbma, hvalma⟩
    have hbb : ma.ballot = b := by simpa [hb] using hbma
    have hsafe : SafeAt s v ma.ballot := (hTA ma hma htagma v hvalma).1
    simpa [hbb] using hsafe
  have hVotedOnce : ∀ s : State N V, Inv s → ∀ a1 a2 : Fin N, ∀ b : ℕ, ∀ v1 v2 : V,
      VotedForIn s a1 v1 b → VotedForIn s a2 v2 b → v1 = v2 := by
    intro s hInv a1 a2 b v1 v2 hv1 hv2
    rcases hInv with ⟨hTO, hOB, hTA, hTB, hAcc⟩
    rcases hv1 with ⟨m1, hm1, ht1, hval1, hb1, hacc1⟩
    rcases hv2 with ⟨m2, hm2, ht2, hval2, hb2, hacc2⟩
    rcases hTB m1 hm1 ht1 a1 v1 hacc1 hval1 with ⟨ma1, hma1, hta1, hbma1, hvalma1⟩
    rcases hTB m2 hm2 ht2 a2 v2 hacc2 hval2 with ⟨ma2, hma2, hta2, hbma2, hvalma2⟩
    have hb1' : ma1.ballot = b := by simpa [hb1] using hbma1
    have hb2' : ma2.ballot = b := by simpa [hb2] using hbma2
    have hball : ma1.ballot = ma2.ballot := by rw [hb1', hb2']
    have hma : ma1 = ma2 := ((hTA ma1 hma1 hta1 v1 hvalma1).2 ma2 hma2 hta2 hball.symm).symm
    subst ma1
    have hsome : some v1 = some v2 := by rw [←hvalma1]; exact hvalma2
    exact Option.some.inj hsome

  have mkInv : ∀ (s : State N V), TypeOK s → OneBInv s → TwoAInv s → TwoBInv s → AccInv s → Inv s := by
    intro s h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  have hOneAPres : ∀ (b : ℕ) (s t : State N V), Inv s → Phase1a b s t → Inv t := by
    intro b s t hInv h1a
    rcases hInv with ⟨hTO, hOB, hTA, hTB, hAcc⟩
    rcases h1a with ⟨hno, hsend, hmb, hmvb, hmv⟩
    simp [Send] at hsend
    have hnot : (@Message.«1a» N V b).tag ≠ MessageTag.twoB := by simp [Message.tag]
    have hVE : ∀ {a : Fin N} {v : V} {b : ℕ}, VotedForIn t a v b ↔ VotedForIn s a v b :=
      hVotedEq hsend hnot
    refine mkInv _ ?_ ?_ ?_ ?_ ?_
    · simpa [TypeOK, hmb, hmvb, hmv] using hTO
    · intro m hm htag a hacc
      rw [hsend] at hm
      rcases hm with hmnew | hmold
      · subst m
        simp [Message.tag] at htag
      · rw [hmb]
        have h := hOB m hmold htag a hacc
        constructor
        · exact h.1
        · constructor
          · rcases h.2.1 with hv | hn
            · left
              rcases hv with ⟨v0, b0, hmv, hvb, hvote⟩
              refine ⟨v0, b0, hmv, hvb, ?_⟩
              exact (hVE (a := a) (v := v0) (b := b0)).2 hvote
            · right
              exact hn
          · intro c hc hcb v hv
            apply h.2.2 c hc hcb v
            exact (hVE (a := a) (v := v) (b := c)).1 hv
    · intro m hm htag v hval
      rw [hsend] at hm
      rcases hm with hmnew | hmold
      · subst m
        simp [Message.tag] at htag
      · have h := hTA m hmold htag v hval
        constructor
        · exact hSafeAtStable (Or.inl ⟨b, Or.inl ⟨hno, hsend, hmb, hmvb, hmv⟩⟩) h.1
        · intro m2 hm2 htag2 hb2
          rw [hsend] at hm2
          rcases hm2 with hm2new | hm2old
          · subst m2
            simp [Message.tag] at htag2
          · exact h.2 m2 hm2old htag2 hb2
    · intro m hm htag a v hacc hval
      rw [hsend] at hm
      rcases hm with hmnew | hmold
      · subst m
        simp [Message.tag] at htag
      · rcases hTB m hmold htag a v hacc hval with ⟨ma, hma, htagma, hbma, hvalma⟩
        exact ⟨ma, by rw [hsend]; exact Or.inr hma, htagma, hbma, hvalma⟩
    · intro a
      have h := hAcc a
      rw [hmb, hmvb, hmv]
      constructor
      · exact h.1
      · constructor
        · exact h.2.1
        · constructor
          · intro hpos
            rcases h.2.2.1 hpos with ⟨v, b0, hval, hvb, hvote⟩
            refine ⟨v, b0, hval, hvb, ?_⟩
            exact (hVE (a := a) (v := v) (b := b0)).2 hvote
          · intro c hc v hv
            apply h.2.2.2 c hc v
            exact (hVE (a := a) (v := v) (b := c)).1 hv

  have hTwoAPres : ∀ (b : ℕ) (s t : State N V), Inv s → Phase2a Quorums b s t → Inv t := by
    intro b s t hInv h2a
    rcases hInv with ⟨hTO, hOB, hTA, hTB, hAcc⟩
    have hInvS : Inv s := ⟨hTO, hOB, hTA, hTB, hAcc⟩
    rcases h2a with ⟨hno2a, hcore, hmb, hmvb, hmv⟩
    rcases hcore with ⟨v, Q, hQ, S, hsub, haccQ, hchoose, hsend⟩
    have h2a' : Phase2a Quorums b s t := ⟨hno2a, ⟨v, Q, hQ, S, hsub, haccQ, hchoose, hsend⟩, hmb, hmvb, hmv⟩
    simp [Send] at hsend
    have hnot : (@Message.«2a» N V b v).tag ≠ MessageTag.twoB := by simp [Message.tag]
    have hVE : ∀ {a : Fin N} {v : V} {b : ℕ}, VotedForIn t a v b ↔ VotedForIn s a v b :=
      hVotedEq hsend hnot
    have hsafe : SafeAt s v b := by
      dsimp [SafeAt]
      intro c hc
      rcases hchoose with hnone | hsome
      · refine ⟨Q, hQ, ?_⟩
        intro a haQ
        rcases haccQ a haQ with ⟨m, hmS, haccm⟩
        have hsubm := hsub hmS
        simp at hsubm
        have hm1b : m.tag = MessageTag.oneB ∧ m.ballot = b ∧ m ∈ s.msgs := by
          rcases hsubm with ⟨⟨hmin, hmtag⟩, hmin', hmb⟩
          exact ⟨hmtag, hmb, hmin⟩
        have hmob := hOB m hm1b.2.2 hm1b.1 a haccm
        right
        constructor
        · intro v0 hv0
          have hmvneg : m.maxVBal = -1 := hnone m hmS
          exact hmob.2.2 c (by rw [hmvneg]; omega) (by rw [hm1b.2.1]; exact hc) v0 hv0
        · have hle : (m.ballot : ℤ) ≤ s.maxBal a := hmob.1
          rw [hm1b.2.1] at hle
          omega
      · rcases hsome with ⟨c0, hc0, hleS, ma, hmaS, hmaeq, hmav⟩
        have hsubma := hsub hmaS
        simp at hsubma
        have hma1b : ma.tag = MessageTag.oneB ∧ ma.ballot = b ∧ ma ∈ s.msgs := by
          rcases hsubma with ⟨⟨hmain, hmatag⟩, hmain', hmab⟩
          exact ⟨hmatag, hmab, hmain⟩
        have hacc_ma_exists : ∃ am : Fin N, ma.acc = some am := by
          rcases ma with _ | ⟨bma, mvbma, mvma, am⟩ | _ | _
          · simp [Message.tag] at hma1b
          · exact ⟨am, rfl⟩
          · simp [Message.tag] at hma1b
          · simp [Message.tag] at hma1b
        rcases hacc_ma_exists with ⟨am, hacc_ma⟩
        have hmobma := hOB ma hma1b.2.2 hma1b.1 am hacc_ma
        have hreported : VotedForIn s am v c0 := by
          rcases hmobma.2.1 with hrep | hnone'
          · rcases hrep with ⟨v0, b0, hvma, hvb, hvote⟩
            have hb0 : b0 = c0 := by
              have hb0z : (b0 : ℤ) = (c0 : ℤ) := by rw [←hvb, hmaeq]
              omega
            have hv0 : v0 = v := by
              have hsome : some v0 = some v := by rw [←hvma, hmav]
              exact Option.some.inj hsome
            subst b0
            subst v0
            exact hvote
          · rcases hnone' with ⟨hnone_val, hnone_vb⟩
            omega
        have hsafe_c0 : SafeAt s v c0 := hSafeAtOfVote s hInvS am v c0 hreported
        rcases lt_trichotomy c c0 with hlt | heq | hgt
        · exact hsafe_c0 c hlt
        · subst c0
          refine ⟨Q, hQ, ?_⟩
          intro a haQ
          rcases haccQ a haQ with ⟨m, hmS, haccm⟩
          have hsubm := hsub hmS
          simp at hsubm
          have hm1b : m.tag = MessageTag.oneB ∧ m.ballot = b ∧ m ∈ s.msgs := by
            rcases hsubm with ⟨⟨hmin, hmtag⟩, hmin', hmb⟩
            exact ⟨hmtag, hmb, hmin⟩
          have hmob := hOB m hm1b.2.2 hm1b.1 a haccm
          by_cases hV : VotedForIn s a v c
          · left
            exact hV
          · right
            constructor
            · intro v0 hv0
              have hvv : v0 = v := hVotedOnce s hInvS a am c v0 v hv0 hreported
              subst v0
              exact hV hv0
            · have hle : (m.ballot : ℤ) ≤ s.maxBal a := hmob.1
              rw [hm1b.2.1] at hle
              omega
        · refine ⟨Q, hQ, ?_⟩
          intro a haQ
          rcases haccQ a haQ with ⟨m, hmS, haccm⟩
          have hsubm := hsub hmS
          simp at hsubm
          have hm1b : m.tag = MessageTag.oneB ∧ m.ballot = b ∧ m ∈ s.msgs := by
            rcases hsubm with ⟨⟨hmin, hmtag⟩, hmin', hmb⟩
            exact ⟨hmtag, hmb, hmin⟩
          have hmob := hOB m hm1b.2.2 hm1b.1 a haccm
          right
          constructor
          · intro v0 hv0
            exact hmob.2.2 c (by have hle_m := hleS m hmS; omega) (by rw [hm1b.2.1]; exact hc) v0 hv0
          · have hle : (m.ballot : ℤ) ≤ s.maxBal a := hmob.1
            rw [hm1b.2.1] at hle
            omega
    refine mkInv _ ?_ ?_ ?_ ?_ ?_
    · simpa [TypeOK, hmb, hmvb, hmv] using hTO
    · intro m hm htag a hacc
      rw [hsend] at hm
      rcases hm with hmnew | hmold
      · subst m
        simp [Message.tag] at htag
      · rw [hmb]
        have h := hOB m hmold htag a hacc
        constructor
        · exact h.1
        · constructor
          · rcases h.2.1 with hv | hn
            · left
              rcases hv with ⟨v0, b0, hmv, hvb, hvote⟩
              refine ⟨v0, b0, hmv, hvb, ?_⟩
              exact (hVE (a := a) (v := v0) (b := b0)).2 hvote
            · right
              exact hn
          · intro c hc hcb v0 hv0
            apply h.2.2 c hc hcb v0
            exact (hVE (a := a) (v := v0) (b := c)).1 hv0
    · intro m hm htag v0 hval
      rw [hsend] at hm
      rcases hm with hmnew | hmold
      · subst m
        -- m is the new 2a message; need SafeAt and uniqueness
        have hv_eq : v0 = v := by
          simp [Message.val] at hval
          exact hval.symm
        subst v0
        constructor
        · simpa [Message.ballot] using (hSafeAtStable (Or.inl ⟨b, Or.inr h2a'⟩) hsafe)
        · intro m2 hm2 htag2 hb2
          rw [hsend] at hm2
          rcases hm2 with hm2new | hm2old
          · subst m2
            rfl
          · exfalso
            exact hno2a ⟨m2, hm2old, htag2, by simpa [Message.ballot] using hb2⟩
      · have h := hTA m hmold htag v0 hval
        constructor
        · exact hSafeAtStable (Or.inl ⟨b, Or.inr h2a'⟩) h.1
        · intro m2 hm2 htag2 hb2
          rw [hsend] at hm2
          rcases hm2 with hm2new | hm2old
          · subst m2
            exfalso
            exact hno2a ⟨m, hmold, htag, hb2.symm⟩
          · exact h.2 m2 hm2old htag2 hb2
    · intro m hm htag a v0 hacc hval
      rw [hsend] at hm
      rcases hm with hmnew | hmold
      · subst m
        simp [Message.tag] at htag
      · rcases hTB m hmold htag a v0 hacc hval with ⟨ma, hma, htagma, hbma, hvalma⟩
        exact ⟨ma, by rw [hsend]; exact Or.inr hma, htagma, hbma, hvalma⟩
    · intro a
      have h := hAcc a
      rw [hmb, hmvb, hmv]
      constructor
      · exact h.1
      · constructor
        · exact h.2.1
        · constructor
          · intro hpos
            rcases h.2.2.1 hpos with ⟨v0, b0, hval, hvb, hvote⟩
            refine ⟨v0, b0, hval, hvb, ?_⟩
            exact (hVE (a := a) (v := v0) (b := b0)).2 hvote
          · intro c hc v0 hv0
            apply h.2.2.2 c hc v0
            exact (hVE (a := a) (v := v0) (b := c)).1 hv0

  have hOneBPres : ∀ (a : Fin N) (s t : State N V), Inv s → Phase1b a s t → Inv t := by
    intro a s t hInv h1b
    rcases hInv with ⟨hTO, hOB, hTA, hTB, hAcc⟩
    have hInvS : Inv s := ⟨hTO, hOB, hTA, hTB, hAcc⟩
    rcases h1b with ⟨b, h1aIn, hgt, hsend, hmb, hmvb, hmv⟩
    have h1b' : Phase1b a s t := ⟨b, h1aIn, hgt, hsend, hmb, hmvb, hmv⟩
    simp [Send] at hsend
    have hnot : (@Message.«1b» N V b (s.maxVBal a) (s.maxVal a) a).tag ≠ MessageTag.twoB := by
      simp [Message.tag]
    have hVE : ∀ {a : Fin N} {v : V} {b : ℕ}, VotedForIn t a v b ↔ VotedForIn s a v b :=
      hVotedEq hsend hnot
    refine mkInv _ ?_ ?_ ?_ ?_ ?_
    · constructor
      · intro a'
        rw [hmb]
        by_cases haa' : a' = a
        · subst a'
          simp [IsBallot]
        · simp [Function.update, haa', IsBallot]
          exact hTO.1 a'
      · constructor
        · intro a'
          rw [hmvb]
          exact hTO.2.1 a'
        · intro a'
          rw [hmb, hmvb]
          by_cases haa' : a' = a
          · subst a'
            have hlemax : s.maxVBal a ≤ s.maxBal a := hTO.2.2 a
            simp
            omega
          · simp [Function.update, haa']
            exact hTO.2.2 a'
    · intro m hm htag a' hacc'
      rw [hsend] at hm
      rcases hm with hmnew | hmold
      · subst m
        have ha' : a' = a := Option.some.inj hacc'.symm
        subst a'
        constructor
        · rw [hmb]
          simp [Message.ballot]
        · constructor
          · have haccA := hAcc a
            by_cases hnone : s.maxVBal a = -1
            · right
              constructor
              · exact (haccA.1).2 hnone
              · exact hnone
            · left
              have hpos : 0 ≤ s.maxVBal a := by
                have hb := hTO.2.1 a
                rcases hb with hneg | ⟨b0, hb0⟩
                · exact False.elim (hnone hneg)
                · rw [hb0]
                  omega
              rcases haccA.2.2.1 hpos with ⟨v0, b0, hval, hvb, hvote⟩
              refine ⟨v0, b0, hval, hvb, ?_⟩
              exact (hVE (a := a) (v := v0) (b := b0)).2 hvote
          · intro c hc hcb v0 hv0
            apply (hAcc a).2.2.2 c hc v0
            exact (hVE (a := a) (v := v0) (b := c)).1 hv0
      · have h := hOB m hmold htag a' hacc'
        constructor
        · rw [hmb]
          by_cases haa' : a' = a
          · subst a'
            simp
            omega
          · simp [Function.update, haa']
            exact h.1
        · constructor
          · rcases h.2.1 with hv | hn
            · left
              rcases hv with ⟨v0, b0, hmv, hvb, hvote⟩
              refine ⟨v0, b0, hmv, hvb, ?_⟩
              exact (hVE (a := a') (v := v0) (b := b0)).2 hvote
            · right
              exact hn
          · intro c hc hcb v0 hv0
            apply h.2.2 c hc hcb v0
            exact (hVE (a := a') (v := v0) (b := c)).1 hv0
    · intro m hm htag v hval
      rw [hsend] at hm
      rcases hm with hmnew | hmold
      · subst m
        simp [Message.tag] at htag
      · have h := hTA m hmold htag v hval
        constructor
        · exact hSafeAtStable (Or.inr ⟨a, Or.inl h1b'⟩) h.1
        · intro m2 hm2 htag2 hb2
          rw [hsend] at hm2
          rcases hm2 with hm2new | hm2old
          · subst m2
            simp [Message.tag] at htag2
          · exact h.2 m2 hm2old htag2 hb2
    · intro m hm htag a' v hacc' hval
      rw [hsend] at hm
      rcases hm with hmnew | hmold
      · subst m
        simp [Message.tag] at htag
      · rcases hTB m hmold htag a' v hacc' hval with ⟨ma, hma, htagma, hbma, hvalma⟩
        exact ⟨ma, by rw [hsend]; exact Or.inr hma, htagma, hbma, hvalma⟩
    · intro a'
      rw [hmvb, hmv]
      constructor
      · exact (hAcc a').1
      · constructor
        · rw [hmb]
          by_cases haa' : a' = a
          · subst a'
            have hlemax : s.maxVBal a ≤ s.maxBal a := (hAcc a).2.1
            simp
            omega
          · simp [Function.update, haa']
            exact (hAcc a').2.1
        · constructor
          · intro hpos
            rcases (hAcc a').2.2.1 hpos with ⟨v0, b0, hval, hvb, hvote⟩
            refine ⟨v0, b0, hval, hvb, ?_⟩
            exact (hVE (a := a') (v := v0) (b := b0)).2 hvote
          · intro c hc v0 hv0
            apply (hAcc a').2.2.2 c hc v0
            exact (hVE (a := a') (v := v0) (b := c)).1 hv0

  have hTwoBPres : ∀ (a : Fin N) (s t : State N V), Inv s → Phase2b a s t → Inv t := by
    intro a s t hInv h2b
    rcases hInv with ⟨hTO, hOB, hTA, hTB, hAcc⟩
    have hInvS : Inv s := ⟨hTO, hOB, hTA, hTB, hAcc⟩
    rcases h2b with ⟨b, v, h2aIn, hge, hsend, hmb, hmvb, hmv⟩
    have h2b' : Phase2b a s t := ⟨b, v, h2aIn, hge, hsend, hmb, hmvb, hmv⟩
    simp [Send] at hsend
    have hVEn : ∀ {a' : Fin N} {v' : V} {c : ℕ}, c ≠ b → (VotedForIn t a' v' c ↔ VotedForIn s a' v' c) := by
      intro a' v' c hc
      exact hVotedEqNe (s := s) (t := t) (b := b) (v := v) (a := a) hsend hc
    have hVEacc : ∀ {a' : Fin N}, a' ≠ a → ∀ {v' : V} {c : ℕ}, VotedForIn t a' v' c ↔ VotedForIn s a' v' c := by
      intro a' haa' v' c
      exact hVotedEqAccNot (s := s) (t := t) (b := b) (v := v) (a := a) hsend haa' (v' := v') (c := c)
    have hnewVote : VotedForIn t a v b := by
      refine ⟨@Message.«2b» N V b v a, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsend]
        exact Or.inl rfl
      · simp [Message.tag]
      · simp [Message.val]
      · simp [Message.ballot]
      · simp [Message.acc]
    refine mkInv _ ?_ ?_ ?_ ?_ ?_
    · constructor
      · intro a'
        rw [hmb]
        by_cases haa' : a' = a
        · subst a'
          simp [IsBallot]
        · simp [Function.update, haa', IsBallot]
          exact hTO.1 a'
      · constructor
        · intro a'
          rw [hmvb]
          by_cases haa' : a' = a
          · subst a'
            simp [IsBallot]
          · simp [Function.update, haa', IsBallot]
            exact hTO.2.1 a'
        · intro a'
          rw [hmb, hmvb]
          by_cases haa' : a' = a
          · subst a'
            simp
          · simp [Function.update, haa']
            exact hTO.2.2 a'
    · intro m hm htag a' hacc'
      rw [hsend] at hm
      rcases hm with hmnew | hmold
      · subst m
        simp [Message.tag] at htag
      · have h := hOB m hmold htag a' hacc'
        constructor
        · rw [hmb]
          by_cases haa' : a' = a
          · subst a'
            simp
            omega
          · simp [Function.update, haa']
            exact h.1
        · constructor
          · rcases h.2.1 with hv | hn
            · left
              rcases hv with ⟨v0, b0, hmv, hvb, hvote⟩
              refine ⟨v0, b0, hmv, hvb, ?_⟩
              exact hVotedMono (Or.inr ⟨a, Or.inr h2b'⟩) hvote
            · right
              exact hn
          · intro c hc hcb v0 hv0
            rcases hv0 with ⟨m0, hm0, htag0, hval0, hb0, hacc0⟩
            rw [hsend] at hm0
            rcases hm0 with hm0new | hm0old
            · subst m0
              simp [Message.tag, Message.val, Message.ballot, Message.acc] at htag0 hval0 hb0 hacc0
              have ha_eq : a' = a := by simpa using hacc0.symm
              subst a'
              have hb_eq : b = c := by simpa using hb0
              omega
            · exact h.2.2 c hc hcb v0 ⟨m0, hm0old, htag0, hval0, hb0, hacc0⟩
    · intro m hm htag v0 hval
      rw [hsend] at hm
      rcases hm with hmnew | hmold
      · subst m
        simp [Message.tag] at htag
      · have h := hTA m hmold htag v0 hval
        constructor
        · exact hSafeAtStable (Or.inr ⟨a, Or.inr h2b'⟩) h.1
        · intro m2 hm2 htag2 hb2
          rw [hsend] at hm2
          rcases hm2 with hm2new | hm2old
          · subst m2
            simp [Message.tag] at htag2
          · exact h.2 m2 hm2old htag2 hb2
    · intro m hm htag a' v0 hacc' hval
      rw [hsend] at hm
      rcases hm with hmnew | hmold
      · subst m
        have hv_eq : v0 = v := by
          simp [Message.val] at hval
          exact hval.symm
        subst v0
        exact ⟨@Message.«2a» N V b v, by rw [hsend]; exact Or.inr h2aIn, by simp [Message.tag], by simp [Message.ballot], by simp [Message.val]⟩
      · rcases hTB m hmold htag a' v0 hacc' hval with ⟨ma, hma, htagma, hbma, hvalma⟩
        exact ⟨ma, by rw [hsend]; exact Or.inr hma, htagma, hbma, hvalma⟩
    · intro a'
      constructor
      · rw [hmv, hmvb]
        by_cases haa' : a' = a
        · subst a'
          constructor
          · intro hnone
            simp at hnone
          · intro hneg
            simp at hneg
        · simp [Function.update, haa']
          exact (hAcc a').1
      · constructor
        · rw [hmvb, hmb]
          by_cases haa' : a' = a
          · subst a'
            simp
          · simp [Function.update, haa']
            exact (hAcc a').2.1
        · constructor
          · intro hpos
            by_cases haa' : a' = a
            · subst a'
              refine ⟨v, b, ?_, ?_, ?_⟩
              · rw [hmv]
                simp
              · rw [hmvb]
                simp
              · simpa using hnewVote
            · have hpos' : 0 ≤ s.maxVBal a' := by
                rw [hmvb] at hpos
                simpa [Function.update, haa'] using hpos
              rcases (hAcc a').2.2.1 hpos' with ⟨v0, b0, hval, hvb, hvote⟩
              refine ⟨v0, b0, ?_, ?_, ?_⟩
              · rw [hmv]
                simp [Function.update, haa', hval]
              · rw [hmvb]
                simp [Function.update, haa', hvb]
              · exact hVotedMono (Or.inr ⟨a, Or.inr h2b'⟩) hvote
          · intro c hc v0 hv0
            by_cases haa' : a' = a
            · subst a'
              have hc' : (c : ℤ) > (b : ℤ) := by
                rw [hmvb] at hc
                simpa using hc
              have hcne : c ≠ b := by omega
              have hc_s : (c : ℤ) > s.maxVBal a := by
                have hle1 : s.maxVBal a ≤ s.maxBal a := (hAcc a).2.1
                have hle2 : (b : ℤ) ≥ s.maxBal a := hge
                linarith
              exact (hAcc a).2.2.2 c hc_s v0 ((hVEn (a' := a) (v' := v0) (c := c) hcne).1 hv0)
            · have hc' : (c : ℤ) > s.maxVBal a' := by
                rw [hmvb] at hc
                simpa [Function.update, haa'] using hc
              apply (hAcc a').2.2.2 c hc' v0
              exact (hVEacc (a' := a') haa' (v' := v0) (c := c)).1 hv0

  have hInv : ∀ s : State N V, Reachable Quorums s → Inv s := by
    intro s hs
    induction hs with
    | init h =>
        rcases h with ⟨hmsgs, hmb, hmvb, hmv⟩
        simp [Inv, TypeOK, OneBInv, TwoAInv, TwoBInv, AccInv, VotedForIn, IsBallot, hmsgs, hmb, hmvb, hmv]
    | step =>
        rename_i s_old t_new hReach hStep ih
        rcases hStep with hNext | rfl
        · rcases hNext with (⟨b, h1a | h2a⟩ | ⟨a, h1b | h2b⟩)
          · exact hOneAPres b s_old t_new ih h1a
          · exact hTwoAPres b s_old t_new ih h2a
          · exact hOneBPres a s_old t_new ih h1b
          · exact hTwoBPres a s_old t_new ih h2b
        · exact ih
  have hInvS : Inv s := hInv s hs
  intro v1 v2 hv1 hv2
  rcases hv1 with ⟨b1, Q1, hQ1, hV1⟩
  rcases hv2 with ⟨b2, Q2, hQ2, hV2⟩
  by_cases hle : b1 ≤ b2
  · by_cases hbe : b1 = b2
    · subst b1
      have hInter : (Q1 ∩ Q2).Nonempty := hQuorums Q1 hQ1 Q2 hQ2
      rcases hInter with ⟨a, ha1, ha2⟩
      exact hVotedOnce s hInvS a a b2 v1 v2 (hV1 a ha1) (hV2 a ha2)
    · have hlt : b1 < b2 := lt_of_le_of_ne hle hbe
      have hQ2ne : Q2.Nonempty := by simpa using hQuorums Q2 hQ2 Q2 hQ2
      rcases hQ2ne with ⟨a2, ha2⟩
      have hsafe2 : SafeAt s v2 b2 := hSafeAtOfVote s hInvS a2 v2 b2 (hV2 a2 ha2)
      rcases hsafe2 b1 hlt with ⟨Q, hQ, hq⟩
      have hInter : (Q1 ∩ Q).Nonempty := hQuorums Q1 hQ1 Q hQ
      rcases hInter with ⟨a, ha1, haQ⟩
      rcases hq a haQ with hv2a | hw
      · exact hVotedOnce s hInvS a a b1 v1 v2 (hV1 a ha1) hv2a
      · exact (hw.1 v1 (hV1 a ha1)).elim
  · have hlt : b2 < b1 := by omega
    have hQ1ne : Q1.Nonempty := by simpa using hQuorums Q1 hQ1 Q1 hQ1
    rcases hQ1ne with ⟨a1, ha1⟩
    have hsafe1 : SafeAt s v1 b1 := hSafeAtOfVote s hInvS a1 v1 b1 (hV1 a1 ha1)
    rcases hsafe1 b2 hlt with ⟨Q, hQ, hq⟩
    have hInter : (Q2 ∩ Q).Nonempty := hQuorums Q2 hQ2 Q hQ
    rcases hInter with ⟨a, ha2, haQ⟩
    rcases hq a haQ with hv1a | hw
    · exact (hVotedOnce s hInvS a a b2 v2 v1 (hV2 a ha2) hv1a).symm
    · exact (hw.1 v2 (hV2 a ha2)).elim

end Paxos
