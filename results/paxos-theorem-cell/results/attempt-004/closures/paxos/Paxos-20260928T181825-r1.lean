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
    (∀ v : V, ¬ VotedForIn s a v b) ∧ s.maxBal a > (b : ℤ)
  let SafeAt : State N V → V → ℕ → Prop := fun s v b =>
    ∀ c : ℕ, c < b → ∃ Q ∈ Quorums, ∀ a ∈ Q, VotedForIn s a v c ∨ WontVoteIn s a c
  let MsgInv1b : State N V → Prop := fun s =>
    ∀ m ∈ s.msgs, m.tag = MessageTag.oneB →
      ∃ b mb mv a, m = Message.«1b» b mb mv a ∧
        (b : ℤ) ≤ s.maxBal a ∧
        ((∃ v : V, ∃ nb : ℕ, mv = some v ∧ mb = (nb : ℤ) ∧ VotedForIn s a v nb) ∨
         (mv = none ∧ mb = -1)) ∧
        (∀ c : ℕ, (mb : ℤ) + 1 ≤ (c : ℤ) → c < b → ∀ v : V, ¬ VotedForIn s a v c)
  let MsgInv2a : State N V → Prop := fun s =>
    ∀ m ∈ s.msgs, m.tag = MessageTag.twoA →
      ∃ b v, m = Message.«2a» b v ∧ SafeAt s v b ∧
        (∀ ma ∈ s.msgs, ma.tag = MessageTag.twoA → ma.ballot = b → ma = m)
  let MsgInv2b : State N V → Prop := fun s =>
    ∀ m ∈ s.msgs, m.tag = MessageTag.twoB →
      ∃ b v a, m = Message.«2b» b v a ∧
        (∃ ma ∈ s.msgs, ma.tag = MessageTag.twoA ∧ ma.ballot = b ∧ ma.val = some v) ∧
        (b : ℤ) ≤ s.maxVBal a
  let MsgInv : State N V → Prop := fun s =>
    MsgInv1b s ∧ MsgInv2a s ∧ MsgInv2b s
  let AccInv : State N V → Prop := fun s =>
    ∀ a : Fin N,
      ((s.maxVal a = none) ↔ (s.maxVBal a = -1)) ∧
      (s.maxVBal a ≤ s.maxBal a) ∧
      (0 ≤ s.maxVBal a →
        ∃ b : ℕ, ∃ v : V, (b : ℤ) = s.maxVBal a ∧ s.maxVal a = some v ∧ VotedForIn s a v b) ∧
      (∀ c : ℕ, (c : ℤ) > s.maxVBal a → ∀ v : V, ¬ VotedForIn s a v c)
  let Inv : State N V → Prop := fun s => TypeOK s ∧ MsgInv s ∧ AccInv s
  have hVotedInv : ∀ s, MsgInv s → ∀ a v b, VotedForIn s a v b →
      SafeAt s v b ∧ (b : ℤ) ≤ s.maxVBal a := by
    intro s hMsg a v b hv
    rcases hv with ⟨m, hm, htag, hval, hb, hacc⟩
    have h2b := hMsg.2.2 m hm htag
    rcases h2b with ⟨b', v', a', hm_eq, h2a, hle⟩
    subst m
    have hv' : v' = v := Option.some.inj (by simpa [Message.val] using hval)
    have ha' : a' = a := Option.some.inj (by simpa [Message.acc] using hacc)
    have hb' : b' = b := by simpa [Message.ballot] using hb
    subst b'
    subst v'
    subst a'
    rcases h2a with ⟨ma, hma, hmaTag, hmaB, hmaV⟩
    have h2a' := hMsg.2.1 ma hma hmaTag
    rcases h2a' with ⟨b2, v2, ma_eq, hSafe, huniq⟩
    subst ma
    have hv2 : v2 = v := Option.some.inj (by simpa [Message.val] using hmaV)
    have hb2 : b2 = b := by simpa [Message.ballot] using hmaB
    subst b2
    subst v2
    exact ⟨hSafe, hle⟩
  have hVotedOnce : ∀ s, MsgInv s → ∀ a1 a2 v1 v2 b, VotedForIn s a1 v1 b → VotedForIn s a2 v2 b → v1 = v2 := by
    intro s hMsg a1 a2 v1 v2 b h1 h2
    rcases h1 with ⟨m1, hm1, ht1, hv1, hb1, ha1⟩
    have hm1b := hMsg.2.2 m1 hm1 ht1
    rcases hm1b with ⟨b1', v1', a1', me1, h2a1, hle1⟩
    subst m1
    have hv1' : v1' = v1 := Option.some.inj (by simpa [Message.val] using hv1)
    have hb1' : b1' = b := by simpa [Message.ballot] using hb1
    subst b1'
    subst v1'
    rcases h2a1 with ⟨ma1, hma1, hma1Tag, hma1B, hma1V⟩
    have hma1' := hMsg.2.1 ma1 hma1 hma1Tag
    rcases hma1' with ⟨b1'', v1'', me1', hSafe1, huniq1⟩
    subst ma1
    have hv1'' : v1'' = v1 := Option.some.inj (by simpa [Message.val] using hma1V)
    have hb1'' : b1'' = b := by simpa [Message.ballot] using hma1B
    subst b1''
    subst v1''
    rcases h2 with ⟨m2, hm2, ht2, hv2, hb2, ha2⟩
    have hm2b := hMsg.2.2 m2 hm2 ht2
    rcases hm2b with ⟨b2', v2', a2', me2, h2a2, hle2⟩
    subst m2
    have hv2' : v2' = v2 := Option.some.inj (by simpa [Message.val] using hv2)
    have hb2' : b2' = b := by simpa [Message.ballot] using hb2
    subst b2'
    subst v2'
    rcases h2a2 with ⟨ma2, hma2, hma2Tag, hma2B, hma2V⟩
    have hma2' := hMsg.2.1 ma2 hma2 hma2Tag
    rcases hma2' with ⟨b2'', v2'', me2', hSafe2, huniq2⟩
    subst ma2
    have hv2'' : v2'' = v2 := Option.some.inj (by simpa [Message.val] using hma2V)
    have hb2'' : b2'' = b := by simpa [Message.ballot] using hma2B
    subst b2''
    subst v2''
    have hma2tag2 : (Message.«2a» b v2 : Message N V).tag = MessageTag.twoA := rfl
    have hma2b2 : (Message.«2a» b v2 : Message N V).ballot = b := rfl
    have heq := huniq1 (Message.«2a» b v2) hma2 hma2tag2 hma2b2
    cases heq
    rfl
  have hSafeAtStable : ∀ s t, Inv s → Next Quorums s t → TypeOK t →
      ∀ v b, SafeAt s v b → SafeAt t v b := by
    intro s t hInv hNext hTypeT
    have hmsgsSub : s.msgs ⊆ t.msgs := by
      rcases hNext with hb | ha
      · rcases hb with ⟨b, hb⟩
        rcases hb with h1a | h2a
        · rcases h1a with ⟨hnot, hsend, hmb, hmvb, hmv⟩
          intro m hm; rw [hsend]; exact Set.mem_insert_of_mem _ hm
        · rcases h2a with ⟨hnot, hex, hmb, hmvb, hmv⟩
          rcases hex with ⟨v0, Q0, hQ0m, S0, hS0, hQ0, hcond, hsend⟩
          intro m hm; rw [hsend]; exact Set.mem_insert_of_mem _ hm
      · rcases ha with ⟨a, ha⟩
        rcases ha with h1b | h2b
        · rcases h1b with ⟨b, h1aIn, hgt, hsend, hmb, hmvb, hmv⟩
          intro m hm; rw [hsend]; exact Set.mem_insert_of_mem _ hm
        · rcases h2b with ⟨b, v0, h2aIn, hge, hsend, hmb, hmvb, hmv⟩
          intro m hm; rw [hsend]; exact Set.mem_insert_of_mem _ hm
    have hVotePersist : ∀ a v c, VotedForIn s a v c → VotedForIn t a v c := by
      intro a v c hv
      rcases hv with ⟨m, hm, htag, hval, hb', hacc⟩
      exact ⟨m, hmsgsSub hm, htag, hval, hb', hacc⟩
    have hWontPersist : ∀ x c, WontVoteIn s x c → WontVoteIn t x c := by
      rcases hNext with hb | ha
      · rcases hb with ⟨b, hb⟩
        rcases hb with h1a | h2a
        · rcases h1a with ⟨hnot, hsend, hmb, hmvb, hmv⟩
          intro x c hW
          constructor
          · intro v hv
            rcases hv with ⟨m, hmT, htag, hval, hb', hacc⟩
            rw [hsend] at hmT
            rcases Set.mem_insert_iff.mp hmT with hEq | hS
            · subst m
              simp [Message.tag] at htag
            · exact hW.1 v ⟨m, hS, htag, hval, hb', hacc⟩
          · simpa [hmb] using hW.2
        · rcases h2a with ⟨hnot, hex, hmb, hmvb, hmv⟩
          rcases hex with ⟨v0, Q0, hQ0m, S0, hS0, hQ0, hcond, hsend⟩
          intro x c hW
          constructor
          · intro v hv
            rcases hv with ⟨m, hmT, htag, hval, hb', hacc⟩
            rw [hsend] at hmT
            rcases Set.mem_insert_iff.mp hmT with hEq | hS
            · subst m
              simp [Message.tag] at htag
            · exact hW.1 v ⟨m, hS, htag, hval, hb', hacc⟩
          · simpa [hmb] using hW.2
      · rcases ha with ⟨a, ha⟩
        rcases ha with h1b | h2b
        · rcases h1b with ⟨b, h1aIn, hgt, hsend, hmb, hmvb, hmv⟩
          intro x c hW
          constructor
          · intro v hv
            rcases hv with ⟨m, hmT, htag, hval, hb', hacc⟩
            rw [hsend] at hmT
            rcases Set.mem_insert_iff.mp hmT with hEq | hS
            · subst m
              simp [Message.tag] at htag
            · exact hW.1 v ⟨m, hS, htag, hval, hb', hacc⟩
          · by_cases hx : x = a
            · subst x
              simp [hmb]
              omega
            · rw [hmb, Function.update_of_ne hx (b : ℤ) s.maxBal]
              exact hW.2
        · rcases h2b with ⟨b, v0, h2aIn, hge, hsend, hmb, hmvb, hmv⟩
          intro x c hW
          constructor
          · intro v hv
            rcases hv with ⟨m, hmT, htag, hval, hb', hacc⟩
            rw [hsend] at hmT
            rcases Set.mem_insert_iff.mp hmT with hEq | hS
            · subst m
              simp [Message.acc] at hacc
              have hx : x = a := hacc.symm
              subst x
              simp [Message.ballot] at hb'
              omega
            · exact hW.1 v ⟨m, hS, htag, hval, hb', hacc⟩
          · by_cases hx : x = a
            · subst x
              simp [hmb]
              omega
            · rw [hmb, Function.update_of_ne hx (b : ℤ) s.maxBal]
              exact hW.2
    intro v b hSafe c hc
    rcases hSafe c hc with ⟨Q, hQm, hQ⟩
    refine ⟨Q, hQm, ?_⟩
    intro a ha
    rcases hQ a ha with hV | hW
    · exact Or.inl (hVotePersist a v c hV)
    · exact Or.inr (hWontPersist a c hW)

  have hInvariant : Inv s := by
    induction hs with
    | init hInit =>
      rcases hInit with ⟨hmsgs, hmb, hmvb, hmv⟩
      constructor
      · constructor
        · intro a
          rw [hmb]
          left
          rfl
        · constructor
          · intro a
            rw [hmvb]
            left
            rfl
          · intro a
            rw [hmb, hmvb]
      · constructor
        · constructor
          · intro m hm
            exfalso
            simpa [hmsgs] using hm
          · constructor
            · intro m hm
              exfalso
              simpa [hmsgs] using hm
            · intro m hm
              exfalso
              simpa [hmsgs] using hm
        · intro a
          constructor
          · constructor <;> simp [hmv, hmvb]
          · constructor
            · simp [hmb, hmvb]
            · constructor
              · intro h
                simp [hmvb] at h
              · intro c hc v hv
                rcases hv with ⟨m, hm, htag, hval, hb', hacc⟩
                exfalso
                simpa [hmsgs] using hm
    | step =>
      rename_i sprev tprev hReach hStep ih
      rcases hStep with hNext | hEq
      · have hTypeT : TypeOK tprev := by
          rcases hNext with hb | ha
          · rcases hb with ⟨b, hb⟩
            rcases hb with h1a | h2a
            · rcases h1a with ⟨hnot, hsend, hmb, hmvb, hmv⟩
              simpa [TypeOK, hmb, hmvb] using ih.1
            · rcases h2a with ⟨hnot, hex, hmb, hmvb, hmv⟩
              simpa [TypeOK, hmb, hmvb] using ih.1
          · rcases ha with ⟨a, ha⟩
            rcases ha with h1b | h2b
            · rcases h1b with ⟨b, h1aIn, hgt, hsend, hmb, hmvb, hmv⟩
              constructor
              · intro a0
                by_cases h : a0 = a
                · subst a0
                  simp [hmb]
                  right
                  exact ⟨b, rfl⟩
                · rw [hmb, Function.update_of_ne h (b : ℤ) sprev.maxBal]
                  exact ih.1.1 a0
              · constructor
                · intro a0
                  rw [hmvb]
                  exact ih.1.2.1 a0
                · intro a0
                  by_cases h : a0 = a
                  · subst a0
                    simp [hmb, hmvb]
                    have hge : sprev.maxBal a ≥ sprev.maxVBal a := ih.1.2.2 a
                    omega
                  · rw [hmb, hmvb, Function.update_of_ne h (b : ℤ) sprev.maxBal]
                    exact ih.1.2.2 a0
            · rcases h2b with ⟨b, v0, h2aIn, hge, hsend, hmb, hmvb, hmv⟩
              constructor
              · intro a0
                by_cases h : a0 = a
                · subst a0
                  simp [hmb]
                  right
                  exact ⟨b, rfl⟩
                · rw [hmb, Function.update_of_ne h (b : ℤ) sprev.maxBal]
                  exact ih.1.1 a0
              · constructor
                · intro a0
                  by_cases h : a0 = a
                  · subst a0
                    simp [hmvb]
                    right
                    exact ⟨b, rfl⟩
                  · rw [hmvb, Function.update_of_ne h (b : ℤ) sprev.maxVBal]
                    exact ih.1.2.1 a0
                · intro a0
                  by_cases h : a0 = a
                  · subst a0
                    simp [hmb, hmvb]
                  · rw [hmb, hmvb, Function.update_of_ne h (b : ℤ) sprev.maxBal, Function.update_of_ne h (b : ℤ) sprev.maxVBal]
                    exact ih.1.2.2 a0
        have hSafeStable : ∀ v b, SafeAt sprev v b → SafeAt tprev v b :=
          hSafeAtStable sprev tprev ih hNext hTypeT
        rcases hNext with hb | ha
        · rcases hb with ⟨b, hb⟩
          rcases hb with h1a | h2a
          · -- Phase1a
            rcases h1a with ⟨hnot, hsend, hmb, hmvb, hmv⟩
            have hVotes : ∀ a v b, VotedForIn tprev a v b ↔ VotedForIn sprev a v b := by
              intro a v b
              constructor
              · intro hv
                rcases hv with ⟨m, hmT, htag, hval, hb', hacc⟩
                rw [hsend] at hmT
                rcases Set.mem_insert_iff.mp hmT with hEq | hS
                · subst m
                  simp [Message.tag] at htag
                · exact ⟨m, hS, htag, hval, hb', hacc⟩
              · intro hv
                rcases hv with ⟨m, hm, htag, hval, hb', hacc⟩
                exact ⟨m, by rw [hsend]; exact Set.mem_insert_of_mem _ hm, htag, hval, hb', hacc⟩
            have hAccT : AccInv tprev := by
              simpa [AccInv, hmb, hmvb, hmv, hVotes] using ih.2.2
            have hMsgT : MsgInv tprev := by
              constructor
              · intro m hmT htag
                rw [hsend] at hmT
                rcases Set.mem_insert_iff.mp hmT with hEq | hS
                · subst m
                  simp [Message.tag] at htag
                · rcases ih.2.1.1 m hS htag with ⟨b', mb, mv, a, hm_eq, hle, hcond, hno⟩
                  refine ⟨b', mb, mv, a, hm_eq, ?_, ?_, ?_⟩
                  · simpa [hmb] using hle
                  · rcases hcond with hV | hNone
                    · left
                      rcases hV with ⟨v, nb, hmv', hmb', hvot⟩
                      exact ⟨v, nb, hmv', hmb', (hVotes a v nb).2 hvot⟩
                    · right
                      exact hNone
                  · intro c hc1 hc2 v hvT
                    exact hno c hc1 hc2 v ((hVotes a v c).1 hvT)
              · constructor
                · intro m hmT htag
                  rw [hsend] at hmT
                  rcases Set.mem_insert_iff.mp hmT with hEq | hS
                  · subst m
                    simp [Message.tag] at htag
                  · rcases ih.2.1.2.1 m hS htag with ⟨b', v', hm_eq, hSafe, huniq⟩
                    refine ⟨b', v', hm_eq, hSafeStable v' b' hSafe, ?_⟩
                    intro ma hmaT hmaTag hmaB
                    rw [hsend] at hmaT
                    rcases Set.mem_insert_iff.mp hmaT with hmaEq | hmaS
                    · subst ma
                      simp [Message.tag] at hmaTag
                    · exact huniq ma hmaS hmaTag hmaB
                · intro m hmT htag
                  rw [hsend] at hmT
                  rcases Set.mem_insert_iff.mp hmT with hEq | hS
                  · subst m
                    simp [Message.tag] at htag
                  · rcases ih.2.1.2.2 m hS htag with ⟨b', v', a, hm_eq, h2a, hle⟩
                    refine ⟨b', v', a, hm_eq, ?_, ?_⟩
                    · rcases h2a with ⟨ma, hma, hmaTag, hmaB, hmaV⟩
                      exact ⟨ma, by rw [hsend]; exact Set.mem_insert_of_mem _ hma, hmaTag, hmaB, hmaV⟩
                    · simpa [hmvb] using hle
            exact ⟨hTypeT, hMsgT, hAccT⟩
          · -- Phase2a
            rcases h2a with ⟨hnot, hex, hmb, hmvb, hmv⟩
            rcases hex with ⟨v0, Q, hQm, S, hSsub, hScov, hcond, hsend⟩
            have hVotes : ∀ a v b, VotedForIn tprev a v b ↔ VotedForIn sprev a v b := by
              intro a v b
              constructor
              · intro hv
                rcases hv with ⟨m, hmT, htag, hval, hb', hacc⟩
                rw [hsend] at hmT
                rcases Set.mem_insert_iff.mp hmT with hEq | hS
                · subst m
                  simp [Message.tag] at htag
                · exact ⟨m, hS, htag, hval, hb', hacc⟩
              · intro hv
                rcases hv with ⟨m, hm, htag, hval, hb', hacc⟩
                exact ⟨m, by rw [hsend]; exact Set.mem_insert_of_mem _ hm, htag, hval, hb', hacc⟩
            have hSafeSprev : SafeAt sprev v0 b := by
              intro d hd
              rcases hcond with hall | hsome
              · refine ⟨Q, hQm, ?_⟩
                intro a haQ
                rcases hScov a haQ with ⟨m, hmS, hacc⟩
                have hsub : m ∈ sprev.msgs ∧ m.tag = MessageTag.oneB ∧ m.ballot = b := hSsub hmS
                have hm1b := ih.2.1.1 m hsub.1 hsub.2.1
                rcases hm1b with ⟨b0, mb, mv, a0, hm_eq, hle, hcond0, hno⟩
                have hmbneg : m.maxVBal = -1 := hall m hmS
                subst m
                have hb0 : b0 = b := by simpa [Message.ballot] using hsub.2.2
                have ha0 : a0 = a := Option.some.inj (by simpa [Message.acc] using hacc)
                subst b0
                subst a0
                right
                constructor
                · intro v hv
                  have hmbneg' : mb = -1 := by simpa [Message.maxVBal] using hmbneg
                  exact hno d (by omega) hd v hv
                · omega
              · rcases hsome with ⟨c, hc, hSle, hSm⟩
                rcases hSm with ⟨m0, hm0S, hm0eq, hm0val⟩
                have hm0sub : m0 ∈ sprev.msgs ∧ m0.tag = MessageTag.oneB ∧ m0.ballot = b := hSsub hm0S
                have hm01b := ih.2.1.1 m0 hm0sub.1 hm0sub.2.1
                rcases hm01b with ⟨b0, mb, mv, a0, hm0_eq, hle0, hcond0, hno0⟩
                subst m0
                have hb0 : b0 = b := by simpa [Message.ballot] using hm0sub.2.2
                subst b0
                have hmbc : mb = (c : ℤ) := by simpa [Message.maxVBal] using hm0eq
                have hmvv : mv = some v0 := by simpa [Message.maxVal] using hm0val
                rcases hcond0 with hleft | hright
                · rcases hleft with ⟨v', nb, hmv', hmbnb, hvot⟩
                  have hv' : v' = v0 := Option.some.inj (by simpa [hmvv] using hmv'.symm)
                  have hnb : nb = c := by omega
                  subst v'
                  subst nb
                  have hSafeC : SafeAt sprev v0 c := (hVotedInv sprev ih.2.1 a0 v0 c hvot).1
                  by_cases hdc : d < c
                  · rcases hSafeC d hdc with ⟨Q', hQ'm, hQ'⟩
                    exact ⟨Q', hQ'm, hQ'⟩
                  · by_cases hde : d = c
                    · subst d
                      refine ⟨Q, hQm, ?_⟩
                      intro a haQ
                      rcases hScov a haQ with ⟨m, hmS, hacc⟩
                      have hsub : m ∈ sprev.msgs ∧ m.tag = MessageTag.oneB ∧ m.ballot = b := hSsub hmS
                      have hm1b := ih.2.1.1 m hsub.1 hsub.2.1
                      rcases hm1b with ⟨b1, mb1, mv1, a1, hm_eq1, hle1, hcond1, hno1⟩
                      have hmSle : m.maxVBal ≤ (c : ℤ) := hSle m hmS
                      subst m
                      have hb1 : b1 = b := by simpa [Message.ballot] using hsub.2.2
                      have ha1 : a1 = a := Option.some.inj (by simpa [Message.acc] using hacc)
                      subst b1
                      subst a1
                      have hmax : sprev.maxBal a > (c : ℤ) := by omega
                      by_cases hvotc : ∃ w, VotedForIn sprev a w c
                      · rcases hvotc with ⟨w, hw⟩
                        left
                        have hwv : w = v0 := hVotedOnce sprev ih.2.1 a a0 w v0 c hw hvot
                        subst w
                        exact hw
                      · right
                        constructor
                        · intro w hw
                          exact hvotc ⟨w, hw⟩
                        · exact hmax
                    · refine ⟨Q, hQm, ?_⟩
                      intro a haQ
                      rcases hScov a haQ with ⟨m, hmS, hacc⟩
                      have hsub : m ∈ sprev.msgs ∧ m.tag = MessageTag.oneB ∧ m.ballot = b := hSsub hmS
                      have hm1b := ih.2.1.1 m hsub.1 hsub.2.1
                      rcases hm1b with ⟨b1, mb1, mv1, a1, hm_eq1, hle1, hcond1, hno1⟩
                      have hmSle : m.maxVBal ≤ (c : ℤ) := hSle m hmS
                      subst m
                      have hb1 : b1 = b := by simpa [Message.ballot] using hsub.2.2
                      have ha1 : a1 = a := Option.some.inj (by simpa [Message.acc] using hacc)
                      subst b1
                      subst a1
                      have hmb1le : mb1 ≤ (c : ℤ) := by simpa [Message.maxVBal] using hmSle
                      right
                      constructor
                      · intro w hw
                        exact hno1 d (by omega) hd w hw
                      · omega
                · exfalso
                  rcases hright with ⟨hmvnone, hmbneg⟩
                  have : some v0 = none := by simpa [hmvv] using hmvnone
                  cases this
            have hAccT : AccInv tprev := by
              simpa [AccInv, hmb, hmvb, hmv, hVotes] using ih.2.2
            have hMsgT : MsgInv tprev := by
              constructor
              · intro m hmT htag
                rw [hsend] at hmT
                rcases Set.mem_insert_iff.mp hmT with hEq | hS
                · subst m
                  simp [Message.tag] at htag
                · rcases ih.2.1.1 m hS htag with ⟨b', mb, mv, a, hm_eq, hle, hcond, hno⟩
                  refine ⟨b', mb, mv, a, hm_eq, ?_, ?_, ?_⟩
                  · simpa [hmb] using hle
                  · rcases hcond with hV | hNone
                    · left
                      rcases hV with ⟨v, nb, hmv', hmb', hvot⟩
                      exact ⟨v, nb, hmv', hmb', (hVotes a v nb).2 hvot⟩
                    · right
                      exact hNone
                  · intro c hc1 hc2 v hvT
                    exact hno c hc1 hc2 v ((hVotes a v c).1 hvT)
              · constructor
                · intro m hmT htag
                  rw [hsend] at hmT
                  rcases Set.mem_insert_iff.mp hmT with hEq | hS
                  · subst m
                    refine ⟨b, v0, rfl, ?_, ?_⟩
                    · exact hSafeStable v0 b hSafeSprev
                    · intro ma hmaT hmaTag hmaB
                      rw [hsend] at hmaT
                      rcases Set.mem_insert_iff.mp hmaT with hmaEq | hmaS
                      · subst ma
                        rfl
                      · exfalso
                        exact hnot ⟨ma, hmaS, hmaTag, hmaB⟩
                  · rcases ih.2.1.2.1 m hS htag with ⟨b', v', hm_eq, hSafe, huniq⟩
                    refine ⟨b', v', hm_eq, hSafeStable v' b' hSafe, ?_⟩
                    intro ma hmaT hmaTag hmaB
                    rw [hsend] at hmaT
                    rcases Set.mem_insert_iff.mp hmaT with hmaEq | hmaS
                    · subst ma
                      have hb'' : b = b' := by simpa [Message.ballot] using hmaB
                      exfalso
                      exact hnot ⟨m, hS, htag, by simpa [hm_eq, Message.ballot] using hb''.symm⟩
                    · exact huniq ma hmaS hmaTag hmaB
                · intro m hmT htag
                  rw [hsend] at hmT
                  rcases Set.mem_insert_iff.mp hmT with hEq | hS
                  · subst m
                    simp [Message.tag] at htag
                  · rcases ih.2.1.2.2 m hS htag with ⟨b', v', a, hm_eq, h2a, hle⟩
                    refine ⟨b', v', a, hm_eq, ?_, ?_⟩
                    · rcases h2a with ⟨ma, hma, hmaTag, hmaB, hmaV⟩
                      exact ⟨ma, by rw [hsend]; exact Set.mem_insert_of_mem _ hma, hmaTag, hmaB, hmaV⟩
                    · simpa [hmvb] using hle
            exact ⟨hTypeT, hMsgT, hAccT⟩
        · rcases ha with ⟨a, ha⟩
          rcases ha with h1b | h2b
          · -- Phase1b
            rcases h1b with ⟨b, h1aIn, hgt, hsend, hmb, hmvb, hmv⟩
            have hVotes : ∀ a v b, VotedForIn tprev a v b ↔ VotedForIn sprev a v b := by
              intro a v b
              constructor
              · intro hv
                rcases hv with ⟨m, hmT, htag, hval, hb', hacc⟩
                rw [hsend] at hmT
                rcases Set.mem_insert_iff.mp hmT with hEq | hS
                · subst m
                  simp [Message.tag] at htag
                · exact ⟨m, hS, htag, hval, hb', hacc⟩
              · intro hv
                rcases hv with ⟨m, hm, htag, hval, hb', hacc⟩
                exact ⟨m, by rw [hsend]; exact Set.mem_insert_of_mem _ hm, htag, hval, hb', hacc⟩
            have hmaxGe : ∀ a0, sprev.maxBal a0 ≤ tprev.maxBal a0 := by
              intro a0
              by_cases h : a0 = a
              · subst a0
                simp [hmb]
                omega
              · rw [hmb, Function.update_of_ne h (b : ℤ) sprev.maxBal]
            have hAccT : AccInv tprev := by
              intro a0
              constructor
              · rw [hmv, hmvb]
                exact (ih.2.2 a0).1
              · constructor
                · by_cases h : a0 = a
                  · subst a0
                    simp [hmb, hmvb]
                    have hge : sprev.maxBal a ≥ sprev.maxVBal a := ih.1.2.2 a
                    omega
                  · rw [hmb, hmvb, Function.update_of_ne h (b : ℤ) sprev.maxBal]
                    exact (ih.2.2 a0).2.1
                · constructor
                  · intro h0
                    have h0' : 0 ≤ sprev.maxVBal a0 := by simpa [hmvb] using h0
                    rcases (ih.2.2 a0).2.2.1 h0' with ⟨b0, v, hb0, hmv0, hvot⟩
                    exact ⟨b0, v, by simpa [hmvb] using hb0, by simpa [hmv] using hmv0, (hVotes a0 v b0).2 hvot⟩
                  · intro c hc v hvT
                    have hc' : (c : ℤ) > sprev.maxVBal a0 := by simpa [hmvb] using hc
                    have hvS : VotedForIn sprev a0 v c := (hVotes a0 v c).1 hvT
                    exact (ih.2.2 a0).2.2.2 c hc' v hvS
            have hMsgT : MsgInv tprev := by
              constructor
              · intro m hmT htag
                rw [hsend] at hmT
                rcases Set.mem_insert_iff.mp hmT with hEq | hS
                · subst m
                  refine ⟨b, sprev.maxVBal a, sprev.maxVal a, a, rfl, ?_, ?_, ?_⟩
                  · simp [hmb]
                  · have hacc := ih.2.2 a
                    by_cases h0 : 0 ≤ sprev.maxVBal a
                    · left
                      rcases hacc.2.2.1 h0 with ⟨b0, v, hb0, hmv0, hvot⟩
                      exact ⟨v, b0, hmv0, hb0.symm, (hVotes a v b0).2 hvot⟩
                    · right
                      have hneg : sprev.maxVBal a = -1 := by
                        rcases ih.1.2.1 a with hneg' | hpos
                        · exact hneg'
                        · rcases hpos with ⟨b0, hb0⟩
                          exfalso
                          apply h0
                          omega
                      constructor
                      · exact (hacc.1).2 hneg
                      · exact hneg
                  · intro c hc1 hc2 v hvT
                    have hvS : VotedForIn sprev a v c := (hVotes a v c).1 hvT
                    exact (ih.2.2 a).2.2.2 c (by omega) v hvS
                · rcases ih.2.1.1 m hS htag with ⟨b', mb, mv, a0, hm_eq, hle, hcond, hno⟩
                  refine ⟨b', mb, mv, a0, hm_eq, ?_, ?_, ?_⟩
                  · exact le_trans hle (hmaxGe a0)
                  · rcases hcond with hV | hNone
                    · left
                      rcases hV with ⟨v, nb, hmv', hmb', hvot⟩
                      exact ⟨v, nb, hmv', hmb', (hVotes a0 v nb).2 hvot⟩
                    · right
                      exact hNone
                  · intro c hc1 hc2 v hvT
                    exact hno c hc1 hc2 v ((hVotes a0 v c).1 hvT)
              · constructor
                · intro m hmT htag
                  rw [hsend] at hmT
                  rcases Set.mem_insert_iff.mp hmT with hEq | hS
                  · subst m
                    simp [Message.tag] at htag
                  · rcases ih.2.1.2.1 m hS htag with ⟨b', v', hm_eq, hSafe, huniq⟩
                    refine ⟨b', v', hm_eq, hSafeStable v' b' hSafe, ?_⟩
                    intro ma hmaT hmaTag hmaB
                    rw [hsend] at hmaT
                    rcases Set.mem_insert_iff.mp hmaT with hmaEq | hmaS
                    · subst ma
                      simp [Message.tag] at hmaTag
                    · exact huniq ma hmaS hmaTag hmaB
                · intro m hmT htag
                  rw [hsend] at hmT
                  rcases Set.mem_insert_iff.mp hmT with hEq | hS
                  · subst m
                    simp [Message.tag] at htag
                  · rcases ih.2.1.2.2 m hS htag with ⟨b', v', a0, hm_eq, h2a, hle⟩
                    refine ⟨b', v', a0, hm_eq, ?_, ?_⟩
                    · rcases h2a with ⟨ma, hma, hmaTag, hmaB, hmaV⟩
                      exact ⟨ma, by rw [hsend]; exact Set.mem_insert_of_mem _ hma, hmaTag, hmaB, hmaV⟩
                    · simpa [hmvb] using hle
            exact ⟨hTypeT, hMsgT, hAccT⟩
          · -- Phase2b
            rcases h2b with ⟨b, v0, h2aIn, hge, hsend, hmb, hmvb, hmv⟩
            have hVoteMonotone : ∀ a v c, VotedForIn sprev a v c → VotedForIn tprev a v c := by
              intro a v c hv
              rcases hv with ⟨m, hm, htag, hval, hb', hacc⟩
              exact ⟨m, by rw [hsend]; exact Set.mem_insert_of_mem _ hm, htag, hval, hb', hacc⟩
            have hVotesOther : ∀ a0, a0 ≠ a → ∀ v c, VotedForIn tprev a0 v c ↔ VotedForIn sprev a0 v c := by
              intro a0 ha0 v c
              constructor
              · intro hv
                rcases hv with ⟨m, hmT, htag, hval, hb', hacc⟩
                rw [hsend] at hmT
                rcases Set.mem_insert_iff.mp hmT with hEq | hS
                · subst m
                  simp [Message.acc] at hacc
                  have : a = a0 := hacc
                  exact (ha0 this.symm).elim
                · exact ⟨m, hS, htag, hval, hb', hacc⟩
              · intro hv
                rcases hv with ⟨m, hm, htag, hval, hb', hacc⟩
                exact ⟨m, by rw [hsend]; exact Set.mem_insert_of_mem _ hm, htag, hval, hb', hacc⟩
            have hNoNewVote1b : ∀ (a0 : Fin N) (b0 : ℕ) (v : V) (c : ℕ), (b0 : ℤ) ≤ sprev.maxBal a0 → c < b0 →
                VotedForIn tprev a0 v c → VotedForIn sprev a0 v c := by
              intro a0 b0 v c hle0 hcb hv
              rcases hv with ⟨m, hmT, htag, hval, hb', hacc⟩
              rw [hsend] at hmT
              rcases Set.mem_insert_iff.mp hmT with hEq | hS
              · subst m
                simp [Message.ballot] at hb'
                have ha0 : a = a0 := Option.some.inj (by simpa [Message.acc] using hacc)
                subst a0
                omega
              · exact ⟨m, hS, htag, hval, hb', hacc⟩
            have hmaxGe : ∀ a0, sprev.maxBal a0 ≤ tprev.maxBal a0 := by
              intro a0
              by_cases h : a0 = a
              · subst a0
                simp [hmb]
                omega
              · rw [hmb, Function.update_of_ne h (b : ℤ) sprev.maxBal]
            have hmaxVGe : ∀ a0, sprev.maxVBal a0 ≤ tprev.maxVBal a0 := by
              intro a0
              by_cases h : a0 = a
              · subst a0
                simp [hmvb]
                have hge' : sprev.maxBal a ≥ sprev.maxVBal a := ih.1.2.2 a
                omega
              · rw [hmvb, Function.update_of_ne h (b : ℤ) sprev.maxVBal]
            have hAccT : AccInv tprev := by
              intro a0
              by_cases h : a0 = a
              · subst a0
                constructor
                · constructor
                  · intro h'; simp [hmv] at h'
                  · intro h'; simp [hmvb] at h'
                · constructor
                  · simp [hmb, hmvb]
                  · constructor
                    · intro h0
                      exact ⟨b, v0, by simp [hmvb], by simp [hmv], ⟨Message.«2b» b v0 a, by rw [hsend]; simp, rfl, rfl, rfl, rfl⟩⟩
                    · intro c hc v hvT
                      rcases hvT with ⟨m, hmT, htag, hval, hb', hacc⟩
                      rw [hsend] at hmT
                      rcases Set.mem_insert_iff.mp hmT with hEq | hS
                      · subst m
                        simp [Message.ballot] at hb'
                        simp [hmvb] at hc
                        omega
                      · simp [hmvb] at hc
                        have hge' : sprev.maxBal a ≥ sprev.maxVBal a := ih.1.2.2 a
                        exact (ih.2.2 a).2.2.2 c (by omega) v ⟨m, hS, htag, hval, hb', hacc⟩
              · have hne : a0 ≠ a := h
                constructor
                · rw [hmv, hmvb, Function.update_of_ne hne (some v0) sprev.maxVal, Function.update_of_ne hne (b : ℤ) sprev.maxVBal]
                  exact (ih.2.2 a0).1
                · constructor
                  · rw [hmb, hmvb, Function.update_of_ne hne (b : ℤ) sprev.maxBal, Function.update_of_ne hne (b : ℤ) sprev.maxVBal]
                    exact (ih.2.2 a0).2.1
                  · constructor
                    · intro h0
                      have h0' : 0 ≤ sprev.maxVBal a0 := by simpa [hmvb, Function.update_of_ne hne (b : ℤ) sprev.maxVBal] using h0
                      rcases (ih.2.2 a0).2.2.1 h0' with ⟨b0, v, hb0, hmv0, hvot⟩
                      exact ⟨b0, v, by simpa [hmvb, Function.update_of_ne hne (b : ℤ) sprev.maxVBal] using hb0, by simpa [hmv, Function.update_of_ne hne (some v0) sprev.maxVal] using hmv0, (hVotesOther a0 hne v b0).2 hvot⟩
                    · intro c hc v hvT
                      have hc' : (c : ℤ) > sprev.maxVBal a0 := by simpa [hmvb, Function.update_of_ne hne (b : ℤ) sprev.maxVBal] using hc
                      have hvS : VotedForIn sprev a0 v c := (hVotesOther a0 hne v c).1 hvT
                      exact (ih.2.2 a0).2.2.2 c hc' v hvS
            have hMsgT : MsgInv tprev := by
              constructor
              · intro m hmT htag
                rw [hsend] at hmT
                rcases Set.mem_insert_iff.mp hmT with hEq | hS
                · subst m
                  simp [Message.tag] at htag
                · rcases ih.2.1.1 m hS htag with ⟨b', mb, mv, a0, hm_eq, hle, hcond, hno⟩
                  refine ⟨b', mb, mv, a0, hm_eq, ?_, ?_, ?_⟩
                  · exact le_trans hle (hmaxGe a0)
                  · rcases hcond with hV | hNone
                    · left
                      rcases hV with ⟨v, nb, hmv', hmb', hvot⟩
                      exact ⟨v, nb, hmv', hmb', hVoteMonotone a0 v nb hvot⟩
                    · right
                      exact hNone
                  · intro c hc1 hc2 v hvT
                    exact hno c hc1 hc2 v (hNoNewVote1b a0 b' v c hle hc2 hvT)
              · constructor
                · intro m hmT htag
                  rw [hsend] at hmT
                  rcases Set.mem_insert_iff.mp hmT with hEq | hS
                  · subst m
                    simp [Message.tag] at htag
                  · rcases ih.2.1.2.1 m hS htag with ⟨b', v', hm_eq, hSafe, huniq⟩
                    refine ⟨b', v', hm_eq, hSafeStable v' b' hSafe, ?_⟩
                    intro ma hmaT hmaTag hmaB
                    rw [hsend] at hmaT
                    rcases Set.mem_insert_iff.mp hmaT with hmaEq | hmaS
                    · subst ma
                      simp [Message.tag] at hmaTag
                    · exact huniq ma hmaS hmaTag hmaB
                · intro m hmT htag
                  rw [hsend] at hmT
                  rcases Set.mem_insert_iff.mp hmT with hEq | hS
                  · subst m
                    refine ⟨b, v0, a, rfl, ?_, ?_⟩
                    · exact ⟨Message.«2a» b v0, by rw [hsend]; exact Set.mem_insert_of_mem _ h2aIn, rfl, rfl, rfl⟩
                    · simp [hmvb]
                  · rcases ih.2.1.2.2 m hS htag with ⟨b', v', a0, hm_eq, h2a, hle⟩
                    refine ⟨b', v', a0, hm_eq, ?_, ?_⟩
                    · rcases h2a with ⟨ma, hma, hmaTag, hmaB, hmaV⟩
                      exact ⟨ma, by rw [hsend]; exact Set.mem_insert_of_mem _ hma, hmaTag, hmaB, hmaV⟩
                    · exact le_trans hle (hmaxVGe a0)
            exact ⟨hTypeT, hMsgT, hAccT⟩
      · subst tprev
        exact ih

  have hConsistency : Consistency Quorums s := by
    intro v1 v2 hc1 hc2
    rcases hc1 with ⟨b1, hb1⟩
    rcases hc2 with ⟨b2, hb2⟩
    have hChosenEq : ∀ {va vb : V} {ba bb : ℕ}, ba < bb →
        ChosenIn Quorums s va ba → ChosenIn Quorums s vb bb → va = vb := by
      intro va vb ba bb hlt hA hB
      rcases hA with ⟨QA, hQAm, hQA⟩
      rcases hB with ⟨QB, hQBm, hQB⟩
      rcases (hQuorums QB hQBm QB hQBm) with ⟨a0, ha0, _⟩
      have hvb : VotedForIn s a0 vb bb := hQB a0 ha0
      have hSafe : SafeAt s vb bb := (hVotedInv s hInvariant.2.1 a0 vb bb hvb).1
      rcases hSafe ba hlt with ⟨Q0, hQ0m, hQ0⟩
      rcases (hQuorums Q0 hQ0m QA hQAm) with ⟨a, ha0', haA⟩
      have ha0'' := hQ0 a ha0'
      have haA' := hQA a haA
      rcases ha0'' with hVb | hWont
      · exact (hVotedOnce s hInvariant.2.1 a a vb va ba hVb haA').symm
      · exact False.elim (hWont.1 va haA')
    by_cases hle : b1 ≤ b2
    · rcases lt_or_eq_of_le hle with hlt | heq
      · exact hChosenEq hlt hb1 hb2
      · have hb2' : b2 = b1 := heq.symm
        subst b2
        rcases hb1 with ⟨Q1, hQ1m, hQ1⟩
        rcases hb2 with ⟨Q2, hQ2m, hQ2⟩
        rcases (hQuorums Q1 hQ1m Q2 hQ2m) with ⟨a, ha1, ha2⟩
        exact hVotedOnce s hInvariant.2.1 a a v1 v2 b1 (hQ1 a ha1) (hQ2 a ha2)
    · have hlt' : b2 < b1 := lt_of_not_ge hle
      exact (hChosenEq hlt' hb2 hb1).symm
  exact hConsistency


end Paxos
