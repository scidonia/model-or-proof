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
  sorry

end Paxos
