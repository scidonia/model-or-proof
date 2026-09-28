/-
Paxos agreement, negative control: the one `Phase2a` quorum-membership guard is weakened.

This is `Paxos.lean`'s model with the single change `specs/tla/paxos/PaxosFiniteMutant.tla` makes to
`specs/tla/paxos/PaxosFinite.tla`: in `Phase2a`, the guard `\E Q \in Quorums :` becomes
`\E Q \in (SUBSET Acceptors) \ {{}} :` — a *nonempty* subset authorises a proposal, not necessarily a
quorum. Everything else is unchanged: `ChosenIn` still requires a quorum, so choosing a value still
needs a full majority, but a `2a` no longer does, and two majorities can be led to choose different
values. `QuorumAssumption` is kept, `Phase2b`'s guard is still `b ≥ maxBal[a]`, the response subset `S`
is still an arbitrary subset of the `1b` messages, and `chosen` is still derived rather than stored.

Because the proposal step no longer consults `Quorums`, `Next`/`Step`/`Reachable` here take no quorum
family; `ChosenIn`/`Chosen`/`Consistency` do, so `agreement` has the same shape as the positive model's
statement — the same conclusion over the same `Quorums`, with a strictly larger reachable set. The
statement is false; a run that closes this file means the rig is broken rather than that something hard
was proved (protocol §5, plan D7).

The `sorry` is a seed's placeholder like any other: the run is expected to *fail* to close it, and that
failure is the cell's acceptance.
-/
import Mathlib

namespace PaxosMutant

/-! ## Messages -/

/-- The four message type tags of the reference. -/
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

/-- TLA+ `Messages`, unchanged from `Paxos.lean`. -/
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

/-- TLA+ `m.type`. -/
def tag : Message N V → MessageTag
  | «1a» _ => .oneA
  | «1b» _ _ _ _ => .oneB
  | «2a» _ _ => .twoA
  | «2b» _ _ _ => .twoB

/-- TLA+ `m.bal`. -/
def ballot : Message N V → ℕ
  | «1a» b => b
  | «1b» b _ _ _ => b
  | «2a» b _ => b
  | «2b» b _ _ => b

/-- TLA+ `m.maxVBal`, carried by `1b` messages. -/
def maxVBal : Message N V → ℤ
  | «1b» _ mb _ _ => mb
  | _ => -1

/-- TLA+ `m.maxVal`, carried by `1b` messages. -/
def maxVal : Message N V → Option V
  | «1b» _ _ mv _ => mv
  | _ => none

/-- TLA+ `m.val`, carried by `2a`/`2b` messages. -/
def val : Message N V → Option V
  | «2a» _ v => some v
  | «2b» _ v _ => some v
  | _ => none

/-- TLA+ `m.acc`, carried by `1b`/`2b` messages. -/
def acc : Message N V → Option (Fin N)
  | «1b» _ _ _ a => some a
  | «2b» _ _ a => some a
  | _ => none

end Message

/-! ## The state -/

/-- TLA+ `VARIABLES msgs, maxBal, maxVBal, maxVal`, unchanged from `Paxos.lean`. -/
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

/-- TLA+ `ASSUME QuorumAssumption`, unchanged: it is kept even though `Phase2a` no longer consults
`Quorums`, because `ChosenIn` still does. -/
def QuorumAssumption (Quorums : Set (Set (Fin N))) : Prop :=
  ∀ Q₁ ∈ Quorums, ∀ Q₂ ∈ Quorums, (Q₁ ∩ Q₂).Nonempty

/-- TLA+ `Send(m)`, unchanged. -/
def Send (m : Message N V) (s t : State N V) : Prop :=
  t.msgs = insert m s.msgs

/-- TLA+ `Init`, unchanged. -/
def Init (s : State N V) : Prop :=
  s.msgs = ∅ ∧
    s.maxBal = (fun _ => -1) ∧
    s.maxVBal = (fun _ => -1) ∧
    s.maxVal = (fun _ => none)

/-- TLA+ `Phase1a(b)`, unchanged. -/
def Phase1a (b : ℕ) (s t : State N V) : Prop :=
  (¬ ∃ m ∈ s.msgs, m.tag = MessageTag.oneA ∧ m.ballot = b) ∧
    Send (Message.«1a» b) s t ∧
    t.maxBal = s.maxBal ∧ t.maxVBal = s.maxVBal ∧ t.maxVal = s.maxVal

/-- TLA+ `Phase1b(a)`, unchanged. -/
def Phase1b (a : Fin N) (s t : State N V) : Prop :=
  ∃ b : ℕ, Message.«1a» b ∈ s.msgs ∧ (b : ℤ) > s.maxBal a ∧
    Send (Message.«1b» b (s.maxVBal a) (s.maxVal a) a) s t ∧
    t.maxBal = Function.update s.maxBal a (b : ℤ) ∧
    t.maxVBal = s.maxVBal ∧ t.maxVal = s.maxVal

/-- TLA+ `Phase2a(b)`, **mutated**: the guard `\E Q \in Quorums :` is replaced by
`\E Q \in (SUBSET Acceptors) \ {{}} :`, i.e. a nonempty subset of acceptors rather than a quorum. Every
other conjunct — the no-earlier-`2a` guard, the response subset `S` with one response per member of `Q`,
the highest-ballot value rule, and the `Send` — is the positive model's. -/
def Phase2a (b : ℕ) (s t : State N V) : Prop :=
  (¬ ∃ m ∈ s.msgs, m.tag = MessageTag.twoA ∧ m.ballot = b) ∧
    (∃ v : V, ∃ Q : Set (Fin N), Q.Nonempty ∧ ∃ S : Set (Message N V),
      S ⊆ {m : Message N V | m ∈ s.msgs ∧ m.tag = MessageTag.oneB ∧ m.ballot = b} ∧
        (∀ a ∈ Q, ∃ m ∈ S, m.acc = some a) ∧
        ((∀ m ∈ S, m.maxVBal = -1) ∨
          (∃ c : ℕ, c < b ∧ (∀ m ∈ S, m.maxVBal ≤ (c : ℤ)) ∧
            ∃ m ∈ S, m.maxVBal = (c : ℤ) ∧ m.maxVal = some v)) ∧
        Send (Message.«2a» b v) s t) ∧
    t.maxBal = s.maxBal ∧ t.maxVBal = s.maxVBal ∧ t.maxVal = s.maxVal

/-- TLA+ `Phase2b(a)`, unchanged: the guard remains `b ≥ maxBal[a]`. -/
def Phase2b (a : Fin N) (s t : State N V) : Prop :=
  ∃ b : ℕ, ∃ v : V, Message.«2a» b v ∈ s.msgs ∧ (b : ℤ) ≥ s.maxBal a ∧
    Send (Message.«2b» b v a) s t ∧
    t.maxBal = Function.update s.maxBal a (b : ℤ) ∧
    t.maxVBal = Function.update s.maxVBal a (b : ℤ) ∧
    t.maxVal = Function.update s.maxVal a (some v)

/-- TLA+ `Next`, with the mutated `Phase2a`. Since the proposal step no longer consults `Quorums`, this
relation takes no quorum family. -/
def Next (s t : State N V) : Prop :=
  (∃ b : ℕ, Phase1a b s t ∨ Phase2a b s t) ∨
    ∃ a : Fin N, Phase1b a s t ∨ Phase2b a s t

/-- TLA+ `[Next]_vars`. -/
def Step (s t : State N V) : Prop :=
  Next s t ∨ t = s

/-- The states admitted by `Init /\ [][Next]_vars`, over the mutated transition relation. -/
inductive Reachable : State N V → Prop where
  /-- The initial states. -/
  | init {s} : Init s → Reachable s
  /-- The states one `[Next]_vars` step away from a reachable state. -/
  | step {s t} : Reachable s → Step s t → Reachable t

/-! ## `Chosen` and `Consistency` -/

/-- TLA+ `VotedForIn(a, v, b)`, unchanged. -/
def VotedForIn (s : State N V) (a : Fin N) (v : V) (b : ℕ) : Prop :=
  ∃ m ∈ s.msgs, m.tag = MessageTag.twoB ∧ m.val = some v ∧ m.ballot = b ∧ m.acc = some a

/-- TLA+ `ChosenIn(v, b)`, **unchanged**: choosing still requires a quorum. -/
def ChosenIn (Quorums : Set (Set (Fin N))) (s : State N V) (v : V) (b : ℕ) : Prop :=
  ∃ Q ∈ Quorums, ∀ a ∈ Q, VotedForIn s a v b

/-- TLA+ `Chosen(v)`, unchanged. -/
def Chosen (Quorums : Set (Set (Fin N))) (s : State N V) (v : V) : Prop :=
  ∃ b : ℕ, ChosenIn Quorums s v b

/-- TLA+ `Consistency`, unchanged. False on the mutated reachable set, which is the point. -/
def Consistency (Quorums : Set (Set (Fin N))) (s : State N V) : Prop :=
  ∀ v₁ v₂ : V, Chosen Quorums s v₁ → Chosen Quorums s v₂ → v₁ = v₂

/-! ## The (false) theorem -/

/-- **Agreement**, with the same statement shape as `Paxos.agreement` — the same conclusion over the same
`Quorums` — and false here, because the weakened `Phase2a` guard lets a non-quorum authorise a proposal.
A run that closes this has been fooled. -/
theorem agreement (Quorums : Set (Set (Fin N))) (hQuorums : QuorumAssumption Quorums)
    (s : State N V) (hs : Reachable s) : Consistency Quorums s := by
  sorry

end PaxosMutant
