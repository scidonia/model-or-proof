/-
EWD998 (Safra's termination detection) — the Lean model for Route B (protocol §2).

This is the idiomatic counterpart of `specs/tla/ewd998/EWD998.tla`, imported at pinned provenance with its
TLAPS proofs (`specs/tla/ewd998/`, and the publication-era revision in `specs/tla/ewd998-paper/`). It is
the **ring layer only**, which is the plan's ruling: the asynchronous termination-detection layer enters
the module solely at `TD == INSTANCE AsyncTerminationDetection`, a parse-time dependency referenced only by
`TDSpec`/`Refinement`, so the port is the five state variables and the five actions of the ring. The
statement-by-statement correspondence is audited in `docs/equivalence-ewd998.md` (protocol §4.1); the model
neither strengthens an assumption nor weakens the goal.

What this file states, and what it does not:

* The seed's theorem is the ring's **invariance** — `THEOREM Invariance == Init /\ [][Next]_vars => []Inv`
  (`EWD998_proof.tla:176`) — with no fairness. The module's `Spec` carries `WF_vars(System)` for the
  liveness theorem, which is a different claim and is not ported here.
* The seed states `Inv` and nothing else, as the plan rules. `TypeOK` is a proof-level strengthening the
  TLAPS proof inlines in its step case; it is carried here by the *types* of `State`, so it is a fact about
  the representation rather than a conjunct of the statement.
* `Termination` and `TerminationDetection` (the module's "main safety property") are *different*
  properties — grouped with the refinement theorem rather than with invariance — and are not stated here.

This file is the closure loop's **tier-2 seed** (plan D5): the theorem statement is the human's, the proof
is the loop's, and the `sorry` below is the seed's placeholder, not a result — the run is closed only when
the harness has observed it gone (protocol §8). The negative control will be `EWD998Mutant.lean`.
-/
import Mathlib

namespace EWD998

open scoped BigOperators

/-! ## The state -/

/-- The nodes — TLA+ `Node == 0 .. N-1`. `Fin N` is the same nodes in the same order. -/
abbrev Node (N : ℕ) := Fin N

/-- TLA+ `Color == {"white", "black"}`. -/
inductive Color where
  | white
  | black
  deriving DecidableEq

/-- TLA+ `Token == [pos : Node, q : Int, color : Color]`. -/
structure Token (N : ℕ) where
  /-- The node the token is at. -/
  pos : Node N
  /-- The count the token carries. -/
  q : ℤ
  /-- The token's colour. -/
  color : Color

/-- TLA+ `VARIABLES active, color, counter, pending, token`. TLA+'s `TypeOK` is carried by this type: the
two per-node predicates are `Bool`-valued, `pending` is a natural, `counter` an integer and the token a
structure of the right shapes, so no value of `State N` can violate it. -/
structure State (N : ℕ) where
  /-- Activation status of the nodes. -/
  active : Node N → Bool
  /-- Colour of the nodes. -/
  color : Node N → Color
  /-- Messages sent minus messages received, per node. TLA+ `counter \in [Node -> Int]`. -/
  counter : Node N → ℤ
  /-- Messages in transit to each node. TLA+ `pending \in [Node -> Nat]`. -/
  pending : Node N → ℕ
  /-- The token. -/
  token : Token N

variable {N : ℕ}

/-- The module's node `N-1`, the token's starting position: the predecessor of the ring's first node. A
node exists, so `N-1` is one (`hN` is the module's `ASSUME N \in Nat \ {0}`). -/
def lastNode (hN : 0 < N) : Node N := ⟨N - 1, by omega⟩

/-- The predecessor of a node, the position `PassToken` moves the token to. -/
def prevNode {N : ℕ} (i : Node N) : Node N := ⟨i.val - 1, by have := i.isLt; omega⟩


/-! ## The model -/

/-- TLA+ `Init`: every colour and activation status is arbitrary (`\in` is an unconstrained choice in the
module, so the Lean model constrains nothing there), both counters start empty, and the token starts at
node 0 with count 0 and colour black. `hN` is the module's `ASSUME N \in Nat \ {0}`, needed only because
the node `0` has to exist for the statement to be about anything. -/
def Init (hN : 0 < N) (s : State N) : Prop :=
  s.counter = (fun _ => 0) ∧
    s.pending = (fun _ => 0) ∧
    s.token.pos = ⟨0, hN⟩ ∧
    s.token.q = 0 ∧
    s.token.color = Color.black

/-- TLA+ `InitiateProbe` (Rules 1 + 5 + 6): with the token at node 0 and the previous round inconclusive,
the token restarts at node `N-1`, white and zeroed, and node 0 whitens. -/
def InitiateProbe (hN : 0 < N) (s t : State N) : Prop :=
  s.token.pos = ⟨0, hN⟩ ∧
    (s.token.color = Color.black ∨ s.color ⟨0, hN⟩ = Color.black ∨ s.counter ⟨0, hN⟩ + s.token.q > 0) ∧
    t.token = ⟨lastNode hN, 0, Color.white⟩ ∧
    t.color = Function.update s.color ⟨0, hN⟩ Color.white ∧
    s.active = t.active ∧
    s.counter = t.counter ∧
    s.pending = t.pending

/-- TLA+ `PassToken(i)` (Rules 2 + 4 + 7): a passive node holding the token passes it on, adding its own
count and blackening the token if it is black, and whitens itself. -/
def PassToken (i : Node N) (s t : State N) : Prop :=
  s.active i = false ∧
    s.token.pos = i ∧
    t.token = ⟨prevNode i, s.token.q + s.counter i,
                if s.color i = Color.black then Color.black else s.token.color⟩ ∧
    t.color = Function.update s.color i Color.white ∧
    s.active = t.active ∧
    s.counter = t.counter ∧
    s.pending = t.pending

/-- TLA+ `SendMsg(i)`: an active node sends one message to any other node, raising its own count and the
receiver's pending count. -/
def SendMsg (i : Node N) (s t : State N) : Prop :=
  s.active i = true ∧
    (∃ j : Node N, j ≠ i) ∧
    t.counter = Function.update s.counter i (s.counter i + 1) ∧
    t.pending = Function.update s.pending i (s.pending i + 1) ∧
    s.active = t.active ∧
    s.color = t.color ∧
    s.token = t.token

/-- TLA+ `RecvMsg(i)`: a node with a message in transit receives it — pending down, count down (Rule 0),
blackened (Rule 3) and activated. -/
def RecvMsg (i : Node N) (s t : State N) : Prop :=
  s.pending i > 0 ∧
    t.pending = Function.update s.pending i (s.pending i - 1) ∧
    t.counter = Function.update s.counter i (s.counter i - 1) ∧
    t.color = Function.update s.color i Color.black ∧
    t.active = Function.update s.active i true ∧
    s.token = t.token

/-- TLA+ `Deactivate(i)`: an active node becomes passive, changing nothing else. -/
def Deactivate (i : Node N) (s t : State N) : Prop :=
  s.active i = true ∧
    t.active = Function.update s.active i false ∧
    s.color = t.color ∧
    s.counter = t.counter ∧
    s.pending = t.pending ∧
    s.token = t.token

/-- TLA+ `System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)`. -/
def System (hN : 0 < N) (s t : State N) : Prop :=
  InitiateProbe hN s t ∨ ∃ i : Node N, i ≠ ⟨0, hN⟩ ∧ PassToken i s t

/-- TLA+ `Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)`. -/
def Environment (s t : State N) : Prop :=
  ∃ i : Node N, SendMsg i s t ∨ RecvMsg i s t ∨ Deactivate i s t

/-- TLA+ `Next == System \/ Environment`. -/
def Next (hN : 0 < N) (s t : State N) : Prop := System hN s t ∨ Environment s t

/-- TLA+ `[Next]_vars`. -/
def Step (hN : 0 < N) (s t : State N) : Prop := Next hN s t ∨ t = s

/-- The states admitted by TLA+ `Init /\ [][Next]_vars`, read as a state predicate — the invariance
reading, which is what `Invariance` proves and what the seed states. `Spec` additionally asserts
`WF_vars(System)`, which is the liveness hypothesis and is deliberately not carried here. -/
inductive Reachable (hN : 0 < N) : State N → Prop where
  /-- The initial states. -/
  | init {s} : Init hN s → Reachable hN s
  /-- The states one `[Next]_vars` step away from a reachable state. -/
  | step {s t} : Reachable hN s → Step hN s t → Reachable hN t

/-! ## `Inv` and its helpers -/

/-- TLA+ `B == Sum(pending, Node)`: the number of messages in flight. -/
def B (s : State N) : ℤ := ∑ i : Node N, (s.pending i : ℤ)

/-- TLA+ `Rng(a, b) == {i \in Node : a <= i /\ i <= b}`, the node interval the invariant's clauses speak
about. -/
def Rng (a b : ℕ) : Finset (Node N) := Finset.univ.filter fun i => a ≤ i.val ∧ i.val ≤ b

/-- TLA+ `Sum(counter, Rng(a, b))`, the interval's counted-message sum. -/
def counterSum (s : State N) (a b : ℕ) : ℤ := (Rng (N := N) a b).sum s.counter

/-- **Safra's inductive invariant**, `Inv` at `EWD998.tla:168-183`: the counted messages at each node and
the messages in transit are consistent (`P0`), and the four-way disjunction `P1`–`P4` that makes the
invariant inductive. The seed states this and nothing else. -/
def Inv (s : State N) : Prop :=
  -- P0: the in-flight count and the counted messages agree.
  B s = ∑ i : Node N, s.counter i ∧
    (-- P1: every node past the token's position is passive, and the token's count is the sum over them.
      ((∀ i : Node N, s.token.pos.val < i.val → s.active i = false) ∧
        (if s.token.pos.val = N - 1 then s.token.q = 0
         else s.token.q = counterSum s (s.token.pos.val + 1) (N - 1))) ∨
      -- P2: the prefix's counted messages plus the token's count is positive.
      counterSum s 0 s.token.pos.val + s.token.q > 0 ∨
      -- P3: some node in the prefix is black.
      (∃ i : Node N, i.val ≤ s.token.pos.val ∧ s.color i = Color.black) ∨
      -- P4: the token is black.
      s.token.color = Color.black)

/-! ## The theorem -/

/-- **Invariance**, in general (tier 2, protocol §2): every state reachable under `Init /\ [][Next]_vars`
satisfies Safra's inductive invariant, at every `N ≥ 1` — the TLA+ `Init /\ [][Next]_vars => []Inv`
(`EWD998_proof.tla:176`) under `ASSUME N \in Nat \ {0}` (`EWD998.tla:19`). No fairness is asserted: that
belongs to the liveness theorem the module proves separately. -/
theorem inv (hN : 1 ≤ N) (s : State N) (hs : Reachable (Nat.lt_of_lt_of_le Nat.zero_lt_one hN) s) : Inv s := by
  sorry

end EWD998
