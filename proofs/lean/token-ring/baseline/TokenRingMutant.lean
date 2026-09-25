/-
Token-passing ring, **negative control** (Route B): the analogue of
`specs/tla/token-ring/TokenRingMutant.tla`.

Identical to `TokenRing.lean` except that `Enter` drops the conjunct `token = i` — a node may enter
its critical section while holding no token. Two nodes can then be critical at once, so the theorem
stated below is **false** and no proof can close it: the expected Route B outcome is `fail_to_close`,
and a run that reports `success` on this file is broken and its numbers are discarded (protocol §5,
plan D7).

The statement is the seed of that run (plan D5): as in `TokenRing.lean`, the model and the statement
are the human's, the proof search is the loop's.
-/
import Mathlib

namespace TokenRingMutant

/-! ## The state -/

/-- A node's program counter — TLA+ `pc[i] \in {"idle", "wait", "crit"}`. -/
inductive Phase where
  | idle
  | wait
  | crit
  deriving DecidableEq

/-- The three-element instance, written out rather than derived (see `TokenRing.lean`). -/
instance : Fintype Phase where
  elems := {Phase.idle, Phase.wait, Phase.crit}
  complete := by intro p; cases p <;> simp

/-- The nodes of the ring — TLA+ `Nodes == 0 .. (N - 1)`. -/
abbrev Node (N : ℕ) := Fin N

/-- TLA+ `VARIABLES token, pc`, with `TypeOK` carried by the type. -/
structure State (N : ℕ) where
  /-- The node holding the token. -/
  token : Node N
  /-- Each node's program counter. -/
  pc : Node N → Phase

variable {N : ℕ}

/-- The ring's node after `i` — TLA+ `(i + 1) % N`. -/
def ringSucc (i : Node N) : Node N :=
  ⟨(i.val + 1) % N, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

/-- The ring's node `0`, which `Init` places the token on — TLA+ `0`, the first element of `Nodes`. -/
def nodeZero (hN : 2 ≤ N) : Node N := ⟨0, by omega⟩

/-! ## The actions -/

/-- TLA+ `Init == token = 0 /\ pc = [i \in Nodes |-> "idle"]`. -/
def Init (hN : 2 ≤ N) (s : State N) : Prop :=
  s.token = nodeZero hN ∧ s.pc = fun _ => Phase.idle

/-- TLA+ `Request(i)`: an idle node starts waiting; the token does not move. -/
def Request (i : Node N) (s t : State N) : Prop :=
  s.pc i = Phase.idle ∧ t.pc = Function.update s.pc i Phase.wait ∧ t.token = s.token

/-- **The mutation.** TLA+ `Enter(i)`-minus-the-guard: a waiting node enters its critical section
regardless of who holds the token (upstream drops `token = i`). -/
def Enter (i : Node N) (s t : State N) : Prop :=
  s.pc i = Phase.wait ∧ t.pc = Function.update s.pc i Phase.crit ∧ t.token = s.token

/-- TLA+ `Release(i)`: the critical section is left idle and the token passes to the next node. -/
def Release (i : Node N) (s t : State N) : Prop :=
  s.pc i = Phase.crit ∧ t.pc = Function.update s.pc i Phase.idle ∧ t.token = ringSucc i

/-- TLA+ `Next == \E i \in Nodes : Request(i) \/ Enter(i) \/ Release(i)`. -/
def Next (s t : State N) : Prop :=
  ∃ i : Node N, Request i s t ∨ Enter i s t ∨ Release i s t

/-- TLA+ `[Next]_vars`: a step of `Next`, or a step that changes nothing. -/
def Step (s t : State N) : Prop := Next s t ∨ t = s

/-- The states admitted by TLA+ `Spec == Init /\ [][Next]_vars`, read as a state predicate. -/
inductive Reachable (hN : 2 ≤ N) : State N → Prop where
  /-- The initial states. -/
  | init {s} : Init hN s → Reachable hN s
  /-- The states one `[Next]_vars` step away from a reachable state. -/
  | step {s t} : Reachable hN s → Step s t → Reachable hN t

/-- TLA+ `Mutex == Cardinality({i \in Nodes : pc[i] = "crit"}) <= 1` — the property TLC refutes on
`specs/tla/token-ring/TokenRingMutant.tla` (`N = 3`), and the loop must fail to close here. -/
def Mutex (s : State N) : Prop :=
  (Finset.univ.filter fun i => s.pc i = Phase.crit).card ≤ 1

/-! ## The theorem (false — the point of the mutant) -/

/-- **Mutual exclusion**, in general: false for this model, since `Enter` dropped its guard. Two
waiting nodes may enter one after the other, so a state with two nodes critical is reachable from
`Init`; the loop cannot close this and must not appear to (protocol §5, plan D7). -/
theorem mutex (hN : 2 ≤ N) (s : State N) (hs : Reachable hN s) : Mutex s := by
  sorry

end TokenRingMutant
