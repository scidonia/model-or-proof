/-
Token-passing ring mutual exclusion — the Lean model for Route B (protocol §2).

This is the idiomatic counterpart of `specs/tla/token-ring/TokenRing.tla`. The statement-by-statement
correspondence is audited in `docs/equivalence-token-ring.md` (protocol §4.1); the model neither
strengthens an assumption nor weakens the goal (plan D9).

This file is the closure loop's **tier-2 seed** (plan D5): the theorem statement is the human's, the
proof is the loop's, and the `sorry` below is the seed's placeholder, not a result — the run is closed
only when the harness has observed it gone (protocol §8). The tier-1 corollary at `N₀` is a separate
seed, `TokenRingN0.lean`, which imports this model and states `mutex_n0` over it (protocol §2: tier 1
is the general theorem instantiated at `N₀`, so it cannot live in the same file as the general
statement without a second unclosed goal in the artifact).
-/
import Mathlib

namespace TokenRing

/-! ## The state -/

/-- A node's program counter — TLA+ `pc[i] \in {"idle", "wait", "crit"}`. -/
inductive Phase where
  | idle
  | wait
  | crit
  deriving DecidableEq

/-- `Phase` is the three-element type. Written out rather than derived: at this pin
(`v4.35.0-rc3` + Mathlib `c55e6e78`) `deriving Fintype` emits a `Finset` construction that does not
type-check against Mathlib's `Finset`. -/
instance : Fintype Phase where
  elems := {Phase.idle, Phase.wait, Phase.crit}
  complete := by intro p; cases p <;> simp

/-- The nodes of the ring — TLA+ `Nodes == 0 .. (N - 1)`. -/
abbrev Node (N : ℕ) := Fin N

/-- TLA+ `VARIABLES token, pc`. TLA+'s `TypeOK` is carried by this type: `token` and the domain of
`pc` are the nodes of the ring, and `pc` takes values among the three phases. -/
structure State (N : ℕ) where
  /-- The node holding the token. -/
  token : Node N
  /-- Each node's program counter. -/
  pc : Node N → Phase

variable {N : ℕ}

/-- The ring's node after `i` — TLA+ `(i + 1) % N`. -/
def ringSucc (i : Node N) : Node N :=
  ⟨(i.val + 1) % N, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

/-- The ring's node `0`, which `Init` places the token on — TLA+ `0`, the first element of `Nodes`.
It exists because `N ≥ 2` (TLA+'s `ASSUME NAssumption`). -/
def nodeZero (hN : 2 ≤ N) : Node N := ⟨0, by omega⟩

/-! ## The actions -/

/-- TLA+ `Init == token = 0 /\ pc = [i \in Nodes |-> "idle"]`. -/
def Init (hN : 2 ≤ N) (s : State N) : Prop :=
  s.token = nodeZero hN ∧ s.pc = fun _ => Phase.idle

/-- TLA+ `Request(i)`: an idle node starts waiting; the token does not move. -/
def Request (i : Node N) (s t : State N) : Prop :=
  s.pc i = Phase.idle ∧ t.pc = Function.update s.pc i Phase.wait ∧ t.token = s.token

/-- TLA+ `Enter(i)`: a waiting node enters its critical section, and only the token holder may — this
conjunct is what the mutant `TokenRingMutant.lean` drops. -/
def Enter (i : Node N) (s t : State N) : Prop :=
  s.pc i = Phase.wait ∧ s.token = i ∧ t.pc = Function.update s.pc i Phase.crit ∧ t.token = s.token

/-- TLA+ `Release(i)`: the critical section is left idle and the token passes to the next node. -/
def Release (i : Node N) (s t : State N) : Prop :=
  s.pc i = Phase.crit ∧ t.pc = Function.update s.pc i Phase.idle ∧ t.token = ringSucc i

/-- TLA+ `Next == \E i \in Nodes : Request(i) \/ Enter(i) \/ Release(i)`. -/
def Next (s t : State N) : Prop :=
  ∃ i : Node N, Request i s t ∨ Enter i s t ∨ Release i s t

/-- TLA+ `[Next]_vars`: a step of `Next`, or a step that changes nothing. -/
def Step (s t : State N) : Prop := Next s t ∨ t = s

/-- The states admitted by TLA+ `Spec == Init /\ [][Next]_vars`, read as a state predicate — the
invariance reading of a safety property, which is what `Mutex` is (protocol §11 decision 4). -/
inductive Reachable (hN : 2 ≤ N) : State N → Prop where
  /-- The initial states. -/
  | init {s} : Init hN s → Reachable hN s
  /-- The states one `[Next]_vars` step away from a reachable state. -/
  | step {s t} : Reachable hN s → Step s t → Reachable hN t

/-- TLA+ `Mutex == Cardinality({i \in Nodes : pc[i] = "crit"}) <= 1`: at most one node is in its
critical section. -/
def Mutex (s : State N) : Prop :=
  (Finset.univ.filter fun i => s.pc i = Phase.crit).card ≤ 1

/-! ## The theorem -/

/-- **Mutual exclusion**, in general (tier 2, protocol §2): every state reachable under `Spec` has at
most one node in its critical section — TLA+ `Spec => []Mutex`. -/
theorem mutex (hN : 2 ≤ N) (s : State N) (hs : Reachable hN s) : Mutex s := by
  have inv : ∀ s : State N, Reachable hN s → ∀ i : Node N, s.pc i = Phase.crit → s.token = i := by
    intro s hs
    induction hs with
    | init =>
        rename_i s0 hinit
        rcases hinit with ⟨htok, hpc⟩
        intro i hi
        simp [hpc] at hi
    | step =>
        rename_i s0 t0 hstep hst ih
        rcases hst with hNext | hEq
        · rcases hNext with ⟨i, hi⟩
          rcases hi with hReq | hEnt | hRel
          · rcases hReq with ⟨hpc, hpct, htok⟩
            intro j hj
            by_cases hij : j = i
            · subst j
              simp [hpct] at hj
            · have hs_crit : s0.pc j = Phase.crit := by
                simpa [hpct, Function.update_of_ne hij] using hj
              exact htok.trans (ih j hs_crit)
          · rcases hEnt with ⟨hpc, htok, hpct, htokt⟩
            intro j hj
            by_cases hij : j = i
            · subst j
              exact htokt.trans htok
            · have hs_crit : s0.pc j = Phase.crit := by
                simpa [hpct, Function.update_of_ne hij] using hj
              exact False.elim (hij ((ih j hs_crit).symm.trans htok))
          · rcases hRel with ⟨hpc, hpct, htokt⟩
            intro j hj
            by_cases hij : j = i
            · subst j
              simp [hpct] at hj
            · have hs_crit : s0.pc j = Phase.crit := by
                simpa [hpct, Function.update_of_ne hij] using hj
              exact False.elim (hij ((ih j hs_crit).symm.trans (ih i hpc)))
        · subst t0
          intro i hi
          exact ih i hi
  have mutex_of_inv : ∀ s : State N, (∀ i : Node N, s.pc i = Phase.crit → s.token = i) → Mutex s := by
    intro s h
    rw [Mutex, Finset.card_le_one]
    intro a ha b hb
    have hca : s.pc a = Phase.crit := (Finset.mem_filter.mp ha).2
    have hcb : s.pc b = Phase.crit := (Finset.mem_filter.mp hb).2
    exact (h a hca).symm.trans (h b hcb)
  exact mutex_of_inv s (inv s hs)
end TokenRing
