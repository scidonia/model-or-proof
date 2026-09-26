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
  have inv : ∀ (N : ℕ) (hN : 2 ≤ N) (s : State N), Reachable hN s →
      Mutex s ∧ ∀ i : Node N, s.pc i = Phase.crit → s.token = i := by
    intro N hN s hs
    induction hs with
    | init h =>
        refine ⟨?_, ?_⟩
        · simp [Mutex, h.2]
        · intro i hi
          rw [h.2] at hi
          simp at hi
    | step =>
        rename_i s t hs hstep ih
        rcases hstep with hnext | heq
        · rcases hnext with ⟨i, hreq | hent | hrel⟩
          · rcases hreq with ⟨hidle, hpc, htok⟩
            have hcrit : ∀ j : Node N, t.pc j = Phase.crit → t.token = j := by
              intro j hj
              rw [hpc] at hj
              by_cases hji : j = i
              · subst hji
                simp at hj
              · simp [Function.update, hji] at hj
                rw [htok]
                exact ih.2 j hj
            refine ⟨?_, hcrit⟩
            simp only [Mutex]
            rw [Finset.card_le_one]
            intro a ha b hb
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
            rw [← hcrit a ha, ← hcrit b hb]
          · rcases hent with ⟨hwait, htok_i, hpc, htok'⟩
            have hcrit : ∀ j : Node N, t.pc j = Phase.crit → t.token = j := by
              intro j hj
              rw [hpc] at hj
              by_cases hji : j = i
              · subst hji
                simp [Function.update] at hj
                rw [htok']
                exact htok_i
              · simp [Function.update, hji] at hj
                rw [htok']
                exact ih.2 j hj
            refine ⟨?_, hcrit⟩
            simp only [Mutex]
            rw [Finset.card_le_one]
            intro a ha b hb
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
            rw [← hcrit a ha, ← hcrit b hb]
          · rcases hrel with ⟨hcrit_i, hpc, htok⟩
            have hcrit : ∀ j : Node N, t.pc j = Phase.crit → t.token = j := by
              intro j hj
              have hji : j ≠ i := by
                intro hji
                rw [hji] at hj
                rw [hpc] at hj
                simp [Function.update] at hj
              have hsj : s.pc j = Phase.crit := by
                rw [hpc] at hj
                simpa [Function.update, hji] using hj
              have h1 : s.token = i := ih.2 i hcrit_i
              have h2 : s.token = j := ih.2 j hsj
              exact absurd ((h1.symm.trans h2).symm) hji
            refine ⟨?_, hcrit⟩
            simp only [Mutex]
            rw [Finset.card_le_one]
            intro a ha b hb
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
            rw [← hcrit a ha, ← hcrit b hb]
        · subst heq
          exact ih
  exact (inv N hN s hs).1

end TokenRing
