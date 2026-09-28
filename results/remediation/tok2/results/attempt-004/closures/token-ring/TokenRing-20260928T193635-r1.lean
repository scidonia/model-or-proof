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
  have h_inv : ∀ t, Reachable hN t → Mutex t ∧ ∀ j, t.pc j = Phase.crit → t.token = j := by
    intro t ht
    induction ht with
    | init =>
        rename_i s hinit
        constructor
        · rw [Mutex]
          simp [hinit.2]
        · intro j hj
          rw [hinit.2] at hj
          simp at hj
    | step =>
        rename_i s' t' hs hst ih
        rcases ih with ⟨hM, hT⟩
        rcases hst with hNext | hEq
        · rcases hNext with ⟨i, hstep⟩
          rcases hstep with hreq | hent | hrel
          · rcases hreq with ⟨hidle, hpc, htok⟩
            constructor
            · rw [Mutex]
              apply Finset.card_le_one.mpr
              intro a ha b hb
              rw [Finset.mem_filter] at ha hb
              rcases ha with ⟨_, hca⟩
              rcases hb with ⟨_, hcb⟩
              have hsa : s'.pc a = Phase.crit := by
                rw [hpc] at hca
                by_cases hai : a = i
                · subst a
                  simp [Function.update] at hca
                · simpa [Function.update, hai] using hca
              have hsb : s'.pc b = Phase.crit := by
                rw [hpc] at hcb
                by_cases hbi : b = i
                · subst b
                  simp [Function.update] at hcb
                · simpa [Function.update, hbi] using hcb
              have ha' : a ∈ Finset.univ.filter (fun k => s'.pc k = Phase.crit) := by
                simp [hsa]
              have hb' : b ∈ Finset.univ.filter (fun k => s'.pc k = Phase.crit) := by
                simp [hsb]
              exact (Finset.card_le_one.mp hM) a ha' b hb'
            · intro j hj
              rw [hpc] at hj
              by_cases hji : j = i
              · subst j
                simp [Function.update] at hj
              · have hsj : s'.pc j = Phase.crit := by
                  simpa [Function.update, hji] using hj
                have htj : s'.token = j := hT j hsj
                rw [htok]
                exact htj
          · rcases hent with ⟨hwait, htok_i, hpc, htok⟩
            constructor
            · rw [Mutex]
              apply Finset.card_le_one.mpr
              intro a ha b hb
              rw [Finset.mem_filter] at ha hb
              rcases ha with ⟨_, hca⟩
              rcases hb with ⟨_, hcb⟩
              have ha_i : a = i := by
                rw [hpc] at hca
                by_cases hai : a = i
                · exact hai
                · have hsa : s'.pc a = Phase.crit := by
                    simpa [Function.update, hai] using hca
                  have hta : s'.token = a := hT a hsa
                  have hia : a = i := hta.symm.trans htok_i
                  exact False.elim (hai hia)
              have hb_i : b = i := by
                rw [hpc] at hcb
                by_cases hbi : b = i
                · exact hbi
                · have hsb : s'.pc b = Phase.crit := by
                    simpa [Function.update, hbi] using hcb
                  have htb : s'.token = b := hT b hsb
                  have hib : b = i := htb.symm.trans htok_i
                  exact False.elim (hbi hib)
              exact ha_i.trans hb_i.symm
            · intro j hj
              rw [hpc] at hj
              by_cases hji : j = i
              · subst j
                rw [htok]
                exact htok_i
              · have hsj : s'.pc j = Phase.crit := by
                  simpa [Function.update, hji] using hj
                have htj : s'.token = j := hT j hsj
                rw [htok]
                exact htj
          · rcases hrel with ⟨hcrit, hpc, htok⟩
            constructor
            · rw [Mutex]
              apply Finset.card_le_one.mpr
              intro a ha b hb
              rw [Finset.mem_filter] at ha hb
              rcases ha with ⟨_, hca⟩
              rcases hb with ⟨_, hcb⟩
              have hsa : s'.pc a = Phase.crit := by
                rw [hpc] at hca
                by_cases hai : a = i
                · subst a
                  simp [Function.update] at hca
                · simpa [Function.update, hai] using hca
              have hsb : s'.pc b = Phase.crit := by
                rw [hpc] at hcb
                by_cases hbi : b = i
                · subst b
                  simp [Function.update] at hcb
                · simpa [Function.update, hbi] using hcb
              have ha' : a ∈ Finset.univ.filter (fun k => s'.pc k = Phase.crit) := by
                simp [hsa]
              have hb' : b ∈ Finset.univ.filter (fun k => s'.pc k = Phase.crit) := by
                simp [hsb]
              exact (Finset.card_le_one.mp hM) a ha' b hb'
            · intro j hj
              rw [hpc] at hj
              by_cases hji : j = i
              · subst j
                simp [Function.update] at hj
              · have hsj : s'.pc j = Phase.crit := by
                  simpa [Function.update, hji] using hj
                have htj : s'.token = j := hT j hsj
                have hti : s'.token = i := hT i hcrit
                have hji' : j = i := by
                  rw [← htj, hti]
                exact False.elim (hji hji')
        · subst t'
          exact ⟨hM, hT⟩
  exact (h_inv s hs).1


end TokenRing
