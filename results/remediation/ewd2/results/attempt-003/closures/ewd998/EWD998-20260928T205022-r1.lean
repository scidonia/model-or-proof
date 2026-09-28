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
  have hN0 : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have rng_singleton : ∀ (i : Node N) (p : ℕ), i.val = p → Rng (N := N) p p = {i} := by
    intro i p hi
    ext j
    simp only [Rng, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hj
      apply Fin.ext
      rw [hi]
      omega
    · intro hji
      subst hji
      simp [hi]
  have counterSum_singleton : ∀ (s : State N) (i : Node N) (p : ℕ), i.val = p → counterSum s p p = s.counter i := by
    intro s i p hi
    rw [counterSum, rng_singleton i p hi]
    simp
  have rng_split_right : ∀ (i : Node N) (p b : ℕ), i.val = p → p ≤ b → Rng (N := N) p b = insert i (Rng (N := N) (p+1) b) := by
    intro i p b hi hpb
    ext j
    simp only [Rng, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hji : j = i
    · subst hji
      simp [hi, hpb]
    · have hjp : j.val ≠ p := by
        intro h
        apply hji
        apply Fin.ext
        rw [hi, h]
      constructor
      · intro hj
        right
        exact ⟨by omega, hj.2⟩
      · intro hj
        rcases hj with h | hj
        · exact False.elim (hji h)
        · exact ⟨by omega, hj.2⟩
  have counterSum_split_right : ∀ (s : State N) (i : Node N) (p b : ℕ), i.val = p → p ≤ b → counterSum s p b = s.counter i + counterSum s (p+1) b := by
    intro s i p b hi hpb
    rw [counterSum, rng_split_right i p b hi hpb]
    rw [Finset.sum_insert]
    · rw [counterSum]
    · intro h
      simp only [Rng, Finset.mem_filter, Finset.mem_univ, true_and] at h
      omega
  have rng_split_left : ∀ (i : Node N) (p : ℕ), i.val = p → 1 ≤ p → Rng (N := N) 0 p = insert i (Rng (N := N) 0 (p-1)) := by
    intro i p hi hp
    ext j
    simp only [Rng, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hji : j = i
    · subst hji
      simp [hi]
    · have hjp : j.val ≠ p := by
        intro h
        apply hji
        apply Fin.ext
        rw [hi, h]
      constructor
      · intro hj
        right
        exact ⟨Nat.zero_le _, by omega⟩
      · intro hj
        rcases hj with h | hj
        · exact False.elim (hji h)
        · exact ⟨Nat.zero_le _, by omega⟩
  have counterSum_split_left : ∀ (s : State N) (i : Node N) (p : ℕ), i.val = p → 1 ≤ p → counterSum s 0 p = s.counter i + counterSum s 0 (p-1) := by
    intro s i p hi hp
    rw [counterSum, rng_split_left i p hi hp]
    rw [Finset.sum_insert]
    · rw [counterSum]
    · intro h
      simp only [Rng, Finset.mem_filter, Finset.mem_univ, true_and] at h
      omega
  have counterSum_congr : ∀ (u v : State N) (a b : ℕ), u.counter = v.counter → counterSum u a b = counterSum v a b := by
    intro u v a b h
    simp [counterSum, h]
  have sum_update_of_not_mem : ∀ (c : Node N → ℤ) (i : Node N) (v : ℤ) (a b : ℕ),
      i.val < a ∨ b < i.val →
      (Rng (N := N) a b).sum (Function.update c i v) = (Rng (N := N) a b).sum c := by
    intro c i v a b h
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hji : j ≠ i := by
      intro hji
      have hval : j.val = i.val := by rw [hji]
      have hmem : a ≤ j.val ∧ j.val ≤ b := by
        simp [Rng] at hj
        exact hj
      rcases h with h1 | h2
      · omega
      · omega
    simp [hji]
  have sum_update_add_one : ∀ (c : Node N → ℤ) (i : Node N) (a b : ℕ),
      a ≤ i.val → i.val ≤ b →
      (Rng (N := N) a b).sum (Function.update c i (c i + 1)) = (Rng (N := N) a b).sum c + 1 := by
    intro c i a b ha hb
    have himem : i ∈ Rng (N := N) a b := by
      simp [Rng, ha, hb]
    rw [Finset.sum_update_of_mem himem]
    rw [← Finset.erase_eq (Rng (N := N) a b) i]
    have herase : ((Rng (N := N) a b).erase i).sum c = (Rng (N := N) a b).sum c - c i := by
      exact Finset.sum_erase_eq_sub himem
    rw [herase]
    ring
  have counterSum_nonneg : ∀ (u : State N) (a b : ℕ), (∀ j : Node N, 0 ≤ u.counter j) → 0 ≤ counterSum u a b := by
    intro u a b h
    simp [counterSum]
    exact Finset.sum_nonneg (by intro j hj; exact h j)
  have rng_empty : ∀ (a b : ℕ), (∀ j : Node N, ¬ (a ≤ j.val ∧ j.val ≤ b)) → Rng (N := N) a b = ∅ := by
    intro a b h
    ext j
    constructor
    · intro hjmem
      have hm : a ≤ j.val ∧ j.val ≤ b := by
        simpa [Rng] using hjmem
      exfalso
      exact h j hm
    · intro hjempty
      simp at hjempty
  have hfull : Inv s ∧ (∀ i : Node N, (s.pending i : ℤ) = s.counter i) := by
    induction hs with
    | init hinit =>
        rcases hinit with ⟨hc, hp, hpos, hq, hcol⟩
        constructor
        · rw [Inv]
          constructor
          · simp [B, hc, hp]
          · right; right; right; exact hcol
        · intro i
          simp [hc, hp]
    | step ih hstep =>
        rename_i sprev tgt ihFull
        rcases ihFull with ⟨ihInv, ihpc⟩
        have hnonneg : ∀ j : Node N, 0 ≤ sprev.counter j := by
          intro j
          have h := ihpc j
          omega
        have hpc_tgt : ∀ i : Node N, (tgt.pending i : ℤ) = tgt.counter i := by
          rcases hstep with hnext | hsame
          · rcases hnext with hsys | henv
            · rcases hsys with hip | hpass
              · rcases hip with ⟨hpos, hcond, htoken, hcolor, hactive, hcounter, hpending⟩
                intro j
                rw [← hpending, ← hcounter, ihpc j]
              · rcases hpass with ⟨i, hi0, hp⟩
                rcases hp with ⟨hai, hpos, htoken, hcolor, hactive, hcounter, hpending⟩
                intro j
                rw [← hpending, ← hcounter, ihpc j]
            · rcases henv with ⟨i, henvi⟩
              rcases henvi with hsm | hrc | hda
              · rcases hsm with ⟨hai, hj, hcounter, hpending, hactive, hcolor, htoken⟩
                intro j
                by_cases hji : j = i
                · simp [hcounter, hpending, hji, ihpc i]
                · simp [hcounter, hpending, hji, ihpc j]
              · rcases hrc with ⟨hpend, hpending, hcounter, hcolor, hactive, htoken⟩
                intro j
                by_cases hji : j = i
                · have hcast : ((sprev.pending i - 1 : ℕ) : ℤ) = (sprev.pending i : ℤ) - 1 := by omega
                  simp [hcounter, hpending, hji, hcast, ihpc i]
                · simp [hcounter, hpending, hji, ihpc j]
              · rcases hda with ⟨hai, hactive, hcolor, hcounter, hpending, htoken⟩
                intro j
                rw [← hpending, ← hcounter, ihpc j]
          · subst tgt
            exact ihpc
        have hInv_tgt : Inv tgt := by
          rw [Inv]
          constructor
          · simp [B, hpc_tgt]
          · rcases hstep with hnext | hsame
            · rcases hnext with hsys | henv
              · rcases hsys with hip | hpass
                · rcases hip with ⟨hpos, hcond, htoken, hcolor, hactive, hcounter, hpending⟩
                  left
                  constructor
                  · intro j hj
                    have htokpos : tgt.token.pos.val = N - 1 := by rw [htoken]; rfl
                    have hjlt : j.val < N := j.isLt
                    have hjN : j.val ≤ N - 1 := by omega
                    omega
                  · have htokpos : tgt.token.pos.val = N - 1 := by rw [htoken]; rfl
                    rw [htokpos]
                    simp [htoken]
                · rcases hpass with ⟨i, hi0, hp⟩
                  rcases hp with ⟨hai, hpos, htoken, hcolor, hactive, hcounter, hpending⟩
                  have hi1 : 1 ≤ i.val := by
                    have hi0' : i.val ≠ 0 := by
                      intro h
                      apply hi0
                      apply Fin.ext
                      simp [h]
                    omega
                  rcases ihInv.2 with hP1 | hP2 | hP3 | hP4
                  · left
                    constructor
                    · intro j hj
                      by_cases hji : j = i
                      · subst hji
                        rw [← hactive]
                        exact hai
                      · have htokpos : tgt.token.pos.val = i.val - 1 := by rw [htoken]; rfl
                        have hj' : i.val - 1 < j.val := by
                          simpa [htokpos] using hj
                        have hjne : j.val ≠ i.val := by
                          intro h
                          apply hji
                          apply Fin.ext
                          exact h
                        have hgt : sprev.token.pos.val < j.val := by
                          have hpval : sprev.token.pos.val = i.val := by rw [hpos]
                          rw [hpval]
                          omega
                        rw [← hactive]
                        exact hP1.1 j hgt
                    · have hpval : sprev.token.pos.val = i.val := by rw [hpos]
                      have hne : tgt.token.pos.val ≠ N - 1 := by
                        have htokpos : tgt.token.pos.val = i.val - 1 := by rw [htoken]; rfl
                        rw [htokpos]
                        have hiN : i.val < N := i.isLt
                        omega
                      rw [if_neg hne]
                      have htokq : tgt.token.q = sprev.token.q + sprev.counter i := by simp [htoken]
                      rw [htokq]
                      have htokpos : tgt.token.pos.val = i.val - 1 := by rw [htoken]; rfl
                      rw [htokpos]
                      have hsum : i.val - 1 + 1 = i.val := by omega
                      rw [hsum]
                      have hcs : counterSum tgt i.val (N - 1) = counterSum sprev i.val (N - 1) := by
                        apply counterSum_congr
                        rw [hcounter]
                      rw [hcs]
                      have hsplit : counterSum sprev i.val (N - 1) = sprev.counter i + counterSum sprev (i.val + 1) (N - 1) := by
                        exact counterSum_split_right sprev i i.val (N - 1) rfl (by omega)
                      rw [hsplit]
                      by_cases hlast : i.val = N - 1
                      · have hq : sprev.token.q = 0 := by
                          have hP12 := hP1.2
                          have hcond : sprev.token.pos.val = N - 1 := by rw [hpval]; exact hlast
                          rw [if_pos hcond] at hP12
                          exact hP12
                        rw [hq]
                        have hempty : counterSum sprev (i.val + 1) (N - 1) = 0 := by
                          have hRng : Rng (N := N) (i.val + 1) (N - 1) = ∅ := by
                            apply rng_empty
                            intro j
                            rw [hlast]
                            have hjlt : j.val < N := j.isLt
                            omega
                          rw [counterSum, hRng]
                          simp
                        rw [hempty]
                        ring
                      · have hq : sprev.token.q = counterSum sprev (i.val + 1) (N - 1) := by
                          have hP12 := hP1.2
                          have hcond : sprev.token.pos.val ≠ N - 1 := by rw [hpval]; exact hlast
                          rw [if_neg hcond] at hP12
                          simpa [hpval] using hP12
                        rw [hq]
                        ring
                  · right; left
                    have hsplit : counterSum sprev 0 i.val = sprev.counter i + counterSum sprev 0 (i.val - 1) := by
                      exact counterSum_split_left sprev i i.val rfl hi1
                    have hpval : sprev.token.pos.val = i.val := by rw [hpos]
                    rw [hpval] at hP2
                    have htokpos : tgt.token.pos.val = i.val - 1 := by rw [htoken]; rfl
                    rw [htokpos]
                    have htokq : tgt.token.q = sprev.token.q + sprev.counter i := by simp [htoken]
                    rw [htokq]
                    have hcs : counterSum tgt 0 (i.val - 1) = counterSum sprev 0 (i.val - 1) := by
                      apply counterSum_congr
                      rw [hcounter]
                    rw [hcs]
                    omega
                  · rcases hP3 with ⟨j, hjle, hjcol⟩
                    by_cases hji : j = i
                    · subst hji
                      right; right; right
                      simp [htoken, hjcol]
                    · right; right; left
                      refine ⟨j, ?_, ?_⟩
                      · have htokpos : tgt.token.pos.val = i.val - 1 := by rw [htoken]; rfl
                        rw [htokpos]
                        have hjne : j.val ≠ i.val := by
                          intro h
                          apply hji
                          apply Fin.ext
                          exact h
                        have hjle' : j.val ≤ i.val := by
                          simpa [hpos] using hjle
                        have hlt : j.val < i.val := by omega
                        exact Nat.le_sub_one_of_lt hlt
                      · rw [hcolor]
                        simp [hji, hjcol]
                  · right; right; right
                    by_cases hc : sprev.color i = Color.black
                    · simp [htoken, hc]
                    · simp [htoken, hc, hP4]
              · rcases henv with ⟨i, henvi⟩
                rcases henvi with hsm | hrc | hda
                · rcases hsm with ⟨hai, hj, hcounter, hpending, hactive, hcolor, htoken⟩
                  rcases ihInv.2 with hP1 | hP2 | hP3 | hP4
                  · left
                    constructor
                    · intro j hj
                      rw [← htoken] at hj
                      rw [← hactive]
                      exact hP1.1 j hj
                    · have hile : i.val ≤ sprev.token.pos.val := by
                        by_contra h
                        have hgt : sprev.token.pos.val < i.val := by omega
                        have hfalse : sprev.active i = false := hP1.1 i hgt
                        rw [hai] at hfalse
                        contradiction
                      rw [← htoken]
                      have hilt : i.val < sprev.token.pos.val + 1 := by omega
                      have hcs : counterSum tgt (sprev.token.pos.val + 1) (N - 1) = counterSum sprev (sprev.token.pos.val + 1) (N - 1) := by
                        simp only [counterSum, hcounter]
                        exact sum_update_of_not_mem sprev.counter i (sprev.counter i + 1) (sprev.token.pos.val + 1) (N - 1) (Or.inl hilt)
                      rw [hcs]
                      exact hP1.2
                  · right; left
                    rw [← htoken]
                    by_cases hile : i.val ≤ sprev.token.pos.val
                    · have hcs : counterSum tgt 0 sprev.token.pos.val = counterSum sprev 0 sprev.token.pos.val + 1 := by
                        simp only [counterSum, hcounter]
                        exact sum_update_add_one sprev.counter i 0 sprev.token.pos.val (Nat.zero_le _) hile
                      rw [hcs]
                      omega
                    · have hgt : sprev.token.pos.val < i.val := by omega
                      have hcs : counterSum tgt 0 sprev.token.pos.val = counterSum sprev 0 sprev.token.pos.val := by
                        simp only [counterSum, hcounter]
                        exact sum_update_of_not_mem sprev.counter i (sprev.counter i + 1) 0 sprev.token.pos.val (Or.inr hgt)
                      rw [hcs]
                      exact hP2
                  · right; right; left
                    rcases hP3 with ⟨j, hjle, hjcol⟩
                    refine ⟨j, ?_, ?_⟩
                    · rw [← htoken]
                      exact hjle
                    · rw [← hcolor]
                      exact hjcol
                  · right; right; right
                    rw [← htoken]
                    exact hP4
                · rcases hrc with ⟨hpend, hpending, hcounter, hcolor, hactive, htoken⟩
                  have hci_pos : 0 < sprev.counter i := by
                    have h := ihpc i
                    omega
                  rcases ihInv.2 with hP1 | hP2 | hP3 | hP4
                  · by_cases hile : i.val ≤ sprev.token.pos.val
                    · left
                      constructor
                      · intro j hj
                        rw [← htoken] at hj
                        have hji : j ≠ i := by
                          intro hji
                          subst hji
                          omega
                        have hact : tgt.active j = sprev.active j := by
                          rw [hactive]
                          simp [hji]
                        rw [hact]
                        exact hP1.1 j hj
                      · rw [← htoken]
                        have hilt : i.val < sprev.token.pos.val + 1 := by omega
                        have hcs : counterSum tgt (sprev.token.pos.val + 1) (N - 1) = counterSum sprev (sprev.token.pos.val + 1) (N - 1) := by
                          simp only [counterSum, hcounter]
                          exact sum_update_of_not_mem sprev.counter i (sprev.counter i - 1) (sprev.token.pos.val + 1) (N - 1) (Or.inl hilt)
                        rw [hcs]
                        exact hP1.2
                    · right; left
                      have hq_pos : 0 < sprev.token.q := by
                        have hc : sprev.token.pos.val ≠ N - 1 := by
                          have hiN : i.val < N := i.isLt
                          omega
                        have hqsum : sprev.token.q = counterSum sprev (sprev.token.pos.val + 1) (N - 1) := by
                          have hP12 := hP1.2
                          rw [if_neg hc] at hP12
                          exact hP12
                        have himem : i ∈ Rng (N := N) (sprev.token.pos.val + 1) (N - 1) := by
                          simp [Rng]
                          omega
                        have hge : sprev.counter i ≤ counterSum sprev (sprev.token.pos.val + 1) (N - 1) := by
                          have hsingle := Finset.single_le_sum (s := Rng (N := N) (sprev.token.pos.val + 1) (N - 1)) (f := sprev.counter) (by intro j hj; exact hnonneg j) himem
                          simpa [counterSum] using hsingle
                        rw [hqsum]
                        omega
                      rw [← htoken]
                      have hgt : sprev.token.pos.val < i.val := by omega
                      have hcs : counterSum tgt 0 sprev.token.pos.val = counterSum sprev 0 sprev.token.pos.val := by
                        simp only [counterSum, hcounter]
                        exact sum_update_of_not_mem sprev.counter i (sprev.counter i - 1) 0 sprev.token.pos.val (Or.inr hgt)
                      rw [hcs]
                      have hpos_nonneg : 0 ≤ counterSum sprev 0 sprev.token.pos.val := by
                        exact counterSum_nonneg sprev 0 sprev.token.pos.val hnonneg
                      omega
                  · by_cases hile : i.val ≤ sprev.token.pos.val
                    · right; right; left
                      refine ⟨i, ?_, ?_⟩
                      · rw [← htoken]
                        exact hile
                      · rw [hcolor]
                        simp
                    · right; left
                      rw [← htoken]
                      have hgt : sprev.token.pos.val < i.val := by omega
                      have hcs : counterSum tgt 0 sprev.token.pos.val = counterSum sprev 0 sprev.token.pos.val := by
                        simp only [counterSum, hcounter]
                        exact sum_update_of_not_mem sprev.counter i (sprev.counter i - 1) 0 sprev.token.pos.val (Or.inr hgt)
                      rw [hcs]
                      exact hP2
                  · right; right; left
                    rcases hP3 with ⟨j, hjle, hjcol⟩
                    by_cases hji : j = i
                    · subst hji
                      refine ⟨j, ?_, ?_⟩
                      · rw [← htoken]
                        exact hjle
                      · rw [hcolor]
                        simp
                    · refine ⟨j, ?_, ?_⟩
                      · rw [← htoken]
                        exact hjle
                      · rw [hcolor]
                        simp [hji, hjcol]
                  · right; right; right
                    rw [← htoken]
                    exact hP4
                · rcases hda with ⟨hai, hactive, hcolor, hcounter, hpending, htoken⟩
                  rcases ihInv.2 with hP1 | hP2 | hP3 | hP4
                  · left
                    constructor
                    · intro j hj
                      rw [← htoken] at hj
                      have hile : i.val ≤ sprev.token.pos.val := by
                        by_contra h
                        have hgt : sprev.token.pos.val < i.val := by omega
                        have hfalse : sprev.active i = false := hP1.1 i hgt
                        rw [hai] at hfalse
                        contradiction
                      by_cases hji : j = i
                      · subst hji
                        omega
                      · have hact : tgt.active j = sprev.active j := by
                          rw [hactive]
                          simp [hji]
                        rw [hact]
                        exact hP1.1 j hj
                    · rw [← htoken]
                      have hcs : counterSum tgt (sprev.token.pos.val + 1) (N - 1) = counterSum sprev (sprev.token.pos.val + 1) (N - 1) := by
                        apply counterSum_congr
                        rw [hcounter]
                      rw [hcs]
                      exact hP1.2
                  · right; left
                    rw [← htoken]
                    have hcs : counterSum tgt 0 sprev.token.pos.val = counterSum sprev 0 sprev.token.pos.val := by
                      apply counterSum_congr
                      rw [hcounter]
                    rw [hcs]
                    exact hP2
                  · right; right; left
                    rcases hP3 with ⟨j, hjle, hjcol⟩
                    refine ⟨j, ?_, ?_⟩
                    · rw [← htoken]
                      exact hjle
                    · rw [← hcolor]
                      exact hjcol
                  · right; right; right
                    rw [← htoken]
                    exact hP4
            · subst tgt
              exact ihInv.2
        exact ⟨hInv_tgt, hpc_tgt⟩
  exact hfull.1

end EWD998
