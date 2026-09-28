/-
Bakery mutual exclusion — the Lean model for Route B (protocol §2).

This is the idiomatic counterpart of `specs/tla/bakery/Bakery.tla`, Lamport's bakery algorithm in its
**bounded atomic-register** form: the shared registers `num` and `flag` are written by single atomic
steps and the ticket domain is bounded by `0 .. N`, so the state space is finite — which is what makes
the module TLC-checkable and what makes it a Route A reference at all (the imported IJCAR artifact's
safe-register encoding is infinite-state). The statement-by-statement correspondence is audited in
`docs/equivalence-bakery.md` (protocol §4.1); the model neither strengthens an assumption nor weakens
the goal.

This file is the closure loop's **tier-2 seed** (plan D5): the theorem statement is the human's, the
proof is the loop's, and the `sorry` below is the seed's placeholder, not a result — the run is closed
only when the harness has observed it gone (protocol §8). The tier-1 corollary at the task's `N₀` is a
separate seed (`BakeryN0.lean`) and is not written yet: `tasks/bakery.json`'s `n0` is still to be
calibrated (plan D23 rung 1). The negative control is `BakeryMutant.lean`.
-/
import Mathlib

namespace Bakery

/-! ## The state -/

/-- A process's program counter — TLA+ `pc[i] \in {"idle", "doorway", "wait", "crit"}`. -/
inductive Phase where
  | idle
  | doorway
  | wait
  | crit
  deriving DecidableEq

/-- The processes — TLA+ `P == 1 .. N`. -/
abbrev Process (N : ℕ) := Fin N

/-- A ticket — TLA+ `0 .. N`, the bounded ticket domain the module's `ChooseTicket` draws from. -/
abbrev Ticket (N : ℕ) := Fin (N + 1)

/-- TLA+ `VARIABLES num, flag, pc`. TLA+'s `TypeOK` is carried by this type: `num` ranges over the
bounded ticket domain, `flag` is boolean and `pc` takes values among the four phases, so no value of
`State N` can violate `TypeOK` and none can name a fifth phase. -/
structure State (N : ℕ) where
  /-- The ticket each process holds; `0` means "none". -/
  num : Process N → Ticket N
  /-- Whether each process is in the doorway. -/
  flag : Process N → Bool
  /-- Each process's program counter. -/
  pc : Process N → Phase

variable {N : ℕ}

/-! ## The model -/

/-- TLA+ `Init == /\ num = [i \in P |-> 0] /\ flag = [i \in P |-> FALSE] /\ pc = [i \in P |-> "idle"]`. -/
def Init (s : State N) : Prop :=
  (s.num = fun _ => (0 : Ticket N)) ∧ (s.flag = fun _ => false) ∧ (s.pc = fun _ => Phase.idle)

/-- TLA+ `LL(i, j)`: `i` takes precedence over `j` — the lexicographic ticket order. Ties cannot occur
(a ticket is taken strictly greater than every ticket held), so the `i ≤ j` half is defensive and is
kept because the module keeps it (`Bakery.tla:37-43`). -/
def LL (s : State N) (i j : Process N) : Prop :=
  s.num i < s.num j ∨ (s.num i = s.num j ∧ i ≤ j)

/-- TLA+ `SetFlag(i)`: an idle process enters the doorway, which raises its flag and blocks the others
until it has taken a ticket. -/
def SetFlag (i : Process N) (s t : State N) : Prop :=
  s.pc i = Phase.idle ∧
    t.flag = Function.update s.flag i true ∧
    t.pc = Function.update s.pc i Phase.doorway ∧
    t.num = s.num

/-- TLA+ `ChooseTicket(i)`: a process in the doorway takes a ticket strictly greater than every ticket
currently held — inside the bound `0 .. N`, which is why a process that would need a ticket above `N`
simply has no step here — lowers its flag and starts waiting. The existential's ticket is the only
place `ChooseTicket` differs from `SetFlag`: `flag` and `pc` are updated independently of it, exactly
as they sit outside the `\E` in the module's conjunction. -/
def ChooseTicket (i : Process N) (s t : State N) : Prop :=
  s.pc i = Phase.doorway ∧
    ∃ ticket : Ticket N,
      (∀ j : Process N, j ≠ i → s.num j < ticket) ∧
        t.num = Function.update s.num i ticket ∧
        t.flag = Function.update s.flag i false ∧
        t.pc = Function.update s.pc i Phase.wait

/-- TLA+ `Enter(i)`: a waiting process enters its critical section only when no process is in its
doorway and no process holds a ticket that takes precedence over its own — the guard the mutant
`BakeryMutant.lean` half-drops. -/
def Enter (i : Process N) (s t : State N) : Prop :=
  s.pc i = Phase.wait ∧
    (∀ j : Process N, j ≠ i → s.flag j = false ∧ (s.num j = (0 : Ticket N) ∨ LL s i j)) ∧
    t.pc = Function.update s.pc i Phase.crit ∧
    t.num = s.num ∧
    t.flag = s.flag

/-- TLA+ `Exit(i)`: the critical section is left, the ticket is given back (`num[i] = 0`) and the
process returns to idle. -/
def Exit (i : Process N) (s t : State N) : Prop :=
  s.pc i = Phase.crit ∧
    t.num = Function.update s.num i (0 : Ticket N) ∧
    t.pc = Function.update s.pc i Phase.idle ∧
    t.flag = s.flag

/-- TLA+ `Next == \E i \in P : SetFlag(i) \/ ChooseTicket(i) \/ Enter(i) \/ Exit(i)`. -/
def Next (s t : State N) : Prop :=
  ∃ i : Process N, SetFlag i s t ∨ ChooseTicket i s t ∨ Enter i s t ∨ Exit i s t

/-- TLA+ `[Next]_vars`: a step of `Next`, or a step that changes nothing. -/
def Step (s t : State N) : Prop := Next s t ∨ t = s

/-- The states admitted by TLA+ `Spec == Init /\ [][Next]_vars`, read as a state predicate — the
invariance reading of a safety property, which is what `MutualExclusion` is (protocol §11 decision 4).
The module's `ASSUME N >= 2` is carried by the theorem's first argument rather than here: unlike
token-ring's `Init`, this one names no distinguished process, so `Init` holds for every `N`. -/
inductive Reachable : State N → Prop where
  /-- The initial states. -/
  | init {s} : Init s → Reachable s
  /-- The states one `[Next]_vars` step away from a reachable state. -/
  | step {s t} : Reachable s → Step s t → Reachable t

/-- TLA+ `MutualExclusion == \A i, j \in P : (i # j) => ~(pc[i] = "crit" /\ pc[j] = "crit")`: no two
distinct processes are in their critical section at once. -/
def MutualExclusion (s : State N) : Prop :=
  ∀ i j : Process N, i ≠ j → ¬ (s.pc i = Phase.crit ∧ s.pc j = Phase.crit)

/-! ## The theorem -/

/-- **Mutual exclusion**, in general (tier 2, protocol §2): every state reachable under `Spec` has at
most one process in its critical section, at every `N` the module's assumption admits — the TLA+
`Spec => []MutualExclusion` under `ASSUME N >= 2` (`Bakery.tla:19`, `:85`). -/
theorem mutual_exclusion (hN : 2 ≤ N) (s : State N) (hs : Reachable s) : MutualExclusion s := by
  let Inv : State N → Prop := fun s =>
    MutualExclusion s ∧
    (∀ i : Process N, (s.pc i = Phase.wait ∨ s.pc i = Phase.crit) → s.num i ≠ (0 : Ticket N)) ∧
    (∀ i : Process N, (s.pc i = Phase.wait ∨ s.pc i = Phase.crit) → s.flag i = false) ∧
    (∀ i j : Process N, i ≠ j → s.pc i = Phase.crit → s.pc j = Phase.wait →
       s.num j ≠ (0 : Ticket N) ∧ LL s i j)
  have hInv : Inv s := by
    induction hs with
    | init =>
        rename_i s0 hInit
        constructor
        · intro i j hij hcrit
          rw [hInit.2.2] at hcrit
          cases hcrit.1
        · constructor
          · intro i hi
            have hpc := congrFun hInit.2.2 i
            rcases hi with h | h
            · rw [hpc] at h; cases h
            · rw [hpc] at h; cases h
          · constructor
            · intro i hi
              have hpc := congrFun hInit.2.2 i
              rcases hi with h | h
              · rw [hpc] at h; cases h
              · rw [hpc] at h; cases h
            · intro i j hij hci hwj
              have hpc := congrFun hInit.2.2 i
              rw [hpc] at hci
              cases hci
    | step =>
        rename_i sp tp hPrev hStep ih
        have hcard : 1 < Fintype.card (Process N) := by
          change 1 < Fintype.card (Fin N)
          rw [Fintype.card_fin]
          omega
        have hexists_ne : ∀ i : Process N, ∃ j : Process N, j ≠ i := by
          intro i
          exact Fintype.exists_ne_of_one_lt_card hcard i
        have ll_antisymm : ∀ (s : State N) (i j : Process N), i ≠ j → ¬ (LL s i j ∧ LL s j i) := by
          intro s i j hij h
          rcases h with ⟨hijLL, hjiLL⟩
          rcases hijLL with hlt | heq
          · rcases hjiLL with hlt' | heq'
            · exact lt_irrefl (s.num i) (lt_trans hlt hlt')
            · rw [heq'.1] at hlt
              exact lt_irrefl (s.num i) hlt
          · rcases hjiLL with hlt' | heq'
            · rw [heq.1] at hlt'
              exact lt_irrefl (s.num j) hlt'
            · have hleij : i ≤ j := heq.2
              have hleji : j ≤ i := heq'.2
              exact hij (le_antisymm hleij hleji)
        cases hStep with
        | inl hnext =>
            rcases ih with ⟨hME, hnz, hfl, hrel⟩
            rcases hnext with ⟨i, hact⟩
            rcases hact with hsf | hct | hen | hex
            · rcases hsf with ⟨hpi, htf, htpc, htn⟩
              constructor
              · intro j k hjk hcrit
                by_cases hji : j = i
                · subst j
                  rw [htpc] at hcrit
                  rw [Function.update_self] at hcrit
                  cases hcrit.1
                · by_cases hki : k = i
                  · subst k
                    rw [htpc] at hcrit
                    rw [Function.update_of_ne hji] at hcrit
                    rw [Function.update_self] at hcrit
                    cases hcrit.2
                  · rw [htpc] at hcrit
                    rw [Function.update_of_ne hji] at hcrit
                    rw [Function.update_of_ne hki] at hcrit
                    exact hME j k hjk hcrit
              · constructor
                · intro j hj
                  by_cases hji : j = i
                  · subst j
                    rw [htpc] at hj
                    rw [Function.update_self] at hj
                    rcases hj with h | h <;> cases h
                  · rw [htpc] at hj
                    rw [Function.update_of_ne hji] at hj
                    have hnj := hnz j hj
                    rw [htn]
                    exact hnj
                · constructor
                  · intro j hj
                    by_cases hji : j = i
                    · subst j
                      rw [htpc] at hj
                      rw [Function.update_self] at hj
                      rcases hj with h | h <;> cases h
                    · rw [htpc] at hj
                      rw [Function.update_of_ne hji] at hj
                      have hfj := hfl j hj
                      rw [htf]
                      rw [Function.update_of_ne hji]
                      exact hfj
                  · intro j k hjk hcj hwk
                    by_cases hji : j = i
                    · subst j
                      rw [htpc] at hcj
                      rw [Function.update_self] at hcj
                      cases hcj
                    · by_cases hki : k = i
                      · subst k
                        rw [htpc] at hwk
                        rw [Function.update_self] at hwk
                        cases hwk
                      · rw [htpc] at hcj
                        rw [Function.update_of_ne hji] at hcj
                        rw [htpc] at hwk
                        rw [Function.update_of_ne hki] at hwk
                        have hreljk := hrel j k hjk hcj hwk
                        constructor
                        · rw [htn]
                          exact hreljk.1
                        · change tp.num j < tp.num k ∨ (tp.num j = tp.num k ∧ j ≤ k)
                          rw [htn]
                          exact hreljk.2
            · rcases hct with ⟨hpi, ticket, hgt, htn, htf, htpc⟩
              have hticket_ne_zero : ticket ≠ 0 := by
                obtain ⟨j, hji⟩ := hexists_ne i
                have hlt : sp.num j < ticket := hgt j hji
                exact ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) hlt)
              constructor
              · intro j k hjk hcrit
                by_cases hji : j = i
                · subst j
                  rw [htpc] at hcrit
                  rw [Function.update_self] at hcrit
                  cases hcrit.1
                · by_cases hki : k = i
                  · subst k
                    rw [htpc] at hcrit
                    rw [Function.update_of_ne hji] at hcrit
                    rw [Function.update_self] at hcrit
                    cases hcrit.2
                  · rw [htpc] at hcrit
                    rw [Function.update_of_ne hji] at hcrit
                    rw [Function.update_of_ne hki] at hcrit
                    exact hME j k hjk hcrit
              · constructor
                · intro j hj
                  by_cases hji : j = i
                  · subst j
                    rw [htn]
                    rw [Function.update_self]
                    exact hticket_ne_zero
                  · rw [htpc] at hj
                    rw [Function.update_of_ne hji] at hj
                    have hnj := hnz j hj
                    rw [htn]
                    rw [Function.update_of_ne hji]
                    exact hnj
                · constructor
                  · intro j hj
                    by_cases hji : j = i
                    · subst j
                      rw [htf]
                      rw [Function.update_self]
                    · rw [htpc] at hj
                      rw [Function.update_of_ne hji] at hj
                      have hfj := hfl j hj
                      rw [htf]
                      rw [Function.update_of_ne hji]
                      exact hfj
                  · intro j k hjk hcj hwk
                    by_cases hji : j = i
                    · subst j
                      rw [htpc] at hcj
                      rw [Function.update_self] at hcj
                      cases hcj
                    · have hspcj : sp.pc j = Phase.crit := by
                        rw [htpc] at hcj
                        rw [Function.update_of_ne hji] at hcj
                        exact hcj
                      by_cases hki : k = i
                      · subst k
                        constructor
                        · rw [htn]
                          rw [Function.update_self]
                          exact hticket_ne_zero
                        · left
                          rw [htn]
                          rw [Function.update_of_ne hji]
                          rw [Function.update_self]
                          exact hgt j hji
                      · rw [htpc] at hwk
                        rw [Function.update_of_ne hki] at hwk
                        have hreljk := hrel j k hjk hspcj hwk
                        constructor
                        · rw [htn]
                          rw [Function.update_of_ne hki]
                          exact hreljk.1
                        · change tp.num j < tp.num k ∨ (tp.num j = tp.num k ∧ j ≤ k)
                          rw [htn]
                          rw [Function.update_of_ne hji]
                          rw [Function.update_of_ne hki]
                          exact hreljk.2
            · rcases hen with ⟨hpi, hguard, htpc, htn, htf⟩
              constructor
              · intro j k hjk hcrit
                by_cases hji : j = i
                · subst j
                  by_cases hki : k = i
                  · subst k
                    exact (hjk rfl).elim
                  · have hspck : sp.pc k = Phase.crit := by
                      rw [htpc] at hcrit
                      rw [Function.update_of_ne hki] at hcrit
                      exact hcrit.2
                    have hrel_ki := hrel k i hki hspck hpi
                    have hguard_k := hguard k hki
                    have hnzk : sp.num k ≠ 0 := hnz k (Or.inr hspck)
                    have hll_ik : LL sp i k := by
                      rcases hguard_k.2 with hz | hll
                      · exact False.elim (hnzk hz)
                      · exact hll
                    exact ll_antisymm sp k i hki ⟨hrel_ki.2, hll_ik⟩
                · by_cases hki : k = i
                  · subst k
                    have hspcj : sp.pc j = Phase.crit := by
                      rw [htpc] at hcrit
                      rw [Function.update_of_ne hji] at hcrit
                      exact hcrit.1
                    have hrel_ji := hrel j i hji hspcj hpi
                    have hguard_j := hguard j hji
                    have hnzj : sp.num j ≠ 0 := hnz j (Or.inr hspcj)
                    have hll_ij : LL sp i j := by
                      rcases hguard_j.2 with hz | hll
                      · exact False.elim (hnzj hz)
                      · exact hll
                    exact ll_antisymm sp j i hji ⟨hrel_ji.2, hll_ij⟩
                  · have hspcj : sp.pc j = Phase.crit := by
                      rw [htpc] at hcrit
                      rw [Function.update_of_ne hji] at hcrit
                      exact hcrit.1
                    have hspck : sp.pc k = Phase.crit := by
                      rw [htpc] at hcrit
                      rw [Function.update_of_ne hki] at hcrit
                      exact hcrit.2
                    exact hME j k hjk ⟨hspcj, hspck⟩
              · constructor
                · intro j hj
                  by_cases hji : j = i
                  · subst j
                    rw [htn]
                    exact hnz i (Or.inl hpi)
                  · have hspj : sp.pc j = Phase.wait ∨ sp.pc j = Phase.crit := by
                      rw [htpc] at hj
                      rw [Function.update_of_ne hji] at hj
                      exact hj
                    rw [htn]
                    exact hnz j hspj
                · constructor
                  · intro j hj
                    by_cases hji : j = i
                    · subst j
                      rw [htf]
                      exact hfl i (Or.inl hpi)
                    · have hspj : sp.pc j = Phase.wait ∨ sp.pc j = Phase.crit := by
                        rw [htpc] at hj
                        rw [Function.update_of_ne hji] at hj
                        exact hj
                      rw [htf]
                      exact hfl j hspj
                  · intro j k hjk hcj hwk
                    by_cases hji : j = i
                    · subst j
                      have hki : k ≠ i := by
                        intro h
                        exact hjk h.symm
                      have hspck : sp.pc k = Phase.wait := by
                        rw [htpc] at hwk
                        rw [Function.update_of_ne hki] at hwk
                        exact hwk
                      have hguard_k := hguard k hki
                      have hnzsp : sp.num k ≠ 0 := hnz k (Or.inl hspck)
                      have hll_ik : LL sp i k := by
                        rcases hguard_k.2 with hz | hll
                        · exact False.elim (hnzsp hz)
                        · exact hll
                      constructor
                      · rw [htn]
                        exact hnzsp
                      · change tp.num i < tp.num k ∨ (tp.num i = tp.num k ∧ i ≤ k)
                        rw [htn]
                        exact hll_ik
                    · have hspcj : sp.pc j = Phase.crit := by
                        rw [htpc] at hcj
                        rw [Function.update_of_ne hji] at hcj
                        exact hcj
                      by_cases hki : k = i
                      · subst k
                        rw [htpc] at hwk
                        rw [Function.update_self] at hwk
                        cases hwk
                      · have hspck : sp.pc k = Phase.wait := by
                          rw [htpc] at hwk
                          rw [Function.update_of_ne hki] at hwk
                          exact hwk
                        have hrel_jk := hrel j k hjk hspcj hspck
                        constructor
                        · rw [htn]
                          exact hrel_jk.1
                        · change tp.num j < tp.num k ∨ (tp.num j = tp.num k ∧ j ≤ k)
                          rw [htn]
                          exact hrel_jk.2
            · rcases hex with ⟨hpi, htn, htpc, htf⟩
              constructor
              · intro j k hjk hcrit
                by_cases hji : j = i
                · subst j
                  rw [htpc] at hcrit
                  rw [Function.update_self] at hcrit
                  cases hcrit.1
                · by_cases hki : k = i
                  · subst k
                    rw [htpc] at hcrit
                    rw [Function.update_of_ne hji] at hcrit
                    rw [Function.update_self] at hcrit
                    cases hcrit.2
                  · rw [htpc] at hcrit
                    rw [Function.update_of_ne hji] at hcrit
                    rw [Function.update_of_ne hki] at hcrit
                    exact hME j k hjk hcrit
              · constructor
                · intro j hj
                  by_cases hji : j = i
                  · subst j
                    rw [htpc] at hj
                    rw [Function.update_self] at hj
                    rcases hj with h | h <;> cases h
                  · rw [htpc] at hj
                    rw [Function.update_of_ne hji] at hj
                    have hnj := hnz j hj
                    rw [htn]
                    rw [Function.update_of_ne hji]
                    exact hnj
                · constructor
                  · intro j hj
                    by_cases hji : j = i
                    · subst j
                      rw [htpc] at hj
                      rw [Function.update_self] at hj
                      rcases hj with h | h <;> cases h
                    · rw [htpc] at hj
                      rw [Function.update_of_ne hji] at hj
                      have hfj := hfl j hj
                      rw [htf]
                      exact hfj
                  · intro j k hjk hcj hwk
                    by_cases hji : j = i
                    · subst j
                      rw [htpc] at hcj
                      rw [Function.update_self] at hcj
                      cases hcj
                    · by_cases hki : k = i
                      · subst k
                        rw [htpc] at hwk
                        rw [Function.update_self] at hwk
                        cases hwk
                      · rw [htpc] at hcj
                        rw [Function.update_of_ne hji] at hcj
                        rw [htpc] at hwk
                        rw [Function.update_of_ne hki] at hwk
                        have hreljk := hrel j k hjk hcj hwk
                        constructor
                        · rw [htn]
                          rw [Function.update_of_ne hki]
                          exact hreljk.1
                        · change tp.num j < tp.num k ∨ (tp.num j = tp.num k ∧ j ≤ k)
                          rw [htn]
                          rw [Function.update_of_ne hji]
                          rw [Function.update_of_ne hki]
                          exact hreljk.2
        | inr hEq =>
            subst tp
            exact ih
  exact hInv.1

end Bakery
