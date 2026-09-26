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
      (∀ i j : Process N, s.pc i = Phase.crit → s.pc j = Phase.wait → ¬ LL s j i) ∧
      (∀ i : Process N, s.pc i = Phase.wait ∨ s.pc i = Phase.crit → s.num i ≠ 0)
  have hll_antisym : ∀ (s : State N) (a b : Process N), a ≠ b → LL s a b → ¬ LL s b a := by
    intro s a b hab h
    rcases h with hlt | heq
    · intro h'
      rcases h' with hlt' | heq'
      · exact lt_asymm hlt hlt'
      · rcases heq' with ⟨hEq, _⟩
        simp [hEq] at hlt
    · rcases heq with ⟨hEq, hle⟩
      intro h'
      rcases h' with hlt' | heq'
      · simp [hEq] at hlt' 
      · rcases heq' with ⟨_, hle'⟩
        exact hab (le_antisymm hle hle')
  have hstep_setFlag : ∀ (i : Process N) (s t : State N), Inv s → SetFlag i s t → Inv t := by
    intro i s t ih hsf
    rcases hsf with ⟨hpc_s, hflag_t, hpc_t, hnum_t⟩
    have hpc_t_i : t.pc i = Phase.doorway := by simp [Function.update, hpc_t]
    refine ⟨?_, ?_, ?_⟩
    · -- MutualExclusion t
      intro x y hxy hcrit
      rcases hcrit with ⟨hx, hy⟩
      by_cases hxi : x = i
      · subst x
        rw [hpc_t_i] at hx
        cases hx
      · have hxs_crit : s.pc x = Phase.crit := by simpa [Function.update, hxi, hpc_t] using hx
        by_cases hyi : y = i
        · subst y
          rw [hpc_t_i] at hy
          cases hy
        · have hys_crit : s.pc y = Phase.crit := by simpa [Function.update, hyi, hpc_t] using hy
          exact ih.1 x y hxy ⟨hxs_crit, hys_crit⟩
    · -- I2
      intro a b ha hb
      have hai : a ≠ i := by
        intro hai
        subst a
        rw [hpc_t_i] at ha
        cases ha
      have hbi : b ≠ i := by
        intro hbi
        subst b
        rw [hpc_t_i] at hb
        cases hb
      have ha_crit_s : s.pc a = Phase.crit := by simpa [Function.update, hai, hpc_t] using ha
      have hb_wait_s : s.pc b = Phase.wait := by simpa [Function.update, hbi, hpc_t] using hb
      have hLL_false : ¬ LL s b a := ih.2.1 a b ha_crit_s hb_wait_s
      intro h
      exact hLL_false (by simpa [LL, hnum_t] using h)
    · -- I3
      intro a ha
      by_cases hai : a = i
      · subst a
        rcases ha with hw | hc
        · rw [hpc_t_i] at hw
          cases hw
        · rw [hpc_t_i] at hc
          cases hc
      · have hs_a : s.pc a = Phase.wait ∨ s.pc a = Phase.crit := by
          rcases ha with hw | hc
          · left
            simpa [Function.update, hai, hpc_t] using hw
          · right
            simpa [Function.update, hai, hpc_t] using hc
        have hnum_a_ne : s.num a ≠ 0 := ih.2.2 a hs_a
        simpa [LL, hnum_t] using hnum_a_ne
  have hstep_choose : ∀ (i : Process N) (s t : State N), Inv s → ChooseTicket i s t → Inv t := by
    intro i s t ih hct
    rcases hct with ⟨hpc_s, ticket, hgt, hnum_t, hflag_t, hpc_t⟩
    have hpc_t_i : t.pc i = Phase.wait := by simp [Function.update, hpc_t]
    have hcard : 1 < Fintype.card (Process N) := by
      rw [Fintype.card_fin]
      exact Nat.lt_of_lt_of_le (by norm_num) hN
    obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hcard i
    have hpos_ticket : 0 < ticket := lt_of_le_of_lt (Fin.zero_le (s.num j)) (hgt j hji)
    have hne_ticket : ticket ≠ 0 := ne_of_gt hpos_ticket
    refine ⟨?_, ?_, ?_⟩
    · -- MutualExclusion t
      intro x y hxy hcrit
      rcases hcrit with ⟨hx, hy⟩
      by_cases hxi : x = i
      · subst x
        rw [hpc_t_i] at hx
        cases hx
      · have hxs_crit : s.pc x = Phase.crit := by simpa [Function.update, hxi, hpc_t] using hx
        by_cases hyi : y = i
        · subst y
          rw [hpc_t_i] at hy
          cases hy
        · have hys_crit : s.pc y = Phase.crit := by simpa [Function.update, hyi, hpc_t] using hy
          exact ih.1 x y hxy ⟨hxs_crit, hys_crit⟩
    · -- I2
      intro a b ha hb
      have hai : a ≠ i := by
        intro hai
        subst a
        rw [hpc_t_i] at ha
        cases ha
      have ha_crit_s : s.pc a = Phase.crit := by simpa [Function.update, hai, hpc_t] using ha
      have htnum_a : t.num a = s.num a := by simp [Function.update, hai, hnum_t]
      have htnum_i : t.num i = ticket := by simp [Function.update, hnum_t]
      by_cases hbi : b = i
      · subst b
        have hlt : t.num a < t.num i := by simpa [htnum_a, htnum_i] using (hgt a hai)
        intro h
        rcases h with hlt_i | heq
        · exact lt_asymm hlt_i hlt
        · rcases heq with ⟨hEq, _⟩
          exact (ne_of_gt hlt) hEq
      · have hb_wait_s : s.pc b = Phase.wait := by simpa [Function.update, hbi, hpc_t] using hb
        have htnum_b : t.num b = s.num b := by simp [Function.update, hbi, hnum_t]
        have hLL_false : ¬ LL s b a := ih.2.1 a b ha_crit_s hb_wait_s
        intro h
        exact hLL_false (by simpa [LL, htnum_a, htnum_b] using h)
    · -- I3
      intro a ha
      by_cases hai : a = i
      · subst a
        have htnum_i : t.num i = ticket := by simp [Function.update, hnum_t]
        rw [htnum_i]
        exact hne_ticket
      · have hs_a : s.pc a = Phase.wait ∨ s.pc a = Phase.crit := by
          rcases ha with hw | hc
          · left
            simpa [Function.update, hai, hpc_t] using hw
          · right
            simpa [Function.update, hai, hpc_t] using hc
        have hnum_a_ne : s.num a ≠ 0 := ih.2.2 a hs_a
        have htnum_a : t.num a = s.num a := by simp [Function.update, hai, hnum_t]
        simpa [htnum_a] using hnum_a_ne
  have hstep_enter : ∀ (i : Process N) (s t : State N), Inv s → Enter i s t → Inv t := by
    intro i s t ih hen
    rcases hen with ⟨hpc_s, hguard, hpc_t, hnum_t, hflag_t⟩
    have hpc_t_i : t.pc i = Phase.crit := by simp [Function.update, hpc_t]
    refine ⟨?_, ?_, ?_⟩
    · -- MutualExclusion t
      intro x y hxy hcrit
      rcases hcrit with ⟨hx, hy⟩
      by_cases hxi : x = i
      · subst x
        have hyi : y ≠ i := by
          intro hyi
          subst y
          exact hxy rfl
        have hys_crit : s.pc y = Phase.crit := by simpa [Function.update, hyi, hpc_t] using hy
        have hnum_y_ne : s.num y ≠ 0 := ih.2.2 y (Or.inr hys_crit)
        rcases (hguard y hyi) with ⟨_, hnum_or⟩
        rcases hnum_or with hy0 | hLL_siy
        · exact hnum_y_ne hy0
        · exact (ih.2.1 y i hys_crit hpc_s) hLL_siy
      · have hxs_crit : s.pc x = Phase.crit := by simpa [Function.update, hxi, hpc_t] using hx
        by_cases hyi : y = i
        · subst y
          have hnum_x_ne : s.num x ≠ 0 := ih.2.2 x (Or.inr hxs_crit)
          rcases (hguard x hxi) with ⟨_, hnum_or⟩
          rcases hnum_or with hx0 | hLL_six
          · exact hnum_x_ne hx0
          · exact (ih.2.1 x i hxs_crit hpc_s) hLL_six
        · have hys_crit : s.pc y = Phase.crit := by simpa [Function.update, hyi, hpc_t] using hy
          exact ih.1 x y hxy ⟨hxs_crit, hys_crit⟩
    · -- I2
      intro a b ha hb
      have hbi : b ≠ i := by
        intro hbi
        subst b
        rw [hpc_t_i] at hb
        cases hb
      have hb_wait_s : s.pc b = Phase.wait := by simpa [Function.update, hbi, hpc_t] using hb
      by_cases hai : a = i
      · subst a
        have hnum_b_ne : s.num b ≠ 0 := ih.2.2 b (Or.inl hb_wait_s)
        rcases (hguard b hbi) with ⟨_, hnum_or⟩
        rcases hnum_or with hb0 | hLL_sib
        · exfalso
          exact hnum_b_ne hb0
        · have hLL_false : ¬ LL s b i := hll_antisym s i b hbi.symm hLL_sib
          intro h
          exact hLL_false (by simpa [LL, hnum_t] using h)
      · have ha_crit_s : s.pc a = Phase.crit := by simpa [Function.update, hai, hpc_t] using ha
        have hLL_false : ¬ LL s b a := ih.2.1 a b ha_crit_s hb_wait_s
        intro h
        exact hLL_false (by simpa [LL, hnum_t] using h)
    · -- I3
      intro a ha
      by_cases hai : a = i
      · subst a
        have hnum_i_ne : s.num i ≠ 0 := ih.2.2 i (Or.inl hpc_s)
        simpa [LL, hnum_t] using hnum_i_ne
      · have hs_a : s.pc a = Phase.wait ∨ s.pc a = Phase.crit := by
          rcases ha with hw | hc
          · left
            simpa [Function.update, hai, hpc_t] using hw
          · right
            simpa [Function.update, hai, hpc_t] using hc
        have hnum_a_ne : s.num a ≠ 0 := ih.2.2 a hs_a
        simpa [LL, hnum_t] using hnum_a_ne
  have hstep_exit : ∀ (i : Process N) (s t : State N), Inv s → Exit i s t → Inv t := by
    intro i s t ih hex
    rcases hex with ⟨hpc_s, hnum_t, hpc_t, hflag_t⟩
    have hpc_t_i : t.pc i = Phase.idle := by simp [Function.update, hpc_t]
    refine ⟨?_, ?_, ?_⟩
    · -- MutualExclusion t
      intro x y hxy hcrit
      rcases hcrit with ⟨hx, hy⟩
      by_cases hxi : x = i
      · subst x
        rw [hpc_t_i] at hx
        cases hx
      · have hxs_crit : s.pc x = Phase.crit := by simpa [Function.update, hxi, hpc_t] using hx
        by_cases hyi : y = i
        · subst y
          rw [hpc_t_i] at hy
          cases hy
        · have hys_crit : s.pc y = Phase.crit := by simpa [Function.update, hyi, hpc_t] using hy
          exact ih.1 x y hxy ⟨hxs_crit, hys_crit⟩
    · -- I2
      intro a b ha hb
      have hai : a ≠ i := by
        intro hai
        subst a
        rw [hpc_t_i] at ha
        cases ha
      have hbi : b ≠ i := by
        intro hbi
        subst b
        rw [hpc_t_i] at hb
        cases hb
      have ha_crit_s : s.pc a = Phase.crit := by simpa [Function.update, hai, hpc_t] using ha
      have hb_wait_s : s.pc b = Phase.wait := by simpa [Function.update, hbi, hpc_t] using hb
      have htnum_a : t.num a = s.num a := by simp [Function.update, hai, hnum_t]
      have htnum_b : t.num b = s.num b := by simp [Function.update, hbi, hnum_t]
      have hLL_false : ¬ LL s b a := ih.2.1 a b ha_crit_s hb_wait_s
      intro h
      exact hLL_false (by simpa [LL, htnum_a, htnum_b] using h)
    · -- I3
      intro a ha
      by_cases hai : a = i
      · subst a
        rcases ha with hw | hc
        · rw [hpc_t_i] at hw
          cases hw
        · rw [hpc_t_i] at hc
          cases hc
      · have hs_a : s.pc a = Phase.wait ∨ s.pc a = Phase.crit := by
          rcases ha with hw | hc
          · left
            simpa [Function.update, hai, hpc_t] using hw
          · right
            simpa [Function.update, hai, hpc_t] using hc
        have hnum_a_ne : s.num a ≠ 0 := ih.2.2 a hs_a
        have htnum_a : t.num a = s.num a := by simp [Function.update, hai, hnum_t]
        simpa [htnum_a] using hnum_a_ne
  have hInv : ∀ s : State N, Reachable s → Inv s := by
    intro s hs
    induction hs with
    | init =>
      rename_i s' hinit
      rcases hinit with ⟨hnum, hflag, hpc⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i j hij hcrit
        rcases hcrit with ⟨hi, hj⟩
        have hpc_i : s'.pc i = Phase.idle := by simp [hpc]
        rw [hpc_i] at hi
        cases hi
      · intro i j hic hjw
        have hpc_i : s'.pc i = Phase.idle := by simp [hpc]
        rw [hpc_i] at hic
        cases hic
      · intro i hi
        have hpc_i : s'.pc i = Phase.idle := by simp [hpc]
        rcases hi with hw | hc
        · rw [hpc_i] at hw
          cases hw
        · rw [hpc_i] at hc
          cases hc
    | step =>
      rename_i s' t' hs' hstep ih
      rcases hstep with hnext | rfl
      · rcases hnext with ⟨i, hnext⟩
        rcases hnext with hsf | hct | hen | hex
        · exact hstep_setFlag i s' t' ih hsf
        · exact hstep_choose i s' t' ih hct
        · exact hstep_enter i s' t' ih hen
        · exact hstep_exit i s' t' ih hex
      · exact ih
  exact (hInv s hs).1


end Bakery
