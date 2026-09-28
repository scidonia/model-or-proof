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
    (∀ i : Process N, s.pc i = Phase.crit → s.num i ≠ 0) ∧
      (∀ i : Process N, s.pc i = Phase.wait → s.num i ≠ 0) ∧
        ∀ i j : Process N, i ≠ j → s.pc i = Phase.crit → s.num j ≠ 0 → LL s i j
  have not_i_of_update :
      ∀ (i : Process N) (ph p : Phase), ph ≠ p → ∀ (s t : State N),
        t.pc = Function.update s.pc i ph → ∀ a : Process N, t.pc a = p → a ≠ i := by
    intro i ph p hph s t htpc a ha hai
    subst a
    rw [htpc] at ha
    rw [Function.update_self] at ha
    exact (hph ha).elim
  have pc_of_update_ne :
      ∀ (i : Process N) (ph p : Phase) (s t : State N),
        t.pc = Function.update s.pc i ph → ∀ a : Process N, a ≠ i → t.pc a = p → s.pc a = p := by
    intro i ph p s t htpc a hai ha
    rw [htpc] at ha
    rw [Function.update_of_ne hai] at ha
    exact ha
  have hInv : ∀ s : State N, Reachable s → Inv s := by
    intro s hs
    induction hs with
    | init =>
        rename_i s hinit
        rcases hinit with ⟨hnum, hflag, hpc⟩
        constructor
        · intro i hci
          have hi : s.pc i = Phase.idle := by simp [hpc]
          rw [hci] at hi
          cases hi
        · constructor
          · intro i hwi
            have hi : s.pc i = Phase.idle := by simp [hpc]
            rw [hwi] at hi
            cases hi
          · intro i j hij hci hnj
            have hi : s.pc i = Phase.idle := by simp [hpc]
            rw [hci] at hi
            cases hi
    | step =>
        rename_i s t hs hst ih
        rcases ih with ⟨hcritNonzero, hwaitNonzero, hmin⟩
        rcases hst with hnext | rfl
        · rcases hnext with ⟨i, hstep⟩
          rcases hstep with hset | hch | hen | hex
          · -- SetFlag i s t
            rcases hset with ⟨hidi, htflag, htpc, htnum⟩
            constructor
            · intro a ha
              have hai : a ≠ i := not_i_of_update i Phase.doorway Phase.crit (by decide) s t htpc a ha
              have hcrit_s : s.pc a = Phase.crit := pc_of_update_ne i Phase.doorway Phase.crit s t htpc a hai ha
              rw [htnum]
              exact hcritNonzero a hcrit_s
            · constructor
              · intro a hwa
                have hai : a ≠ i := not_i_of_update i Phase.doorway Phase.wait (by decide) s t htpc a hwa
                have hwait_s : s.pc a = Phase.wait := pc_of_update_ne i Phase.doorway Phase.wait s t htpc a hai hwa
                rw [htnum]
                exact hwaitNonzero a hwait_s
              · intro a b hab ha hnb
                have hai : a ≠ i := not_i_of_update i Phase.doorway Phase.crit (by decide) s t htpc a ha
                have hcrit_s : s.pc a = Phase.crit := pc_of_update_ne i Phase.doorway Phase.crit s t htpc a hai ha
                have hnb' : s.num b ≠ 0 := by
                  rwa [htnum] at hnb
                have hll := hmin a b hab hcrit_s hnb'
                simpa [LL, htnum] using hll
          · -- ChooseTicket i s t
            rcases hch with ⟨hidi, hticket⟩
            rcases hticket with ⟨ticket, hguard, htnum, htflag, htpc⟩
            have hticket_ne : ticket ≠ 0 := by
              intro h0
              have h1N : 1 < N := by omega
              obtain ⟨j, hji⟩ :=
                Fintype.exists_ne_of_one_lt_card (by simpa [Fintype.card_fin] using h1N) i
              have hlt := hguard j hji
              rw [h0] at hlt
              exact (not_lt_of_ge (Fin.zero_le (s.num j))) hlt
            constructor
            · intro a ha
              have hai : a ≠ i := not_i_of_update i Phase.wait Phase.crit (by decide) s t htpc a ha
              have hcrit_s : s.pc a = Phase.crit := pc_of_update_ne i Phase.wait Phase.crit s t htpc a hai ha
              rw [htnum, Function.update_of_ne hai]
              exact hcritNonzero a hcrit_s
            · constructor
              · intro a hwa
                by_cases hai : a = i
                · subst a
                  rw [htnum, Function.update_self]
                  exact hticket_ne
                · have hwait_s : s.pc a = Phase.wait := pc_of_update_ne i Phase.wait Phase.wait s t htpc a hai hwa
                  rw [htnum, Function.update_of_ne hai]
                  exact hwaitNonzero a hwait_s
              · intro a b hab ha hnb
                have hai : a ≠ i := not_i_of_update i Phase.wait Phase.crit (by decide) s t htpc a ha
                have hcrit_s : s.pc a = Phase.crit := pc_of_update_ne i Phase.wait Phase.crit s t htpc a hai ha
                unfold LL
                rw [htnum]
                by_cases hbi : b = i
                · subst b
                  rw [Function.update_self, Function.update_of_ne hai]
                  left
                  exact hguard a hai
                · rw [Function.update_of_ne hbi, Function.update_of_ne hai]
                  have hnb' : s.num b ≠ 0 := by
                    rwa [htnum, Function.update_of_ne hbi] at hnb
                  exact hmin a b hab hcrit_s hnb'
          · -- Enter i s t
            rcases hen with ⟨hwait_i, hguard, htpc, htnum, htflag⟩
            constructor
            · intro a ha
              by_cases hai : a = i
              · subst a
                rw [htnum]
                exact hwaitNonzero i hwait_i
              · have hcrit_s : s.pc a = Phase.crit := pc_of_update_ne i Phase.crit Phase.crit s t htpc a hai ha
                rw [htnum]
                exact hcritNonzero a hcrit_s
            · constructor
              · intro a hwa
                have hai : a ≠ i := not_i_of_update i Phase.crit Phase.wait (by decide) s t htpc a hwa
                have hwait_s : s.pc a = Phase.wait := pc_of_update_ne i Phase.crit Phase.wait s t htpc a hai hwa
                rw [htnum]
                exact hwaitNonzero a hwait_s
              · intro a b hab ha hnb
                by_cases hai : a = i
                · subst a
                  have hbi : b ≠ i := hab.symm
                  have hnb' : s.num b ≠ 0 := by
                    rwa [htnum] at hnb
                  rcases hguard b hbi with ⟨hflag_b, hnum_or_ll⟩
                  rcases hnum_or_ll with hnum0 | hll
                  · exact False.elim (hnb' hnum0)
                  · simpa [LL, htnum] using hll
                · have hcrit_s : s.pc a = Phase.crit := pc_of_update_ne i Phase.crit Phase.crit s t htpc a hai ha
                  have hnb' : s.num b ≠ 0 := by
                    rwa [htnum] at hnb
                  have hll := hmin a b hab hcrit_s hnb'
                  simpa [LL, htnum] using hll
          · -- Exit i s t
            rcases hex with ⟨hcrit_i, htnum, htpc, htflag⟩
            constructor
            · intro a ha
              have hai : a ≠ i := not_i_of_update i Phase.idle Phase.crit (by decide) s t htpc a ha
              have hcrit_s : s.pc a = Phase.crit := pc_of_update_ne i Phase.idle Phase.crit s t htpc a hai ha
              rw [htnum, Function.update_of_ne hai]
              exact hcritNonzero a hcrit_s
            · constructor
              · intro a hwa
                have hai : a ≠ i := not_i_of_update i Phase.idle Phase.wait (by decide) s t htpc a hwa
                have hwait_s : s.pc a = Phase.wait := pc_of_update_ne i Phase.idle Phase.wait s t htpc a hai hwa
                rw [htnum, Function.update_of_ne hai]
                exact hwaitNonzero a hwait_s
              · intro a b hab ha hnb
                have hai : a ≠ i := not_i_of_update i Phase.idle Phase.crit (by decide) s t htpc a ha
                have hcrit_s : s.pc a = Phase.crit := pc_of_update_ne i Phase.idle Phase.crit s t htpc a hai ha
                unfold LL
                rw [htnum]
                by_cases hbi : b = i
                · subst b
                  rw [Function.update_self, Function.update_of_ne hai]
                  rw [htnum, Function.update_self] at hnb
                  exact False.elim (hnb rfl)
                · rw [Function.update_of_ne hbi, Function.update_of_ne hai]
                  have hnb' : s.num b ≠ 0 := by
                    rwa [htnum, Function.update_of_ne hbi] at hnb
                  exact hmin a b hab hcrit_s hnb'
        · exact ⟨hcritNonzero, hwaitNonzero, hmin⟩
  have hme : ∀ s : State N, Inv s → MutualExclusion s := by
    intro s hinv
    rcases hinv with ⟨hcritNonzero, hwaitNonzero, hmin⟩
    intro i j hij hcritpair
    rcases hcritpair with ⟨hci, hcj⟩
    have hni : s.num i ≠ 0 := hcritNonzero i hci
    have hnj : s.num j ≠ 0 := hcritNonzero j hcj
    have hllij := hmin i j hij hci hnj
    have hllji := hmin j i hij.symm hcj hni
    unfold LL at hllij hllji
    rcases hllij with hijlt | hijeq
    · rcases hllji with hjilt | hjieq
      · exact (lt_asymm hijlt) hjilt
      · rw [hjieq.1] at hijlt
        exact lt_irrefl _ hijlt
    · rcases hllji with hjilt | hjieq
      · rw [hijeq.1] at hjilt
        exact lt_irrefl _ hjilt
      · have : i = j := Fin.le_antisymm hijeq.2 hjieq.2
        exact hij this
  exact hme s (hInv s hs)

end Bakery
