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
  have num_iff : ∀ (s : State N), Reachable s → ∀ i : Process N,
      (s.num i = (0 : Ticket N)) ↔ (s.pc i = Phase.idle ∨ s.pc i = Phase.doorway) := by
    intro s hs
    induction hs with
    | init =>
      rename_i hinit
      intro i
      rcases hinit with ⟨hn, hf, hp⟩
      simp [hn, hp]
    | step =>
      rename_i s' t' hs' hst' ih
      rcases hst' with hnext | rfl
      · rcases hnext with ⟨i, hstep⟩
        rcases hstep with hsf | hct | hent | hex
        · rcases hsf with ⟨hpc_i, hflag, hpc, hnum⟩
          intro j
          by_cases hji : j = i
          · subst j
            simp [hnum, hpc, Function.update_self, ih i, hpc_i]
          · simp [hnum, hpc, Function.update_of_ne, hji, ih j]
        · rcases hct with ⟨hdoor, ticket, hgt, hnum, hflag, hpc⟩
          intro j
          by_cases hji : j = i
          · subst j
            have hcard : 1 < Fintype.card (Process N) := by
              change 1 < Fintype.card (Fin N)
              rw [Fintype.card_fin]
              exact hN
            obtain ⟨k, hki⟩ := Fintype.exists_ne_of_one_lt_card hcard i
            have ht_ne : ticket ≠ (0 : Ticket N) := by
              intro ht0
              have hlt0 : s'.num k < (0 : Ticket N) := by
                simpa [ht0] using hgt k hki
              exact Fin.not_lt_zero (s'.num k) hlt0
            simp [hnum, hpc, Function.update_self, ht_ne]
          · simp [hnum, hpc, Function.update_of_ne, hji, ih j]
        · rcases hent with ⟨hwait, hguard, hpc, hnum, hflag⟩
          intro j
          by_cases hji : j = i
          · subst j
            simp [hnum, hpc, Function.update_self, ih i, hwait]
          · simp [hnum, hpc, Function.update_of_ne, hji, ih j]
        · rcases hex with ⟨hcrit, hnum, hpc, hflag⟩
          intro j
          by_cases hji : j = i
          · subst j
            simp [hnum, hpc, Function.update_self]
          · simp [hnum, hpc, Function.update_of_ne, hji, ih j]
      · exact ih
  have distinct_tickets : ∀ (s : State N), Reachable s → ∀ i j : Process N, i ≠ j →
      (s.pc i = Phase.wait ∨ s.pc i = Phase.crit) →
      (s.pc j = Phase.wait ∨ s.pc j = Phase.crit) →
      s.num i ≠ s.num j := by
    intro s hs
    induction hs with
    | init =>
      rename_i hinit
      intro i j hij hi hj
      rcases hinit with ⟨hn, hf, hp⟩
      rw [hp] at hi hj
      rcases hi with h | h <;> cases h
    | step =>
      rename_i s' t' hs' hst' ih
      rcases hst' with hnext | rfl
      · rcases hnext with ⟨a, hstep⟩
        rcases hstep with hsf | hct | hent | hex
        · rcases hsf with ⟨hpc_a, hflag, hpc, hnum⟩
          intro i j hij hti htj
          have hia : i ≠ a := by
            intro hia
            subst i
            rw [hpc, Function.update_self] at hti
            rcases hti with h | h <;> cases h
          have hja : j ≠ a := by
            intro hja
            subst j
            rw [hpc, Function.update_self] at htj
            rcases htj with h | h <;> cases h
          have hti' : s'.pc i = Phase.wait ∨ s'.pc i = Phase.crit := by
            simpa [hpc, Function.update_of_ne, hia] using hti
          have htj' : s'.pc j = Phase.wait ∨ s'.pc j = Phase.crit := by
            simpa [hpc, Function.update_of_ne, hja] using htj
          have hne := ih i j hij hti' htj'
          rw [hnum]
          exact hne
        · rcases hct with ⟨hdoor, ticket, hgt, hnum, hflag, hpc⟩
          intro i j hij hti htj
          by_cases hia : i = a
          · subst i
            by_cases hja : j = a
            · subst j
              exact (hij rfl).elim
            · have hlt : s'.num j < ticket := hgt j hja
              simpa [hnum, Function.update_self, Function.update_of_ne, hja] using hlt.ne'
          · by_cases hja : j = a
            · subst j
              have hlt : s'.num i < ticket := hgt i hia
              simpa [hnum, Function.update_self, Function.update_of_ne, hia] using hlt.ne
            · have hti' : s'.pc i = Phase.wait ∨ s'.pc i = Phase.crit := by
                simpa [hpc, Function.update_of_ne, hia] using hti
              have htj' : s'.pc j = Phase.wait ∨ s'.pc j = Phase.crit := by
                simpa [hpc, Function.update_of_ne, hja] using htj
              have hne := ih i j hij hti' htj'
              rw [hnum]
              simp [Function.update_of_ne, hia, hja]
              exact hne
        · rcases hent with ⟨hwait, hguard, hpc, hnum, hflag⟩
          intro i j hij hti htj
          have hti' : s'.pc i = Phase.wait ∨ s'.pc i = Phase.crit := by
            by_cases hia : i = a
            · subst i
              left
              exact hwait
            · simpa [hpc, Function.update_of_ne, hia] using hti
          have htj' : s'.pc j = Phase.wait ∨ s'.pc j = Phase.crit := by
            by_cases hja : j = a
            · subst j
              left
              exact hwait
            · simpa [hpc, Function.update_of_ne, hja] using htj
          have hne := ih i j hij hti' htj'
          rw [hnum]
          exact hne
        · rcases hex with ⟨hcrit, hnum, hpc, hflag⟩
          intro i j hij hti htj
          have hia : i ≠ a := by
            intro hia
            subst i
            rw [hpc, Function.update_self] at hti
            rcases hti with h | h <;> cases h
          have hja : j ≠ a := by
            intro hja
            subst j
            rw [hpc, Function.update_self] at htj
            rcases htj with h | h <;> cases h
          have hti' : s'.pc i = Phase.wait ∨ s'.pc i = Phase.crit := by
            simpa [hpc, Function.update_of_ne, hia] using hti
          have htj' : s'.pc j = Phase.wait ∨ s'.pc j = Phase.crit := by
            simpa [hpc, Function.update_of_ne, hja] using htj
          have hne := ih i j hij hti' htj'
          rw [hnum]
          simp [Function.update_of_ne, hia, hja]
          exact hne
      · exact ih
  have crit_lt_wait : ∀ (s : State N), Reachable s → ∀ i j : Process N, i ≠ j →
      s.pc i = Phase.crit → s.pc j = Phase.wait → s.num i < s.num j := by
    intro s hs
    induction hs with
    | init =>
      rename_i hinit
      intro i j hij hci hwj
      rcases hinit with ⟨hn, hf, hp⟩
      rw [hp] at hci
      cases hci
    | step =>
      rename_i s' t' hs' hst' ih
      rcases hst' with hnext | rfl
      · rcases hnext with ⟨a, hstep⟩
        rcases hstep with hsf | hct | hent | hex
        · rcases hsf with ⟨hpc_a, hflag, hpc, hnum⟩
          intro i j hij hti htj
          have hia : i ≠ a := by
            intro hia; subst i; rw [hpc, Function.update_self] at hti; cases hti
          have hja : j ≠ a := by
            intro hja; subst j; rw [hpc, Function.update_self] at htj; cases htj
          have hci : s'.pc i = Phase.crit := by simpa [hpc, Function.update_of_ne, hia] using hti
          have hwj : s'.pc j = Phase.wait := by simpa [hpc, Function.update_of_ne, hja] using htj
          have hlt := ih i j hij hci hwj
          rw [hnum]
          exact hlt
        · rcases hct with ⟨hdoor, ticket, hgt, hnum, hflag, hpc⟩
          intro i j hij hti htj
          have hia : i ≠ a := by
            intro hia; subst i; rw [hpc, Function.update_self] at hti; cases hti
          by_cases hja : j = a
          · subst j
            have hci : s'.pc i = Phase.crit := by simpa [hpc, Function.update_of_ne, hia] using hti
            have hlt : s'.num i < ticket := hgt i hia
            simpa [hnum, Function.update_self, Function.update_of_ne, hia] using hlt
          · have hci : s'.pc i = Phase.crit := by simpa [hpc, Function.update_of_ne, hia] using hti
            have hwj : s'.pc j = Phase.wait := by simpa [hpc, Function.update_of_ne, hja] using htj
            have hlt := ih i j hij hci hwj
            rw [hnum]
            simp [Function.update_of_ne, hia, hja]
            exact hlt
        · rcases hent with ⟨hwait, hguard, hpc, hnum, hflag⟩
          intro i j hij hti htj
          by_cases hia : i = a
          · subst i
            have hja : j ≠ a := hij.symm
            have hwj : s'.pc j = Phase.wait := by simpa [hpc, Function.update_of_ne, hja] using htj
            rcases hguard j hja with ⟨hflagj, hor⟩
            have hnumj_ne : s'.num j ≠ (0 : Ticket N) := by
              intro h0
              have hnot : ¬ (s'.pc j = Phase.idle ∨ s'.pc j = Phase.doorway) := by
                intro h
                rcases h with h | h
                · rw [hwj] at h; cases h
                · rw [hwj] at h; cases h
              exact hnot ((num_iff s' hs' j).mp h0)
            have hLL : LL s' a j := by
              rcases hor with h0 | hll
              · exact False.elim (hnumj_ne h0)
              · exact hll
            have hstrict : s'.num a < s'.num j := by
              rcases hLL with hlt | heq
              · exact hlt
              · rcases heq with ⟨heq', hle⟩
                exact False.elim ((distinct_tickets s' hs' a j hja.symm (by left; exact hwait) (by left; exact hwj)) heq')
            rw [hnum]
            exact hstrict
          · have hja : j ≠ a := by
              intro hja; subst j; rw [hpc, Function.update_self] at htj; cases htj
            have hci : s'.pc i = Phase.crit := by simpa [hpc, Function.update_of_ne, hia] using hti
            have hwj : s'.pc j = Phase.wait := by simpa [hpc, Function.update_of_ne, hja] using htj
            have hlt := ih i j hij hci hwj
            rw [hnum]
            exact hlt
        · rcases hex with ⟨hcrit, hnum, hpc, hflag⟩
          intro i j hij hti htj
          have hia : i ≠ a := by
            intro hia; subst i; rw [hpc, Function.update_self] at hti; cases hti
          have hja : j ≠ a := by
            intro hja; subst j; rw [hpc, Function.update_self] at htj; cases htj
          have hci : s'.pc i = Phase.crit := by simpa [hpc, Function.update_of_ne, hia] using hti
          have hwj : s'.pc j = Phase.wait := by simpa [hpc, Function.update_of_ne, hja] using htj
          have hlt := ih i j hij hci hwj
          rw [hnum]
          simp [Function.update_of_ne, hia, hja]
          exact hlt
      · exact ih
  induction hs with
  | init =>
    rename_i hinit
    intro i j hij hboth
    rcases hinit with ⟨hn, hf, hp⟩
    rcases hboth with ⟨hci, hcj⟩
    rw [hp] at hci
    cases hci
  | step =>
    rename_i s' t' hs' hst' ih
    rcases hst' with hnext | rfl
    · rcases hnext with ⟨a, hstep⟩
      rcases hstep with hsf | hct | hent | hex
      · rcases hsf with ⟨hpc_a, hflag, hpc, hnum⟩
        intro i j hij hboth
        rcases hboth with ⟨hci, hcj⟩
        have hia : i ≠ a := by
          intro hia; subst i; rw [hpc, Function.update_self] at hci; cases hci
        have hja : j ≠ a := by
          intro hja; subst j; rw [hpc, Function.update_self] at hcj; cases hcj
        have hci' : s'.pc i = Phase.crit := by simpa [hpc, Function.update_of_ne, hia] using hci
        have hcj' : s'.pc j = Phase.crit := by simpa [hpc, Function.update_of_ne, hja] using hcj
        exact ih i j hij ⟨hci', hcj'⟩
      · rcases hct with ⟨hdoor, ticket, hgt, hnum, hflag, hpc⟩
        intro i j hij hboth
        rcases hboth with ⟨hci, hcj⟩
        have hia : i ≠ a := by
          intro hia; subst i; rw [hpc, Function.update_self] at hci; cases hci
        have hja : j ≠ a := by
          intro hja; subst j; rw [hpc, Function.update_self] at hcj; cases hcj
        have hci' : s'.pc i = Phase.crit := by simpa [hpc, Function.update_of_ne, hia] using hci
        have hcj' : s'.pc j = Phase.crit := by simpa [hpc, Function.update_of_ne, hja] using hcj
        exact ih i j hij ⟨hci', hcj'⟩
      · rcases hent with ⟨hwait, hguard, hpc, hnum, hflag⟩
        intro i j hij hboth
        rcases hboth with ⟨hci, hcj⟩
        by_cases hia : i = a
        · subst i
          have hja : j ≠ a := hij.symm
          have hcj' : s'.pc j = Phase.crit := by
            simpa [hpc, Function.update_of_ne, hja] using hcj
          have hlt : s'.num j < s'.num a := crit_lt_wait s' hs' j a hja hcj' hwait
          rcases hguard j hja with ⟨hflagj, hor⟩
          have hnumj_ne : s'.num j ≠ (0 : Ticket N) := by
            intro h0
            have hpcj := (num_iff s' hs' j).mp h0
            rcases hpcj with h | h
            · rw [hcj'] at h; cases h
            · rw [hcj'] at h; cases h
          have hLL : LL s' a j := by
            rcases hor with h0 | hll
            · exact False.elim (hnumj_ne h0)
            · exact hll
          rcases hLL with hlt2 | heq
          · exact (not_lt_of_gt hlt) hlt2
          · rcases heq with ⟨heq', hle⟩
            exact (lt_irrefl (s'.num j)) (heq' ▸ hlt)
        · by_cases hja : j = a
          · subst j
            have hci' : s'.pc i = Phase.crit := by
              simpa [hpc, Function.update_of_ne, hia] using hci
            have hlt : s'.num i < s'.num a := crit_lt_wait s' hs' i a hia hci' hwait
            rcases hguard i hia with ⟨hflagi, hor⟩
            have hnumi_ne : s'.num i ≠ (0 : Ticket N) := by
              intro h0
              have hpci := (num_iff s' hs' i).mp h0
              rcases hpci with h | h
              · rw [hci'] at h; cases h
              · rw [hci'] at h; cases h
            have hLL : LL s' a i := by
              rcases hor with h0 | hll
              · exact False.elim (hnumi_ne h0)
              · exact hll
            rcases hLL with hlt2 | heq
            · exact (not_lt_of_gt hlt) hlt2
            · rcases heq with ⟨heq', hle⟩
              exact (lt_irrefl (s'.num i)) (heq' ▸ hlt)
          · have hci' : s'.pc i = Phase.crit := by
              simpa [hpc, Function.update_of_ne, hia] using hci
            have hcj' : s'.pc j = Phase.crit := by
              simpa [hpc, Function.update_of_ne, hja] using hcj
            exact ih i j hij ⟨hci', hcj'⟩
      · rcases hex with ⟨hcrit, hnum, hpc, hflag⟩
        intro i j hij hboth
        rcases hboth with ⟨hci, hcj⟩
        have hia : i ≠ a := by
          intro hia; subst i; rw [hpc, Function.update_self] at hci; cases hci
        have hja : j ≠ a := by
          intro hja; subst j; rw [hpc, Function.update_self] at hcj; cases hcj
        have hci' : s'.pc i = Phase.crit := by simpa [hpc, Function.update_of_ne, hia] using hci
        have hcj' : s'.pc j = Phase.crit := by simpa [hpc, Function.update_of_ne, hja] using hcj
        exact ih i j hij ⟨hci', hcj'⟩
    · exact ih

end Bakery
