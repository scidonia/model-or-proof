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
      (∀ i : Process N, s.pc i = Phase.crit → ∀ j : Process N, j ≠ i → s.num j = (0 : Ticket N) ∨ LL s i j)
  have hInv : ∀ s : State N, Reachable s → Inv s := by
    intro s hs
    induction hs with
    | init =>
      rename_i hinit
      rcases hinit with ⟨hnum0, hflag0, hpc0⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i j hij hcrit
        rcases hcrit with ⟨hci, hcj⟩
        rw [hpc0] at hci
        cases hci
      · intro i hi
        rw [hpc0] at hi
        rcases hi with hi | hi <;> cases hi
      · intro i hci j hij
        rw [hpc0] at hci
        cases hci
    | step =>
      rename_i s' t' hs' hst' ih
      rcases hst' with hnext | rfl
      · rcases hnext with ⟨a, hstep⟩
        rcases hstep with hsf | hct | hent | hex
        · -- SetFlag
          rcases hsf with ⟨hpc_a, hflag, hpc, hnum⟩
          refine ⟨?_, ?_, ?_⟩
          · intro i j hij hcrit
            rcases hcrit with ⟨hci, hcj⟩
            have hia : i ≠ a := by
              intro hia
              subst i
              rw [hpc, Function.update_self] at hci
              cases hci
            have hja : j ≠ a := by
              intro hja
              subst j
              rw [hpc, Function.update_self] at hcj
              cases hcj
            have hci' : s'.pc i = Phase.crit := by
              simpa [hpc, Function.update_of_ne, hia] using hci
            have hcj' : s'.pc j = Phase.crit := by
              simpa [hpc, Function.update_of_ne, hja] using hcj
            exact ih.1 i j hij ⟨hci', hcj'⟩
          · intro i hi
            have hia : i ≠ a := by
              intro hia
              subst i
              rw [hpc, Function.update_self] at hi
              rcases hi with hi | hi <;> cases hi
            have hi' : s'.pc i = Phase.wait ∨ s'.pc i = Phase.crit := by
              simpa [hpc, Function.update_of_ne, hia] using hi
            have hne := ih.2.1 i hi'
            rw [hnum]
            exact hne
          · intro i hci j hij
            have hia : i ≠ a := by
              intro hia
              subst i
              rw [hpc, Function.update_self] at hci
              cases hci
            have hci' : s'.pc i = Phase.crit := by
              simpa [hpc, Function.update_of_ne, hia] using hci
            have hor := ih.2.2 i hci' j hij
            simpa [hnum, LL] using hor
        · -- ChooseTicket
          rcases hct with ⟨hpc_a, ticket, hgt, hnum, hflag, hpc⟩
          refine ⟨?_, ?_, ?_⟩
          · intro i j hij hcrit
            rcases hcrit with ⟨hci, hcj⟩
            have hia : i ≠ a := by
              intro hia
              subst i
              rw [hpc, Function.update_self] at hci
              cases hci
            have hja : j ≠ a := by
              intro hja
              subst j
              rw [hpc, Function.update_self] at hcj
              cases hcj
            have hci' : s'.pc i = Phase.crit := by
              simpa [hpc, Function.update_of_ne, hia] using hci
            have hcj' : s'.pc j = Phase.crit := by
              simpa [hpc, Function.update_of_ne, hja] using hcj
            exact ih.1 i j hij ⟨hci', hcj'⟩
          · intro i hi
            by_cases hia : i = a
            · subst i
              have hcard : 1 < Fintype.card (Process N) := by
                change 1 < Fintype.card (Fin N)
                rw [Fintype.card_fin]
                exact hN
              obtain ⟨k, hka⟩ := Fintype.exists_ne_of_one_lt_card hcard a
              have hlt : s'.num k < ticket := hgt k hka
              have hpos : (0 : Ticket N) < ticket := lt_of_le_of_lt (Fin.zero_le (s'.num k)) hlt
              have hne : ticket ≠ (0 : Ticket N) := ne_of_gt hpos
              rw [hnum]
              simp [Function.update_self]
              exact hne
            · have hi' : s'.pc i = Phase.wait ∨ s'.pc i = Phase.crit := by
                simpa [hpc, Function.update_of_ne, hia] using hi
              have hne := ih.2.1 i hi'
              rw [hnum]
              simpa [Function.update_of_ne, hia] using hne
          · intro i hci j hij
            have hia : i ≠ a := by
              intro hia
              subst i
              rw [hpc, Function.update_self] at hci
              cases hci
            have hci' : s'.pc i = Phase.crit := by
              simpa [hpc, Function.update_of_ne, hia] using hci
            by_cases hja : j = a
            · subst j
              have hlt : s'.num i < ticket := hgt i hia
              right
              left
              rw [hnum]
              simpa [Function.update_self, Function.update_of_ne, hia] using hlt
            · have hor := ih.2.2 i hci' j hij
              simpa [hnum, Function.update_of_ne, hia, hja, LL] using hor
        · -- Enter
          rcases hent with ⟨hwait, hguard, hpc, hnum, hflag⟩
          refine ⟨?_, ?_, ?_⟩
          · intro i j hij hcrit
            have hno_other_crit : ∀ k : Process N, k ≠ a → s'.pc k ≠ Phase.crit := by
              intro k hka hkcrit
              rcases hguard k hka with ⟨hflagk, hork⟩
              have hnumk_ne : s'.num k ≠ (0 : Ticket N) := ih.2.1 k (Or.inr hkcrit)
              have hLL_ak : LL s' a k := by
                rcases hork with h0 | hll
                · exact False.elim (hnumk_ne h0)
                · exact hll
              have hnuma_ne : s'.num a ≠ (0 : Ticket N) := ih.2.1 a (Or.inl hwait)
              have hLL_ka : LL s' k a := by
                rcases ih.2.2 k hkcrit a hka.symm with h0 | hll
                · exact False.elim (hnuma_ne h0)
                · exact hll
              have hanti : ¬ (LL s' a k ∧ LL s' k a) := by
                rintro ⟨h1, h2⟩
                rcases h1 with hlt | ⟨heq, hle⟩
                · rcases h2 with hlt2 | ⟨heq2, hle2⟩
                  · exact lt_asymm hlt hlt2
                  · simp [heq2] at hlt
                · rcases h2 with hlt2 | ⟨heq2, hle2⟩
                  · simp [heq] at hlt2
                  · exact hka (le_antisymm hle hle2).symm
              exact hanti ⟨hLL_ak, hLL_ka⟩
            rcases hcrit with ⟨hci, hcj⟩
            by_cases hia : i = a
            · subst i
              have hja : j ≠ a := hij.symm
              have hcj' : s'.pc j = Phase.crit := by
                simpa [hpc, Function.update_of_ne, hja] using hcj
              exact (hno_other_crit j hja) hcj'
            · have hci' : s'.pc i = Phase.crit := by
                simpa [hpc, Function.update_of_ne, hia] using hci
              exact (hno_other_crit i hia) hci'
          · intro i hi
            by_cases hia : i = a
            · subst i
              have hnuma_ne : s'.num a ≠ (0 : Ticket N) := ih.2.1 a (Or.inl hwait)
              rw [hnum]
              exact hnuma_ne
            · have hi' : s'.pc i = Phase.wait ∨ s'.pc i = Phase.crit := by
                simpa [hpc, Function.update_of_ne, hia] using hi
              have hne := ih.2.1 i hi'
              rw [hnum]
              exact hne
          · intro i hci j hij
            by_cases hia : i = a
            · subst i
              rcases hguard j hij with ⟨hflagj, horj⟩
              simpa [hnum, LL] using horj
            · have hci' : s'.pc i = Phase.crit := by
                simpa [hpc, Function.update_of_ne, hia] using hci
              have hor := ih.2.2 i hci' j hij
              simpa [hnum, LL] using hor
        · -- Exit
          rcases hex with ⟨hcrit, hnum, hpc, hflag⟩
          refine ⟨?_, ?_, ?_⟩
          · intro i j hij hcrit'
            rcases hcrit' with ⟨hci, hcj⟩
            have hia : i ≠ a := by
              intro hia
              subst i
              rw [hpc, Function.update_self] at hci
              cases hci
            have hja : j ≠ a := by
              intro hja
              subst j
              rw [hpc, Function.update_self] at hcj
              cases hcj
            have hci' : s'.pc i = Phase.crit := by
              simpa [hpc, Function.update_of_ne, hia] using hci
            have hcj' : s'.pc j = Phase.crit := by
              simpa [hpc, Function.update_of_ne, hja] using hcj
            exact ih.1 i j hij ⟨hci', hcj'⟩
          · intro i hi
            have hia : i ≠ a := by
              intro hia
              subst i
              rw [hpc, Function.update_self] at hi
              rcases hi with hi | hi <;> cases hi
            have hi' : s'.pc i = Phase.wait ∨ s'.pc i = Phase.crit := by
              simpa [hpc, Function.update_of_ne, hia] using hi
            have hne := ih.2.1 i hi'
            rw [hnum]
            simp [Function.update_of_ne, hia]
            exact hne
          · intro i hci j hij
            have hia : i ≠ a := by
              intro hia
              subst i
              rw [hpc, Function.update_self] at hci
              cases hci
            have hci' : s'.pc i = Phase.crit := by
              simpa [hpc, Function.update_of_ne, hia] using hci
            by_cases hja : j = a
            · subst j
              rw [hnum]
              left
              simp [Function.update_self]
            · have hor := ih.2.2 i hci' j hij
              simpa [hnum, Function.update_of_ne, hia, hja, LL] using hor
      · exact ih
  exact (hInv s hs).1

end Bakery
