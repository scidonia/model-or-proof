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
  classical
  let Inv (s : State N) : Prop :=
    (∀ i : Process N, s.pc i = Phase.wait → s.num i ≠ (0 : Ticket N)) ∧
    (∀ i : Process N, s.pc i = Phase.crit → s.num i ≠ (0 : Ticket N)) ∧
    (∀ i j : Process N, i ≠ j → s.num i ≠ (0 : Ticket N) → s.num j ≠ (0 : Ticket N) →
      s.num i ≠ s.num j) ∧
    (∀ i j : Process N, i ≠ j → s.pc j = Phase.crit → s.num i ≠ (0 : Ticket N) →
      s.num j < s.num i)
  have hinit : ∀ s : State N, Init s → Inv s := by
    intro s hs
    rcases hs with ⟨hn, hf, hp⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      have hpi : s.pc i = Phase.idle := congrFun hp i
      rw [hpi] at hi
      cases hi
    · intro i hi
      have hpi : s.pc i = Phase.idle := congrFun hp i
      rw [hpi] at hi
      cases hi
    · intro i j hij hni hnj
      have hni0 : s.num i = (0 : Ticket N) := congrFun hn i
      exact False.elim (hni hni0)
    · intro i j hij hjc hni
      have hpj : s.pc j = Phase.idle := congrFun hp j
      rw [hpj] at hjc
      cases hjc
  have hstep : ∀ s t : State N, Inv s → Step s t → Inv t := by
    intro s t hs hst
    rcases hst with hNext | hEq
    · rcases hs with ⟨hW, hA, hC, hB⟩
      rcases hNext with ⟨i, hst_i⟩
      rcases hst_i with hsf | hct | hent | hex
      · -- SetFlag
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro k hk
          by_cases hki : k = i
          · subst k
            have hpci : t.pc i = Phase.doorway := by
              rw [hsf.2.2.1]
              simp [Function.update]
            rw [hpci] at hk
            cases hk
          · have hpck : t.pc k = s.pc k := by
              rw [hsf.2.2.1]
              simp [Function.update, hki]
            rw [hpck] at hk
            rw [hsf.2.2.2]
            exact hW k hk
        · intro k hk
          by_cases hki : k = i
          · subst k
            have hpci : t.pc i = Phase.doorway := by
              rw [hsf.2.2.1]
              simp [Function.update]
            rw [hpci] at hk
            cases hk
          · have hpck : t.pc k = s.pc k := by
              rw [hsf.2.2.1]
              simp [Function.update, hki]
            rw [hpck] at hk
            rw [hsf.2.2.2]
            exact hA k hk
        · intro a b hab hna hnb
          rw [congrFun hsf.2.2.2 a] at hna
          rw [congrFun hsf.2.2.2 b] at hnb
          rw [congrFun hsf.2.2.2 a, congrFun hsf.2.2.2 b]
          exact hC a b hab hna hnb
        · intro a b hab hbc hna
          by_cases hbi : b = i
          · subst b
            have hpci : t.pc i = Phase.doorway := by
              rw [hsf.2.2.1]
              simp [Function.update]
            rw [hpci] at hbc
            cases hbc
          · have hpcb : t.pc b = s.pc b := by
              rw [hsf.2.2.1]
              simp [Function.update, hbi]
            rw [hpcb] at hbc
            have hna' : s.num a ≠ (0 : Ticket N) := by
              rw [congrFun hsf.2.2.2 a] at hna
              exact hna
            have hlt : s.num b < s.num a := hB a b hab hbc hna'
            rw [congrFun hsf.2.2.2 b, congrFun hsf.2.2.2 a]
            exact hlt
      · -- ChooseTicket
        rcases hct with ⟨hpci, ticket, hlt, htnum, htflag, htpc⟩
        have hgtcard : 1 < Fintype.card (Process N) := by
          have hc : Fintype.card (Process N) = N := Fintype.card_fin N
          omega
        rcases Fintype.exists_ne_of_one_lt_card hgtcard i with ⟨j0, hj0⟩
        have hjn0 : s.num j0 < ticket := hlt j0 hj0
        have htnz : ticket ≠ (0 : Ticket N) := by
          intro hz
          have hv : (s.num j0 : ℕ) < (ticket : ℕ) := Fin.lt_def.mp hjn0
          rw [hz] at hv
          norm_num at hv
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro k hk
          by_cases hki : k = i
          · subst k
            rw [htnum]
            simp [Function.update]
            exact htnz
          · rw [htpc] at hk
            simp [Function.update, hki] at hk
            rw [htnum]
            simp [Function.update, hki]
            exact hW k hk
        · intro k hk
          by_cases hki : k = i
          · subst k
            rw [htpc] at hk
            simp [Function.update] at hk
          · rw [htpc] at hk
            simp [Function.update, hki] at hk
            rw [htnum]
            simp [Function.update, hki]
            exact hA k hk
        · intro a b hab hna hnb
          by_cases hai : a = i
          · subst a
            have htb : t.num b = s.num b := by
              rw [htnum]
              simp [Function.update, hab.symm]
            have hta : t.num i = ticket := by
              rw [htnum]
              simp [Function.update]
            rw [hta, htb]
            exact (ne_of_lt (hlt b hab.symm)).symm
          · by_cases hbi : b = i
            · subst b
              have hta : t.num a = s.num a := by
                rw [htnum]
                simp [Function.update, hai]
              have htb : t.num i = ticket := by
                rw [htnum]
                simp [Function.update]
              rw [hta, htb]
              exact ne_of_lt (hlt a hai)
            · have hta : t.num a = s.num a := by
                rw [htnum]
                simp [Function.update, hai]
              have htb : t.num b = s.num b := by
                rw [htnum]
                simp [Function.update, hbi]
              rw [hta] at hna
              rw [htb] at hnb
              rw [hta, htb]
              exact hC a b hab hna hnb
        · intro a b hab hbc hna
          by_cases hbi : b = i
          · subst b
            rw [htpc] at hbc
            simp [Function.update] at hbc
          · have hpcb : t.pc b = s.pc b := by
              rw [htpc]
              simp [Function.update, hbi]
            rw [hpcb] at hbc
            by_cases hai : a = i
            · subst a
              have htb : t.num b = s.num b := by
                rw [htnum]
                simp [Function.update, hbi]
              have hta : t.num i = ticket := by
                rw [htnum]
                simp [Function.update]
              rw [hta, htb]
              exact hlt b hbi
            · have hta : t.num a = s.num a := by
                rw [htnum]
                simp [Function.update, hai]
              have htb : t.num b = s.num b := by
                rw [htnum]
                simp [Function.update, hbi]
              rw [hta] at hna
              have hlt' : s.num b < s.num a := hB a b hab hbc hna
              rw [htb, hta]
              exact hlt'
      · -- Enter
        rcases hent with ⟨hpci, hguard, htpc, htnum, htflag⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro k hk
          by_cases hki : k = i
          · subst k
            rw [htpc] at hk
            simp [Function.update] at hk
          · rw [htpc] at hk
            simp [Function.update, hki] at hk
            rw [htnum]
            exact hW k hk
        · intro k hk
          by_cases hki : k = i
          · subst k
            rw [htnum]
            exact hW i hpci
          · rw [htpc] at hk
            simp [Function.update, hki] at hk
            rw [htnum]
            exact hA k hk
        · intro a b hab hna hnb
          rw [htnum] at hna hnb ⊢
          exact hC a b hab hna hnb
        · intro a b hab hbc hna
          by_cases hbi : b = i
          · subst b
            have hna' : s.num a ≠ (0 : Ticket N) := by
              rw [htnum] at hna
              exact hna
            have hni' : s.num i ≠ (0 : Ticket N) := hW i hpci
            rcases hguard a hab with ⟨hfa, hnumLL⟩
            rcases hnumLL with hz | hLL
            · exact False.elim (hna' hz)
            · rcases hLL with hlt | ⟨heq, hle⟩
              · rw [htnum]
                exact hlt
              · have hne : s.num a ≠ s.num i := hC a i hab hna' hni'
                exact False.elim (hne heq.symm)
          · have hpcb : t.pc b = s.pc b := by
              rw [htpc]
              simp [Function.update, hbi]
            rw [hpcb] at hbc
            by_cases hai : a = i
            · subst a
              have hni' : s.num i ≠ (0 : Ticket N) := hW i hpci
              have hlt' : s.num b < s.num i := hB i b hab hbc hni'
              rw [htnum]
              exact hlt'
            · have hta : t.num a = s.num a := by
                rw [htnum]
              have htb : t.num b = s.num b := by
                rw [htnum]
              rw [hta] at hna
              have hlt' : s.num b < s.num a := hB a b hab hbc hna
              rw [htb, hta]
              exact hlt'
      · -- Exit
        rcases hex with ⟨hpci, htnum, htpc, htflag⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro k hk
          by_cases hki : k = i
          · subst k
            rw [htpc] at hk
            simp [Function.update] at hk
          · rw [htpc] at hk
            simp [Function.update, hki] at hk
            rw [htnum]
            simp [Function.update, hki]
            exact hW k hk
        · intro k hk
          by_cases hki : k = i
          · subst k
            rw [htpc] at hk
            simp [Function.update] at hk
          · rw [htpc] at hk
            simp [Function.update, hki] at hk
            rw [htnum]
            simp [Function.update, hki]
            exact hA k hk
        · intro a b hab hna hnb
          by_cases hai : a = i
          · subst a
            rw [htnum] at hna
            simp [Function.update] at hna
          · by_cases hbi : b = i
            · subst b
              rw [htnum] at hnb
              simp [Function.update] at hnb
            · rw [htnum] at hna hnb ⊢
              simp [Function.update, hai, hbi] at hna hnb ⊢
              exact hC a b hab hna hnb
        · intro a b hab hbc hna
          by_cases hbi : b = i
          · subst b
            rw [htpc] at hbc
            simp [Function.update] at hbc
          · have hpcb : t.pc b = s.pc b := by
              rw [htpc]
              simp [Function.update, hbi]
            rw [hpcb] at hbc
            by_cases hai : a = i
            · subst a
              rw [htnum] at hna
              simp [Function.update] at hna
            · rw [htnum] at hna ⊢
              simp [Function.update, hai, hbi] at hna ⊢
              exact hB a b hab hbc hna
    · subst t
      exact hs
  have hinv : Inv s := by
    induction hs with
    | init h => exact hinit _ h
    | step ih hst =>
        rename_i _ inv
        exact hstep _ _ inv hst
  rcases hinv with ⟨hW, hA, hC, hB⟩
  intro i j hij hboth
  rcases hboth with ⟨hci, hcj⟩
  have hni : s.num i ≠ (0 : Ticket N) := hA i hci
  have hnj : s.num j ≠ (0 : Ticket N) := hA j hcj
  have hji : s.num j < s.num i := hB i j hij hcj hni
  have hij' : s.num i < s.num j := hB j i hij.symm hci hnj
  exact (lt_irrefl (s.num i) (hij'.trans hji))

end Bakery
