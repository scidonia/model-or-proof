/-
Bakery mutual exclusion, **negative control** (Route B): the analogue of
`specs/tla/bakery/BakeryMutant.tla`.

Identical to `Bakery.lean` except that `Enter` keeps only the flag half of its guard — the ticket half
(`num[j] = 0 \/ LL s i j`) is dropped, so a process may enter its critical section without holding a
ticket that takes precedence. Two waiting processes whose flags are both down then each satisfy the
weakened guard and enter together, so the theorem stated below is **false** and no proof can close it:
the expected Route B outcome is `fail_to_close`, and a run that reports `success` on this file is
broken and its numbers are discarded (protocol §5, plan D7).

The statement is the seed of that run (plan D5): as in `Bakery.lean`, the model and the statement are
the human's, the proof search is the loop's. `LL` is kept although the weakened `Enter` below does not
read it, so this file differs from `Bakery.lean` in exactly one guard — the same choice the TLA+
mutant makes.
-/
import Mathlib

namespace BakeryMutant

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

/-- TLA+ `VARIABLES num, flag, pc`, with `TypeOK` carried by the type. -/
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
  s.num = fun _ => (0 : Ticket N) ∧ s.flag = fun _ => false ∧ s.pc = fun _ => Phase.idle

/-- TLA+ `LL(i, j)`, the lexicographic ticket order — unused by the weakened `Enter` below and kept
only so this file differs from `Bakery.lean` in exactly one guard. -/
def LL (s : State N) (i j : Process N) : Prop :=
  s.num i < s.num j ∨ (s.num i = s.num j ∧ i ≤ j)

/-- TLA+ `SetFlag(i)`: an idle process enters the doorway. -/
def SetFlag (i : Process N) (s t : State N) : Prop :=
  s.pc i = Phase.idle ∧
    t.flag = Function.update s.flag i true ∧
    t.pc = Function.update s.pc i Phase.doorway ∧
    t.num = s.num

/-- TLA+ `ChooseTicket(i)`: a process in the doorway takes a ticket strictly greater than every ticket
currently held, inside the bound `0 .. N`, lowers its flag and starts waiting. -/
def ChooseTicket (i : Process N) (s t : State N) : Prop :=
  s.pc i = Phase.doorway ∧
    ∃ ticket : Ticket N,
      (∀ j : Process N, j ≠ i → s.num j < ticket) ∧
        t.num = Function.update s.num i ticket ∧
        t.flag = Function.update s.flag i false ∧
        t.pc = Function.update s.pc i Phase.wait

/-- **The mutation.** TLA+ `Enter(i)`-minus-its-ticket-half: a waiting process enters its critical
section as soon as no process is in its doorway, regardless of the tickets held. -/
def Enter (i : Process N) (s t : State N) : Prop :=
  s.pc i = Phase.wait ∧
    (∀ j : Process N, j ≠ i → s.flag j = false) ∧
    t.pc = Function.update s.pc i Phase.crit ∧
    t.num = s.num ∧
    t.flag = s.flag

/-- TLA+ `Exit(i)`: the critical section is left, the ticket is given back and the process returns to
idle. -/
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

/-- The states admitted by TLA+ `Spec == Init /\ [][Next]_vars`, read as a state predicate. The
module's `ASSUME N >= 2` is carried by the theorem's first argument. -/
inductive Reachable : State N → Prop where
  /-- The initial states. -/
  | init {s} : Init s → Reachable s
  /-- The states one `[Next]_vars` step away from a reachable state. -/
  | step {s t} : Reachable s → Step s t → Reachable t

/-- TLA+ `MutualExclusion == \A i, j \in P : (i # j) => ~(pc[i] = "crit" /\ pc[j] = "crit")` — the
property TLC refutes on `specs/tla/bakery/BakeryMutant.tla` (`N = 3`), and the loop must fail to close
here. -/
def MutualExclusion (s : State N) : Prop :=
  ∀ i j : Process N, i ≠ j → ¬ (s.pc i = Phase.crit ∧ s.pc j = Phase.crit)

/-! ## The theorem (false — the point of the mutant) -/

/-- **Mutual exclusion**, in general: false for this model, since `Enter` dropped its ticket half. Two
waiting processes whose flags are down may enter one after the other, so a state with two processes in
their critical section is reachable from `Init`; the loop cannot close this and must not appear to
(protocol §5, plan D7). -/
theorem mutual_exclusion (hN : 2 ≤ N) (s : State N) (hs : Reachable s) : MutualExclusion s := by
  sorry

end BakeryMutant
