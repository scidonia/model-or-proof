/-
LeLann–Chang–Roberts, negative control: the max-id election guard is dropped.

Identical to `LCR.lean` except for `ElectSelf`, which elects a process with no condition beyond its not
already being a leader. In the model, election is reachable only when a process's own identity comes back
round the ring (`Receive`'s third case, `m = i`), which is what makes the elected process the maximum;
`ElectSelf` removes that condition, so any two processes can both become leader and `UniqueLeader` is
false.

The violation is *unforced*, unlike the bakery mutant's: there, two processes must happen to be waiting
with distinct tickets at the same moment; here, any two processes electing in any order suffice. That is
deliberate — the control's job is to check the rig refuses a false statement, not to check that the rig is
sensitive to a subtle one — and it is why a run that closes this file means the pipeline is broken rather
than that the model proved something hard (protocol §5).

The theorem statement is false, and it carries a `sorry` because it is a seed like any other: the run is
expected to *fail* to close it, and that failure is the cell's acceptance.
-/
import Mathlib

namespace LCRMutant

/-! ## The state -/

/-- The processes — TLA+ `P == 1 .. N`. -/
abbrev Process (N : ℕ) := Fin N

/-- The ring's successor: TLA+ `succ(i) == (i % N) + 1`. -/
def succ (i : Process N) : Process N := ⟨(i.val + 1) % N, Nat.mod_lt _ i.pos⟩

/-- TLA+ `VARIABLES ident, msg, sent, leader`, minus `ident`; see `LCR.lean`'s header for why. -/
structure State (N : ℕ) where
  /-- The identity in transit into each process's slot, if any. -/
  msg : Process N → Option (Process N)
  /-- Whether each process has already initiated. -/
  sent : Process N → Bool
  /-- Whether each process has elected itself. -/
  leader : Process N → Bool

variable {N : ℕ}

/-! ## The model -/

/-- TLA+ `Init`. -/
def Init (s : State N) : Prop :=
  (s.msg = fun _ => none) ∧ (s.sent = fun _ => false) ∧ (s.leader = fun _ => false)

/-- TLA+ `Send(i)`. -/
def Send (i : Process N) (s t : State N) : Prop :=
  s.sent i = false ∧
    s.msg (succ i) = none ∧
    t.msg = Function.update s.msg (succ i) (some i) ∧
    t.sent = Function.update s.sent i true ∧
    t.leader = s.leader

/-- The weakened action: election with no condition beyond not already being a leader. In `LCR` this is
reachable only under `msg[i] = ident[i]`; here it is reachable whenever the process is not a leader. -/
def ElectSelf (i : Process N) (s t : State N) : Prop :=
  s.leader i = false ∧
    t.leader = Function.update s.leader i true ∧
    t.msg = s.msg ∧
    t.sent = s.sent

/-- TLA+ `Receive(i)`, unchanged from `LCR`. -/
def Receive (i : Process N) (s t : State N) : Prop :=
  ∃ m : Process N,
    s.msg i = some m ∧
      ((m > i ∧
            s.msg (succ i) = none ∧
            t.msg = Function.update (Function.update s.msg i none) (succ i) (some m) ∧
            t.sent = s.sent ∧
            t.leader = s.leader) ∨
        (m < i ∧
            t.msg = Function.update s.msg i none ∧
            t.sent = s.sent ∧
            t.leader = s.leader) ∨
        (m = i ∧
            t.leader = Function.update s.leader i true ∧
            t.msg = Function.update s.msg i none ∧
            t.sent = s.sent))

/-- TLA+ `Next`, with the weakened election added. -/
def Next (s t : State N) : Prop :=
  ∃ i : Process N, Send i s t ∨ Receive i s t ∨ ElectSelf i s t

/-- TLA+ `[Next]_vars`. -/
def Step (s t : State N) : Prop := Next s t ∨ t = s

/-- The states admitted by `Spec == Init /\ [][Next]_vars`. -/
inductive Reachable : State N → Prop where
  /-- The initial states. -/
  | init {s} : Init s → Reachable s
  /-- The states one `[Next]_vars` step away from a reachable state. -/
  | step {s t} : Reachable s → Step s t → Reachable t

/-- TLA+ `UniqueLeader == Card({i \in P : leader[i]}) <= 1`, in the pairwise form the proof reasons
about. False here at `N >= 2`, which is the point. -/
def UniqueLeader (s : State N) : Prop :=
  ∀ i j : Process N, i ≠ j → ¬ (s.leader i = true ∧ s.leader j = true)

/-! ## The (false) theorem -/

/-- **Unique leadership**, as in `LCR` — and false in this model, because `ElectSelf` drops the guard
that made it true. A run that closes this has been fooled. -/
theorem unique_leader (hN : 2 ≤ N) (s : State N) (hs : Reachable s) : UniqueLeader s := by
  sorry

end LCRMutant
