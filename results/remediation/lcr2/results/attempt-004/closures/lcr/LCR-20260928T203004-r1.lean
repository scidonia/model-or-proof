/-
LeLann–Chang–Roberts leader election — the Lean model for Route B (protocol §2).

This is the idiomatic counterpart of `specs/tla/lcr/LCR.tla`: N processes in a unidirectional ring, each
with a unique identity, every message travelling from a process to its successor. Each process initiates
once with its own identity; a process forwards a message larger than its identity, discards one that is
smaller, and elects itself when its own identity comes all the way round — so it elects only if it is the
largest in the ring. The statement-by-statement correspondence is audited in `docs/equivalence-lcr.md`
(protocol §4.1); the model neither strengthens an assumption nor weakens the goal.

Two correspondences worth naming here, because they are the model's only departures from a literal
transcription of the module:

* The module's `ident` is a *variable* that no action ever changes (every action takes
  `UNCHANGED ident`). It is therefore not a field of `State`: the identity of process `i` is `i`, so
  `Send` loads `i` itself into the successor's slot. Dropping an unchanged variable is a change of
  representation, not of the model.
* The module's `msg[i] = 0` ("slot empty") is `s.msg i = none` here, `0` being outside `1 .. N` in the
  module and `none` being outside the identities of `Process N`.

This file is the closure loop's **tier-2 seed** (plan D5): the theorem statement is the human's, the proof
is the loop's, and the `sorry` below is the seed's placeholder, not a result — the run is closed only when
the harness has observed it gone (protocol §8). The tier-1 corollary at the task's `N₀` is a separate seed
(`LCRN0.lean`), written once `tasks/lcr.json`'s `n0` is calibrated (the TLC sweep, plan D23 rung 1). The
negative control is `LCRMutant.lean`.
-/
import Mathlib

namespace LCR

/-! ## The state -/

/-- The processes — TLA+ `P == 1 .. N`. -/
abbrev Process (N : ℕ) := Fin N

/-- The ring's successor: TLA+ `succ(i) == (i % N) + 1`. A process exists, so `N > 0` (`i.pos`), which
is the positivity `Nat.mod_lt` needs. -/
def succ (i : Process N) : Process N := ⟨(i.val + 1) % N, Nat.mod_lt _ i.pos⟩

/-- TLA+ `VARIABLES ident, msg, sent, leader`, minus `ident` (see the header): a slot holding the
identity in transit or nothing, whether each process has initiated, and whether each has elected
itself. TLA+'s `TypeOK` is carried by this type — a slot holds a process identity or nothing, the two
flags are boolean — so no value of `State N` can violate it. -/
structure State (N : ℕ) where
  /-- The identity in transit into each process's slot, if any. TLA+ `msg \in [P -> 0 .. N]`, with
  `0` meaning "empty". -/
  msg : Process N → Option (Process N)
  /-- Whether each process has already initiated. TLA+ `sent \in [P -> BOOLEAN]`. -/
  sent : Process N → Bool
  /-- Whether each process has elected itself. TLA+ `leader \in [P -> BOOLEAN]`. -/
  leader : Process N → Bool

variable {N : ℕ}

/-! ## The model -/

/-- TLA+ `Init == /\ ident = [i \in P |-> i] /\ msg = [i \in P |-> 0] /\ sent = [i \in P |-> FALSE]
/\ leader = [i \in P |-> FALSE]`, with `ident` represented by the identity function rather than stored. -/
def Init (s : State N) : Prop :=
  (s.msg = fun _ => none) ∧ (s.sent = fun _ => false) ∧ (s.leader = fun _ => false)

/-- TLA+ `Send(i)`: an uninitiated process initiates once, with its own identity, into its successor's
slot. The successor's slot may be occupied, in which case there is no step — the ring's capacity
assumption, made explicit rather than left to the reader. -/
def Send (i : Process N) (s t : State N) : Prop :=
  s.sent i = false ∧
    s.msg (succ i) = none ∧
    t.msg = Function.update s.msg (succ i) (some i) ∧
    t.sent = Function.update s.sent i true ∧
    t.leader = s.leader

/-- TLA+ `Receive(i)`: the three cases of the algorithm, each its own disjunct so a violation can be
attributed. A larger identity is forwarded, a smaller one discarded, and the process's own identity
returning round the ring is the election — the guard `LCRMutant.lean` drops. -/
def Receive (i : Process N) (s t : State N) : Prop :=
  ∃ m : Process N,
    s.msg i = some m ∧
      (-- forward a larger identity
        (m > i ∧
            s.msg (succ i) = none ∧
            t.msg = Function.update (Function.update s.msg i none) (succ i) (some m) ∧
            t.sent = s.sent ∧
            t.leader = s.leader) ∨
        -- discard a smaller identity
        (m < i ∧
            t.msg = Function.update s.msg i none ∧
            t.sent = s.sent ∧
            t.leader = s.leader) ∨
        -- our own identity has returned: elect, and stop the message
        (m = i ∧
            t.leader = Function.update s.leader i true ∧
            t.msg = Function.update s.msg i none ∧
            t.sent = s.sent))

/-- TLA+ `Next == \E i \in P : Send(i) \/ Receive(i)`. -/
def Next (s t : State N) : Prop :=
  ∃ i : Process N, Send i s t ∨ Receive i s t

/-- TLA+ `[Next]_vars`: a step of `Next`, or a step that changes nothing. -/
def Step (s t : State N) : Prop := Next s t ∨ t = s

/-- The states admitted by TLA+ `Spec == Init /\ [][Next]_vars`, read as a state predicate — the
invariance reading of a safety property, which is what `UniqueLeader` is (protocol §11 decision 4). The
module's `ASSUME N >= 2` is carried by the theorem's first argument rather than here: `Init` names no
distinguished process, so it holds for every `N`. -/
inductive Reachable : State N → Prop where
  /-- The initial states. -/
  | init {s} : Init s → Reachable s
  /-- The states one `[Next]_vars` step away from a reachable state. -/
  | step {s t} : Reachable s → Step s t → Reachable t

/-- TLA+ `UniqueLeader == Card({i \in P : leader[i]}) <= 1`: at most one process is ever a leader. The
cardinality bound is written as the equivalent pairwise form, which is what a proof reasons about. -/
def UniqueLeader (s : State N) : Prop :=
  ∀ i j : Process N, i ≠ j → ¬ (s.leader i = true ∧ s.leader j = true)

/-! ## The theorem -/

/-- **Unique leadership**, in general (tier 2, protocol §2): every state reachable under `Spec` has at
most one leader, at every `N` the module's assumption admits — the TLA+ `Spec => []UniqueLeader` under
`ASSUME N >= 2` (`LCR.tla:21`, `:99`). -/
theorem unique_leader (hN : 2 ≤ N) (s : State N) (hs : Reachable s) : UniqueLeader s := by
  let IsMax : Process N → Prop := fun m => ∀ q : Process N, q ≤ m
  have hsucc_ne : ∀ i : Process N, succ i ≠ i := by
    intro i h
    have hval : (i.val + 1) % N = i.val := congrArg Fin.val h
    have hlt : i.val < N := i.isLt
    have hle : i.val + 1 ≤ N := Nat.succ_le_of_lt hlt
    rcases lt_or_eq_of_le hle with hlt' | heq
    · have hm : (i.val + 1) % N = i.val + 1 := Nat.mod_eq_of_lt hlt'
      rw [hm] at hval
      omega
    · have hm : (i.val + 1) % N = 0 := by
        rw [heq]
        exact Nat.mod_self N
      rw [hm] at hval
      have hN' : N = 1 := by omega
      omega
  have hsucc_le_of_lt : ∀ {i m : Process N}, i < m → succ i ≤ m := by
    intro i m hlt
    have h1 : i.val < m.val := hlt
    have h2 : m.val < N := m.isLt
    have h3 : i.val + 1 < N := by omega
    have h4 : (i.val + 1) % N = i.val + 1 := Nat.mod_eq_of_lt h3
    change (i.val + 1) % N ≤ m.val
    rw [h4]
    omega
  have hgt_succ : ∀ m : Process N, succ m < m → IsMax m := by
    intro m hm
    have hltN : m.val < N := m.isLt
    have hnot : ¬ m.val < N - 1 := by
      intro hlt
      have h1 : m.val + 1 < N := by omega
      have hmod : (m.val + 1) % N = m.val + 1 := Nat.mod_eq_of_lt h1
      have hsucc : (succ m).val = m.val + 1 := by
        change (m.val + 1) % N = m.val + 1
        exact hmod
      have hcontr : m.val + 1 < m.val := by
        rw [← hsucc]
        exact hm
      omega
    have hmN : m.val = N - 1 := by omega
    intro q
    change q.val ≤ m.val
    have hq : q.val < N := q.isLt
    omega
  have hmax_eq : ∀ {a b : Process N}, IsMax a → IsMax b → a = b := by
    intro a b ha hb
    exact le_antisymm (hb a) (ha b)
  let InvMsg : State N → Prop := fun st => ∀ m q : Process N, st.msg q = some m → q = succ m ∨ IsMax m
  let InvLead : State N → Prop := fun st => ∀ j : Process N, st.leader j = true → IsMax j
  have hmain : InvMsg s ∧ InvLead s := by
    induction hs with
    | init =>
        rename_i s0 hInit
        constructor
        · intro m q hq
          have hmsg : s0.msg q = none := congrFun hInit.1 q
          rw [hmsg] at hq
          cases hq
        · intro j hj
          have hlead : s0.leader j = false := congrFun hInit.2.2 j
          rw [hlead] at hj
          cases hj
    | step =>
        rename_i s' t' hs' hstep ih
        rcases hstep with hnext | heq
        · rcases hnext with ⟨i, hsi⟩
          rcases hsi with hsend | hrecv
          · -- Send
            constructor
            · intro m q hq
              by_cases hq_eq : q = succ i
              · subst q
                rw [hsend.2.2.1] at hq
                have hsome : some i = some m := by
                  simpa [Function.update_apply] using hq
                have hmi : i = m := Option.some.inj hsome
                left
                rw [hmi]
              · rw [hsend.2.2.1] at hq
                simp [Function.update_apply, hq_eq] at hq
                exact ih.1 m q hq
            · intro j hj
              rw [hsend.2.2.2.2] at hj
              exact ih.2 j hj
          · -- Receive
            rcases hrecv with ⟨m, hmi, hcase⟩
            rcases hcase with hfwd | hdisc | helec
            · -- forward
              constructor
              · intro m2 q hq
                rw [hfwd.2.2.1] at hq
                by_cases hq1 : q = succ i
                · subst q
                  have hsome : some m = some m2 := by
                    simpa [Function.update_apply] using hq
                  have hmm2 : m = m2 := Option.some.inj hsome
                  subst m2
                  have hfrom := ih.1 m i hmi
                  rcases hfrom with h1 | h1
                  · have hgt : i < m := hfwd.1
                    have hmgt : succ m < m := by
                      rw [h1] at hgt
                      exact hgt
                    right
                    exact hgt_succ m hmgt
                  · right
                    exact h1
                · have hq' : (Function.update s'.msg i none) q = some m2 := by
                    simpa [Function.update_apply, hq1] using hq
                  by_cases hq2 : q = i
                  · subst q
                    have hnone : none = some m2 := by
                      simpa [Function.update_apply] using hq'
                    cases hnone
                  · have hq'' : s'.msg q = some m2 := by
                      simpa [Function.update_apply, hq2] using hq'
                    exact ih.1 m2 q hq''
              · intro j hj
                rw [hfwd.2.2.2.2] at hj
                exact ih.2 j hj
            · -- discard
              constructor
              · intro m2 q hq
                rw [hdisc.2.1] at hq
                by_cases hqi : q = i
                · subst q
                  have hnone : none = some m2 := by
                    simpa [Function.update_apply] using hq
                  cases hnone
                · have hq' : s'.msg q = some m2 := by
                    simpa [Function.update_apply, hqi] using hq
                  exact ih.1 m2 q hq'
              · intro j hj
                rw [hdisc.2.2.2] at hj
                exact ih.2 j hj
            · -- elect
              constructor
              · intro m2 q hq
                rw [helec.2.2.1] at hq
                by_cases hqi : q = i
                · subst q
                  have hnone : none = some m2 := by
                    simpa [Function.update_apply] using hq
                  cases hnone
                · have hq' : s'.msg q = some m2 := by
                    simpa [Function.update_apply, hqi] using hq
                  exact ih.1 m2 q hq'
              · intro j hj
                rw [helec.2.1] at hj
                by_cases hji : j = i
                · subst j
                  have hmi' : s'.msg i = some i := by
                    rw [helec.1] at hmi
                    exact hmi
                  have hfrom := ih.1 i i hmi'
                  rcases hfrom with hsucc | hmax
                  · exact (hsucc_ne i hsucc.symm).elim
                  · exact hmax
                · have hj' : s'.leader j = true := by
                    simpa [Function.update_apply, hji] using hj
                  exact ih.2 j hj'
        · rw [heq]
          exact ih
  intro i j hij hlead
  have hi : IsMax i := hmain.2 i hlead.1
  have hj : IsMax j := hmain.2 j hlead.2
  exact hij (hmax_eq hi hj)

end LCR
