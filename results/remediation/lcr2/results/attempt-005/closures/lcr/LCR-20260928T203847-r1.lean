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
  let top : Process N := ⟨N - 1, Nat.sub_one_lt (by omega : N ≠ 0)⟩
  have hsucc_ne_self : ∀ i : Process N, succ i ≠ i := by
    intro i h
    have hval : (i.val + 1) % N = i.val := by
      simpa [succ] using congrArg Fin.val h
    have hlt : i.val < N := i.isLt
    have hcases : i.val + 1 < N ∨ i.val + 1 = N := by omega
    rcases hcases with hlt1 | heq
    · have hm : (i.val + 1) % N = i.val + 1 := Nat.mod_eq_of_lt hlt1
      rw [hm] at hval
      omega
    · have hm : (i.val + 1) % N = 0 := by
        rw [heq]
        exact Nat.mod_self N
      rw [hm] at hval
      omega
  have hsucc_gt_of_ne_top : ∀ m : Process N, m ≠ top → succ m > m := by
    intro m hm
    have hmval : m.val < N := m.isLt
    have hmne : m.val ≠ N - 1 := by
      intro hval
      apply hm
      ext
      exact hval
    have hlt : m.val + 1 < N := by omega
    have hsucc : (succ m).val = m.val + 1 := by
      simp [succ, Nat.mod_eq_of_lt hlt]
    simpa [Fin.lt_def, hsucc] using (Nat.lt_succ_self m.val)
  have hmsg_gt_top : ∀ m i : Process N, m > i → m = top ∨ i = succ m → m = top := by
    intro m i hgt hmold
    rcases hmold with hmtop | hisucc
    · exact hmtop
    · have hsucc_gt : succ m < m := by
        rwa [hisucc] at hgt
      by_contra hmne
      exact (lt_asymm hsucc_gt) (hsucc_gt_of_ne_top m hmne)
  have hmain : ∀ s : State N, Reachable s →
      UniqueLeader s ∧ (∀ j : Process N, s.leader j = true → j = top) ∧
        (∀ m j : Process N, s.msg j = some m → m = top ∨ j = succ m) := by
    intro s hs
    induction hs with
    | init hinit =>
        rename_i s0
        rcases hinit with ⟨hmsg, hsent, hleader⟩
        constructor
        · intro i j hij hboth
          rw [hleader] at hboth
          simp at hboth
        · constructor
          · intro j hj
            rw [hleader] at hj
            simp at hj
          · intro m j hmj
            rw [hmsg] at hmj
            simp at hmj
    | step =>
        rename_i s0 t0 hs0 hst ih
        rcases ih with ⟨hUnique, hLeader, hMsg⟩
        rcases hst with hNext | hEq
        · rcases hNext with ⟨i, hstep⟩
          rcases hstep with hSend | hRecv
          · rcases hSend with ⟨hsent, hsucc, hmsg_t, hsent_t, hlead_t⟩
            constructor
            · intro a b hab hboth
              rw [hlead_t] at hboth
              exact hUnique a b hab hboth
            constructor
            · intro j hj
              rw [hlead_t] at hj
              exact hLeader j hj
            · intro m j hmj
              rw [hmsg_t] at hmj
              by_cases hji : j = succ i
              · have hEqopt : some i = some m := by
                  simpa [hji] using hmj
                have hmi : i = m := Option.some.inj hEqopt
                right
                rw [← hmi]
                exact hji
              · have hmj0 : s0.msg j = some m := by
                  simpa [hji] using hmj
                exact hMsg m j hmj0
          · rcases hRecv with ⟨m, hm_i, hcase⟩
            rcases hcase with hFwd | hDisc | hElec
            · rcases hFwd with ⟨hgt, hsucc, hmsg_t, hsent_t, hlead_t⟩
              constructor
              · intro a b hab hboth
                rw [hlead_t] at hboth
                exact hUnique a b hab hboth
              constructor
              · intro j hj
                rw [hlead_t] at hj
                exact hLeader j hj
              · intro m' j hmj
                rw [hmsg_t] at hmj
                by_cases hji : j = succ i
                · have hEqopt : some m = some m' := by
                    simpa [hji] using hmj
                  have hmm' : m = m' := Option.some.inj hEqopt
                  have hmtop : m = top := hmsg_gt_top m i hgt (hMsg m i hm_i)
                  left
                  rw [← hmm']
                  exact hmtop
                · by_cases hji' : j = i
                  · have hnone : none = some m' := by
                      simpa [Function.update, hji', (hsucc_ne_self i).symm] using hmj
                    cases hnone
                  · have hmj0 : s0.msg j = some m' := by
                      simpa [hji, hji'] using hmj
                    exact hMsg m' j hmj0
            · rcases hDisc with ⟨hlt, hmsg_t, hsent_t, hlead_t⟩
              constructor
              · intro a b hab hboth
                rw [hlead_t] at hboth
                exact hUnique a b hab hboth
              constructor
              · intro j hj
                rw [hlead_t] at hj
                exact hLeader j hj
              · intro m' j hmj
                rw [hmsg_t] at hmj
                by_cases hji : j = i
                · have hnone : none = some m' := by
                    simpa [hji] using hmj
                  cases hnone
                · have hmj0 : s0.msg j = some m' := by
                    simpa [hji] using hmj
                  exact hMsg m' j hmj0
            · rcases hElec with ⟨hmi, hlead_t, hmsg_t, hsent_t⟩
              have hitop : i = top := by
                have hmold : m = top ∨ i = succ m := hMsg m i hm_i
                rcases hmold with hmtop | hisucc
                · simpa [hmi] using hmtop
                · have hself : i = succ i := by
                    simpa [hmi] using hisucc
                  exfalso
                  exact (hsucc_ne_self i) hself.symm
              have hleadert : ∀ j : Process N, t0.leader j = true → j = top := by
                intro j hj
                rw [hlead_t] at hj
                by_cases hji : j = i
                · rw [hji, hitop]
                · have hj0 : s0.leader j = true := by
                    simpa [hji] using hj
                  exact hLeader j hj0
              constructor
              · intro a b hab hboth
                exact hab (by rw [hleadert a hboth.1, hleadert b hboth.2])
              constructor
              · exact hleadert
              · intro m' j hmj
                rw [hmsg_t] at hmj
                by_cases hji : j = i
                · have hnone : none = some m' := by
                    simpa [hji] using hmj
                  cases hnone
                · have hmj0 : s0.msg j = some m' := by
                    simpa [hji] using hmj
                  exact hMsg m' j hmj0
        · rw [hEq]
          exact ⟨hUnique, hLeader, hMsg⟩
  exact (hmain s hs).1
end LCR
