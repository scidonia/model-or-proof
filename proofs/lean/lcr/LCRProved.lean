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
  let lift : Process N → Process N → ℕ := fun m p => if m.val < p.val then p.val else p.val + N
  let between : Process N → Process N → Process N → Prop := fun m k p => p ≠ m ∧ lift m p < lift m k
  have succ_ne : ∀ i : Process N, succ i ≠ i := by
    intro i h
    have hval : i.val = (i.val + 1) % N := by
      have : i.val = (succ i).val := by rw [h]
      simpa [succ] using this
    have hiN : i.val < N := i.isLt
    have hle : i.val + 1 ≤ N := by omega
    by_cases hlt : i.val + 1 < N
    · have hm : (i.val + 1) % N = i.val + 1 := Nat.mod_eq_of_lt hlt
      omega
    · have heq : i.val + 1 = N := by omega
      have hm : (i.val + 1) % N = 0 := by rw [heq, Nat.mod_self]
      omega
  have lift_mem : ∀ (m p : Process N), p ≠ m → m.val < lift m p ∧ lift m p < m.val + N := by
    intro m p hp
    unfold lift
    by_cases h : m.val < p.val
    · simp [h]
      omega
    · have hpn : p.val ≠ m.val := by intro hc; apply hp; exact Fin.ext hc
      have hpl : p.val < m.val := by omega
      simp [h]
      constructor
      · omega
      · omega
  have lift_eq_of_lift_eq : ∀ {m p q : Process N}, lift m p = lift m q → p = q := by
    intro m p q h
    apply Fin.ext
    by_cases hmp : m.val < p.val <;> by_cases hmq : m.val < q.val
    · unfold lift at h
      rw [if_pos hmp, if_pos hmq] at h
      omega
    · unfold lift at h
      rw [if_pos hmp, if_neg hmq] at h
      omega
    · unfold lift at h
      rw [if_neg hmp, if_pos hmq] at h
      omega
    · unfold lift at h
      rw [if_neg hmp, if_neg hmq] at h
      omega
  have lift_self : ∀ m : Process N, lift m m = m.val + N := by
    intro m
    unfold lift
    simp
  have lift_of_gt : ∀ {m i : Process N}, m > i → lift m i = i.val + N := by
    intro m i h
    unfold lift
    have hi : i.val < m.val := h
    have hnot : ¬ m.val < i.val := by omega
    simp [hnot]
  have succ_val_of_gt : ∀ {m i : Process N}, m > i → (succ i).val = i.val + 1 := by
    intro m i h
    have hi : i.val < m.val := h
    have h2 : i.val + 1 < N := by omega
    simp [succ, Nat.mod_eq_of_lt h2]
  have lift_succ_of_gt : ∀ {m i : Process N}, m > i → lift m (succ i) = lift m i + 1 := by
    intro m i h
    have hs : (succ i).val = i.val + 1 := succ_val_of_gt h
    have hi : i.val < m.val := h
    have hnot : ¬ m.val < (succ i).val := by rw [hs]; omega
    have hnot2 : ¬ m.val < i.val := by omega
    unfold lift
    rw [if_neg hnot, if_neg hnot2]
    rw [hs]
    omega
  have between_succ_of_gt : ∀ {m i p : Process N}, m > i →
      (∀ q, between m i q → m > q) → between m (succ i) p → m > p := by
    intro m i p h hinc hp
    rcases hp with ⟨hpne, hlift⟩
    by_cases hpi : p = i
    · subst p
      exact h
    · have hb : between m i p := by
        constructor
        · exact hpne
        · have hls : lift m (succ i) = lift m i + 1 := lift_succ_of_gt h
          rw [hls] at hlift
          have hli : lift m i = i.val + N := lift_of_gt h
          rw [hli] at hlift
          have hne_lift : lift m p ≠ i.val + N := by
            intro heq
            apply hpi
            have heq' : lift m p = lift m i := by rw [hli]; exact heq
            exact lift_eq_of_lift_eq heq'
          omega
      exact hinc p hb
  have lift_succ_self : ∀ i : Process N, lift i (succ i) = i.val + 1 := by
    intro i
    unfold lift
    by_cases h : i.val < (succ i).val
    · have hs : (succ i).val = i.val + 1 := by
        have hsucc : (succ i).val = (i.val + 1) % N := rfl
        by_contra hc
        have hle : i.val + 1 ≤ N := by omega
        have hlt' : ¬ i.val + 1 < N := by
          intro hlt'
          have hmod : (i.val + 1) % N = i.val + 1 := Nat.mod_eq_of_lt hlt'
          apply hc
          rw [hsucc, hmod]
        have heq : i.val + 1 = N := by omega
        have : (succ i).val = 0 := by simp [succ, heq]
        omega
      simp [h, hs]
    · have hs : (succ i).val + N = i.val + 1 := by
        have hsucc : (succ i).val = (i.val + 1) % N := rfl
        have hle : i.val + 1 ≤ N := by omega
        by_cases hlt : i.val + 1 < N
        · have hm : (i.val + 1) % N = i.val + 1 := Nat.mod_eq_of_lt hlt
          have : i.val < (succ i).val := by rw [hsucc, hm]; omega
          omega
        · have heq : i.val + 1 = N := by omega
          have hm : (i.val + 1) % N = 0 := by rw [heq, Nat.mod_self]
          rw [hsucc, hm]
          omega
      simp [h, hs]
  have lift_ge_succ : ∀ (i p : Process N), p ≠ i → i.val + 1 ≤ lift i p := by
    intro i p hp
    unfold lift
    by_cases h : i.val < p.val
    · simp [h]
    · have hpn : p.val ≠ i.val := by intro hc; apply hp; exact Fin.ext hc
      have hpl : p.val < i.val := by omega
      simp [h]
      omega
  have no_between_succ : ∀ {i : Process N} (p : Process N), ¬ between i (succ i) p := by
    intro i p hp
    rcases hp with ⟨hpne, hlift⟩
    have hge := lift_ge_succ i p hpne
    have heq := lift_succ_self i
    rw [heq] at hlift
    omega
  let MsgInv : State N → Prop := fun s =>
    ∀ k m, s.msg k = some m → ∀ p, between m k p → m > p
  let LeadInv : State N → Prop := fun s =>
    ∀ i, s.leader i = true → ∀ j, j ≠ i → i > j
  have msg_inv : ∀ s, Reachable s → MsgInv s := by
    intro s0 hs0
    induction hs0 with
    | init =>
        rename_i sinit hinit
        intro k m hmsg p hp
        have hnone : sinit.msg k = none := by simpa [hinit.1]
        rw [hnone] at hmsg
        cases hmsg
    | step =>
        rename_i s' t' hprev hstep ih
        intro k m hmsg p hp
        rcases hstep with hnext | hstutter
        · rcases hnext with ⟨i, hsend | hrecv⟩
          · rcases hsend with ⟨hsi, hsn, htmsg, htsent, htleader⟩
            by_cases hk : k = succ i
            · subst k
              rw [htmsg] at hmsg
              simp [Function.update] at hmsg
              have hmi : m = i := hmsg.symm
              subst m
              exfalso
              exact no_between_succ p hp
            · have hmsg' : s'.msg k = some m := by
                rw [htmsg] at hmsg
                simp [Function.update, hk] at hmsg
                exact hmsg
              exact ih k m hmsg' p hp
          · rcases hrecv with ⟨m0, hmsgi, hcase⟩
            rcases hcase with hfwd | hdisc_or_elec
            · rcases hfwd with ⟨hmgt, hsn, htmsg, htsent, htleader⟩
              by_cases hki : k = i
              · subst k
                have hnone : t'.msg i = none := by
                  rw [htmsg]
                  simp [Function.update, (succ_ne i).symm]
                rw [hnone] at hmsg
                cases hmsg
              · by_cases hks : k = succ i
                · subst k
                  rw [htmsg] at hmsg
                  simp [Function.update] at hmsg
                  have hmm0 : m = m0 := hmsg.symm
                  subst m
                  exact between_succ_of_gt hmgt (ih i m0 hmsgi) hp
                · have hmsg' : s'.msg k = some m := by
                    rw [htmsg] at hmsg
                    simp [Function.update, hki, hks] at hmsg
                    exact hmsg
                  exact ih k m hmsg' p hp
            · rcases hdisc_or_elec with hdisc | helec
              · rcases hdisc with ⟨hmlt, htmsg, htsent, htleader⟩
                by_cases hki : k = i
                · subst k
                  have hnone : t'.msg i = none := by
                    rw [htmsg]
                    simp [Function.update]
                  rw [hnone] at hmsg
                  cases hmsg
                · have hmsg' : s'.msg k = some m := by
                    rw [htmsg] at hmsg
                    simp [Function.update, hki] at hmsg
                    exact hmsg
                  exact ih k m hmsg' p hp
              · rcases helec with ⟨hmi, htleader, htmsg, htsent⟩
                by_cases hki : k = i
                · subst k
                  have hnone : t'.msg i = none := by
                    rw [htmsg]
                    simp [Function.update]
                  rw [hnone] at hmsg
                  cases hmsg
                · have hmsg' : s'.msg k = some m := by
                    rw [htmsg] at hmsg
                    simp [Function.update, hki] at hmsg
                    exact hmsg
                  exact ih k m hmsg' p hp
        · subst t'
          exact ih k m hmsg p hp
  have lead_inv : ∀ s, Reachable s → LeadInv s := by
    intro s0 hs0
    induction hs0 with
    | init =>
        rename_i sinit hinit
        intro i hli j hij
        have hfalse : sinit.leader i = false := by simpa [hinit.2.2]
        rw [hfalse] at hli
        cases hli
    | step =>
        rename_i s' t' hprev hstep ih
        intro a hla b hab
        rcases hstep with hnext | hstutter
        · rcases hnext with ⟨i, hsend | hrecv⟩
          · rcases hsend with ⟨hsi, hsn, htmsg, htsent, htleader⟩
            rw [htleader] at hla
            exact ih a hla b hab
          · rcases hrecv with ⟨m0, hmsgi, hcase⟩
            rcases hcase with hfwd | hdisc_or_elec
            · rcases hfwd with ⟨hmgt, hsn, htmsg, htsent, htleader⟩
              rw [htleader] at hla
              exact ih a hla b hab
            · rcases hdisc_or_elec with hdisc | helec
              · rcases hdisc with ⟨hmlt, htmsg, htsent, htleader⟩
                rw [htleader] at hla
                exact ih a hla b hab
              · rcases helec with ⟨hmi, htleader, htmsg, htsent⟩
                by_cases hai : a = i
                · subst a
                  have hmsgi' : s'.msg i = some i := by rw [hmi] at hmsgi; exact hmsgi
                  have himax : ∀ q, q ≠ i → i > q := by
                    intro q hq
                    have hb : between i i q := by
                      constructor
                      · exact hq
                      · rw [lift_self i]
                        exact (lift_mem i q hq).2
                    exact msg_inv s' hprev i i hmsgi' q hb
                  exact himax b hab
                · have hla' : s'.leader a = true := by
                    rw [htleader] at hla
                    simpa [Function.update, hai] using hla
                  exact ih a hla' b hab
        · subst t'
          exact ih a hla b hab
  intro i j hij hboth
  rcases hboth with ⟨hli, hlj⟩
  have hi_gt : i > j := lead_inv s hs i hli j (Ne.symm hij)
  have hj_gt : j > i := lead_inv s hs j hlj i hij
  have h1 : j.val < i.val := hi_gt
  have h2 : i.val < j.val := hj_gt
  omega

end LCR
