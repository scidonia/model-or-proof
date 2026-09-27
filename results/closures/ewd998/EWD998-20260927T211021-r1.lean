/-
EWD998 (Safra's termination detection) — the Lean model for Route B (protocol §2).

This is the idiomatic counterpart of `specs/tla/ewd998/EWD998.tla`, imported at pinned provenance with its
TLAPS proofs (`specs/tla/ewd998/`, and the publication-era revision in `specs/tla/ewd998-paper/`). It is
the **ring layer only**, which is the plan's ruling: the asynchronous termination-detection layer enters
the module solely at `TD == INSTANCE AsyncTerminationDetection`, a parse-time dependency referenced only by
`TDSpec`/`Refinement`, so the port is the five state variables and the five actions of the ring. The
statement-by-statement correspondence is audited in `docs/equivalence-ewd998.md` (protocol §4.1); the model
neither strengthens an assumption nor weakens the goal.

What this file states, and what it does not:

* The seed's theorem is the ring's **invariance** — `THEOREM Invariance == Init /\ [][Next]_vars => []Inv`
  (`EWD998_proof.tla:176`) — with no fairness. The module's `Spec` carries `WF_vars(System)` for the
  liveness theorem, which is a different claim and is not ported here.
* The seed states `Inv` and nothing else, as the plan rules. `TypeOK` is a proof-level strengthening the
  TLAPS proof inlines in its step case; it is carried here by the *types* of `State`, so it is a fact about
  the representation rather than a conjunct of the statement.
* `Termination` and `TerminationDetection` (the module's "main safety property") are *different*
  properties — grouped with the refinement theorem rather than with invariance — and are not stated here.

This file is the closure loop's **tier-2 seed** (plan D5): the theorem statement is the human's, the proof
is the loop's, and the `sorry` below is the seed's placeholder, not a result — the run is closed only when
the harness has observed it gone (protocol §8). The negative control will be `EWD998Mutant.lean`.
-/
import Mathlib

namespace EWD998

open scoped BigOperators

/-! ## The state -/

/-- The nodes — TLA+ `Node == 0 .. N-1`. `Fin N` is the same nodes in the same order. -/
abbrev Node (N : ℕ) := Fin N

/-- TLA+ `Color == {"white", "black"}`. -/
inductive Color where
  | white
  | black
  deriving DecidableEq

/-- TLA+ `Token == [pos : Node, q : Int, color : Color]`. -/
structure Token (N : ℕ) where
  /-- The node the token is at. -/
  pos : Node N
  /-- The count the token carries. -/
  q : ℤ
  /-- The token's colour. -/
  color : Color

/-- TLA+ `VARIABLES active, color, counter, pending, token`. TLA+'s `TypeOK` is carried by this type: the
two per-node predicates are `Bool`-valued, `pending` is a natural, `counter` an integer and the token a
structure of the right shapes, so no value of `State N` can violate it. -/
structure State (N : ℕ) where
  /-- Activation status of the nodes. -/
  active : Node N → Bool
  /-- Colour of the nodes. -/
  color : Node N → Color
  /-- Messages sent minus messages received, per node. TLA+ `counter \in [Node -> Int]`. -/
  counter : Node N → ℤ
  /-- Messages in transit to each node. TLA+ `pending \in [Node -> Nat]`. -/
  pending : Node N → ℕ
  /-- The token. -/
  token : Token N

variable {N : ℕ}

/-- The module's node `N-1`, the token's starting position: the predecessor of the ring's first node. A
node exists, so `N-1` is one (`hN` is the module's `ASSUME N \in Nat \ {0}`). -/
def lastNode (hN : 0 < N) : Node N := ⟨N - 1, by omega⟩

/-- The predecessor of a node, the position `PassToken` moves the token to. -/
def prevNode {N : ℕ} (i : Node N) : Node N := ⟨i.val - 1, by have := i.isLt; omega⟩


/-! ## The model -/

/-- TLA+ `Init`: every colour and activation status is arbitrary (`\in` is an unconstrained choice in the
module, so the Lean model constrains nothing there), both counters start empty, and the token starts at
node 0 with count 0 and colour black. `hN` is the module's `ASSUME N \in Nat \ {0}`, needed only because
the node `0` has to exist for the statement to be about anything. -/
def Init (hN : 0 < N) (s : State N) : Prop :=
  s.counter = (fun _ => 0) ∧
    s.pending = (fun _ => 0) ∧
    s.token.pos = ⟨0, hN⟩ ∧
    s.token.q = 0 ∧
    s.token.color = Color.black

/-- TLA+ `InitiateProbe` (Rules 1 + 5 + 6): with the token at node 0 and the previous round inconclusive,
the token restarts at node `N-1`, white and zeroed, and node 0 whitens. -/
def InitiateProbe (hN : 0 < N) (s t : State N) : Prop :=
  s.token.pos = ⟨0, hN⟩ ∧
    (s.token.color = Color.black ∨ s.color ⟨0, hN⟩ = Color.black ∨ s.counter ⟨0, hN⟩ + s.token.q > 0) ∧
    t.token = ⟨lastNode hN, 0, Color.white⟩ ∧
    t.color = Function.update s.color ⟨0, hN⟩ Color.white ∧
    s.active = t.active ∧
    s.counter = t.counter ∧
    s.pending = t.pending

/-- TLA+ `PassToken(i)` (Rules 2 + 4 + 7): a passive node holding the token passes it on, adding its own
count and blackening the token if it is black, and whitens itself. -/
def PassToken (i : Node N) (s t : State N) : Prop :=
  s.active i = false ∧
    s.token.pos = i ∧
    t.token = ⟨prevNode i, s.token.q + s.counter i,
                if s.color i = Color.black then Color.black else s.token.color⟩ ∧
    t.color = Function.update s.color i Color.white ∧
    s.active = t.active ∧
    s.counter = t.counter ∧
    s.pending = t.pending

/-- TLA+ `SendMsg(i)`: an active node sends one message to any other node, raising its own count and the
receiver's pending count. -/
def SendMsg (i : Node N) (s t : State N) : Prop :=
  s.active i = true ∧
    (∃ j : Node N, j ≠ i) ∧
    t.counter = Function.update s.counter i (s.counter i + 1) ∧
    t.pending = Function.update s.pending i (s.pending i + 1) ∧
    s.active = t.active ∧
    s.color = t.color ∧
    s.token = t.token

/-- TLA+ `RecvMsg(i)`: a node with a message in transit receives it — pending down, count down (Rule 0),
blackened (Rule 3) and activated. -/
def RecvMsg (i : Node N) (s t : State N) : Prop :=
  s.pending i > 0 ∧
    t.pending = Function.update s.pending i (s.pending i - 1) ∧
    t.counter = Function.update s.counter i (s.counter i - 1) ∧
    t.color = Function.update s.color i Color.black ∧
    t.active = Function.update s.active i true ∧
    s.token = t.token

/-- TLA+ `Deactivate(i)`: an active node becomes passive, changing nothing else. -/
def Deactivate (i : Node N) (s t : State N) : Prop :=
  s.active i = true ∧
    t.active = Function.update s.active i false ∧
    s.color = t.color ∧
    s.counter = t.counter ∧
    s.pending = t.pending ∧
    s.token = t.token

/-- TLA+ `System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)`. -/
def System (hN : 0 < N) (s t : State N) : Prop :=
  InitiateProbe hN s t ∨ ∃ i : Node N, i ≠ ⟨0, hN⟩ ∧ PassToken i s t

/-- TLA+ `Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)`. -/
def Environment (s t : State N) : Prop :=
  ∃ i : Node N, SendMsg i s t ∨ RecvMsg i s t ∨ Deactivate i s t

/-- TLA+ `Next == System \/ Environment`. -/
def Next (hN : 0 < N) (s t : State N) : Prop := System hN s t ∨ Environment s t

/-- TLA+ `[Next]_vars`. -/
def Step (hN : 0 < N) (s t : State N) : Prop := Next hN s t ∨ t = s

/-- The states admitted by TLA+ `Init /\ [][Next]_vars`, read as a state predicate — the invariance
reading, which is what `Invariance` proves and what the seed states. `Spec` additionally asserts
`WF_vars(System)`, which is the liveness hypothesis and is deliberately not carried here. -/
inductive Reachable (hN : 0 < N) : State N → Prop where
  /-- The initial states. -/
  | init {s} : Init hN s → Reachable hN s
  /-- The states one `[Next]_vars` step away from a reachable state. -/
  | step {s t} : Reachable hN s → Step hN s t → Reachable hN t

/-! ## `Inv` and its helpers -/

/-- TLA+ `B == Sum(pending, Node)`: the number of messages in flight. -/
def B (s : State N) : ℤ := ∑ i : Node N, (s.pending i : ℤ)

/-- TLA+ `Rng(a, b) == {i \in Node : a <= i /\ i <= b}`, the node interval the invariant's clauses speak
about. -/
def Rng (a b : ℕ) : Finset (Node N) := Finset.univ.filter fun i => a ≤ i.val ∧ i.val ≤ b

/-- TLA+ `Sum(counter, Rng(a, b))`, the interval's counted-message sum. -/
def counterSum (s : State N) (a b : ℕ) : ℤ := (Rng (N := N) a b).sum s.counter

/-- **Safra's inductive invariant**, `Inv` at `EWD998.tla:168-183`: the counted messages at each node and
the messages in transit are consistent (`P0`), and the four-way disjunction `P1`–`P4` that makes the
invariant inductive. The seed states this and nothing else. -/
def Inv (s : State N) : Prop :=
  -- P0: the in-flight count and the counted messages agree.
  B s = ∑ i : Node N, s.counter i ∧
    (-- P1: every node past the token's position is passive, and the token's count is the sum over them.
      ((∀ i : Node N, s.token.pos.val < i.val → s.active i = false) ∧
        (if s.token.pos.val = N - 1 then s.token.q = 0
         else s.token.q = counterSum s (s.token.pos.val + 1) (N - 1))) ∨
      -- P2: the prefix's counted messages plus the token's count is positive.
      counterSum s 0 s.token.pos.val + s.token.q > 0 ∨
      -- P3: some node in the prefix is black.
      (∃ i : Node N, i.val ≤ s.token.pos.val ∧ s.color i = Color.black) ∨
      -- P4: the token is black.
      s.token.color = Color.black)

/-! ## The theorem -/

/-- **Invariance**, in general (tier 2, protocol §2): every state reachable under `Init /\ [][Next]_vars`
satisfies Safra's inductive invariant, at every `N ≥ 1` — the TLA+ `Init /\ [][Next]_vars => []Inv`
(`EWD998_proof.tla:176`) under `ASSUME N \in Nat \ {0}` (`EWD998.tla:19`). No fairness is asserted: that
belongs to the liveness theorem the module proves separately. -/
theorem inv (hN : 1 ≤ N) (s : State N) (hs : Reachable (Nat.lt_of_lt_of_le Nat.zero_lt_one hN) s) : Inv s := by
  have hpos : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have sum_update_int : ∀ (i : Node N) (f : Node N → ℤ) (b : ℤ),
      (∑ j : Node N, Function.update f i b j) = ∑ j : Node N, f j + (b - f i) := by
    intro i f b
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    rw [Finset.sdiff_singleton_eq_erase]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    ring
  have sum_update_nat : ∀ (i : Node N) (f : Node N → ℕ) (b : ℕ),
      (∑ j : Node N, (Function.update f i b j : ℤ)) = ∑ j : Node N, (f j : ℤ) + ((b : ℤ) - (f i : ℤ)) := by
    intro i f b
    rw [show (∑ j : Node N, (Function.update f i b j : ℤ)) = ∑ j : Node N, Function.update (fun j => (f j : ℤ)) i (b : ℤ) j by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hji : j = i <;> simp [hji]]
    rw [sum_update_int]
  have rng_0_last : Rng (N := N) 0 (N - 1) = Finset.univ := by
    ext j
    simp [Rng]
    omega
  have rng_self : ∀ (i : Node N), Rng (N := N) i.val i.val = {i} := by
    intro i
    ext j
    simp only [Rng, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      apply Fin.ext
      omega
    · intro h
      subst j
      omega
  have rng_insert_left : ∀ {a b : ℕ} {i : Node N}, i.val = a → a ≤ b → Rng (N := N) a b = insert i (Rng (N := N) (a + 1) b) := by
    intro a b i ha hab
    ext j
    simp only [Rng, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases hji : j = i
      · left; exact hji
      · right
        have hjval : j.val ≠ a := by
          intro hja
          apply hji
          apply Fin.ext
          omega
        omega
    · intro h
      rcases h with hji | h
      · subst j; omega
      · omega
  have rng_insert_right : ∀ {a b : ℕ} {i : Node N}, i.val = b → a < b → Rng (N := N) a b = insert i (Rng (N := N) a (b - 1)) := by
    intro a b i hb hab
    ext j
    simp only [Rng, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases hji : j = i
      · left; exact hji
      · right
        have hjval : j.val ≠ b := by
          intro hjb
          apply hji
          apply Fin.ext
          omega
        omega
    · intro h
      rcases h with hji | h
      · subst j; omega
      · omega
  have rng_union_prefix_suffix : ∀ (p : ℕ), p ≤ N - 1 → Rng (N := N) 0 p ∪ Rng (N := N) (p + 1) (N - 1) = Finset.univ := by
    intro p hp
    ext j
    simp only [Rng, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h; trivial
    · intro h
      omega
  have rng_disjoint_prefix_suffix : ∀ (p : ℕ), Disjoint (Rng (N := N) 0 p) (Rng (N := N) (p + 1) (N - 1)) := by
    intro p
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb heq
    subst b
    simp [Rng] at ha hb
    omega
  have counterSum_all : ∀ (s : State N), counterSum s 0 (N - 1) = ∑ j : Node N, s.counter j := by
    intro s
    rw [counterSum, rng_0_last]
  have counterSum_split : ∀ (s : State N) {p : ℕ}, (hp : p ≤ N - 1) → counterSum s 0 p + counterSum s (p + 1) (N - 1) = ∑ j : Node N, s.counter j := by
    intro s p hp
    unfold counterSum
    rw [← rng_union_prefix_suffix p hp]
    rw [Finset.sum_union (rng_disjoint_prefix_suffix p)]
  have counterSum_singleton : ∀ (s : State N) {a : ℕ} {i : Node N}, (ha : i.val = a) → counterSum s a a = s.counter i := by
    intro s a i ha
    subst a
    unfold counterSum
    rw [rng_self]
    rw [Finset.sum_singleton]
  have counterSum_insert_left : ∀ (s : State N) {a b : ℕ} {i : Node N}, (ha : i.val = a) → (hab : a ≤ b) → counterSum s a b = s.counter i + counterSum s (a + 1) b := by
    intro s a b i ha hab
    unfold counterSum
    rw [rng_insert_left ha hab]
    rw [Finset.sum_insert (by simp [Rng]; omega)]
  have counterSum_insert_right : ∀ (s : State N) {a b : ℕ} {i : Node N}, (hb : i.val = b) → (hab : a < b) → counterSum s a b = counterSum s a (b - 1) + s.counter i := by
    intro s a b i hb hab
    unfold counterSum
    rw [rng_insert_right hb hab]
    rw [Finset.sum_insert (by simp [Rng]; omega)]
    ring
  have counterSum_congr : ∀ {s t : State N} {a b : ℕ}, t.counter = s.counter → counterSum t a b = counterSum s a b := by
    intro s t a b h
    unfold counterSum
    rw [h]
  have B_pos_of_pending : ∀ {s : State N} {i : Node N}, s.pending i > 0 → 0 < B s := by
    intro s i h
    unfold B
    have hi : 1 ≤ (s.pending i : ℤ) := by exact_mod_cast (Nat.succ_le_of_lt h)
    have hle : (s.pending i : ℤ) ≤ ∑ j : Node N, (s.pending j : ℤ) := by
      have hsf := Finset.single_le_sum (s := (Finset.univ : Finset (Node N)))
        (f := fun j : Node N => (s.pending j : ℤ))
        (fun j hj => by exact_mod_cast (Nat.zero_le (s.pending j))) (Finset.mem_univ i)
      simpa using hsf
    omega
  have inv_init : ∀ {s : State N}, Init hpos s → Inv s := by
    intro s h
    rcases h with ⟨hc, hp, htok, hq, hcol⟩
    unfold Inv
    constructor
    · unfold B
      rw [hp, hc]
      simp
    · right; right; right
      exact hcol
  have inv_ip : ∀ {s t : State N}, InitiateProbe hpos s t → Inv s → Inv t := by
    intro s t h ih
    rcases h with ⟨hp0, hpre, htok, hcol, hact, hcnt, hpend⟩
    rcases ih with ⟨hp0s, hdisj⟩
    unfold Inv
    constructor
    · unfold B
      rw [← hpend, ← hcnt]
      exact hp0s
    · left
      constructor
      · intro j hj
        have hval : t.token.pos.val = N - 1 := by rw [htok]; rfl
        rw [hval] at hj
        omega
      · have hval : t.token.pos.val = N - 1 := by rw [htok]; rfl
        rw [hval]
        have hq : t.token.q = 0 := by rw [htok]
        rw [hq]
        simp
  have inv_pass : ∀ {s t : State N} {i : Node N}, i ≠ ⟨0, hpos⟩ → PassToken i s t → Inv s → Inv t := by
    intro s t i hi0 h ih
    rcases h with ⟨hpassive, hpos_eq, htok, hcol, hact, hcnt, hpend⟩
    rcases ih with ⟨hp0s, hdisj⟩
    have hi_val : i.val ≠ 0 := by
      intro hval
      exact hi0 (Fin.ext hval)
    have hi_pos : 0 < i.val := Nat.pos_iff_ne_zero.mpr hi_val
    have htp : t.token.pos.val = i.val - 1 := by rw [htok]; rfl
    have htq : t.token.q = s.token.q + s.counter i := by rw [htok]
    have htc : t.token.color = (if s.color i = Color.black then Color.black else s.token.color) := by rw [htok]
    unfold Inv
    constructor
    · unfold B
      rw [← hpend, ← hcnt]
      exact hp0s
    · rcases hdisj with hp1 | hp2 | hp3 | hp4
      · left
        constructor
        · intro j hj
          rw [htp] at hj
          rw [← hact]
          by_cases hji : j = i
          · subst j
            exact hpassive
          · apply hp1.1
            rw [hpos_eq]
            have hjval_ne : j.val ≠ i.val := by intro h; exact hji (Fin.ext h)
            omega
        · rw [htp, htq]
          rw [counterSum_congr hcnt.symm]
          have hcond : i.val - 1 ≠ N - 1 := by omega
          simp [hcond]
          have hadd : i.val - 1 + 1 = i.val := by omega
          rw [hadd]
          rw [hpos_eq] at hp1
          by_cases hlast : i.val = N - 1
          · have hq0 : s.token.q = 0 := by simpa [hlast] using hp1.2
            have hsingle : counterSum s (N - 1) (N - 1) = s.counter i := counterSum_singleton s (ha := hlast)
            rw [hq0, hlast, hsingle]
            ring
          · have hq : s.token.q = counterSum s (i.val + 1) (N - 1) := by
              simpa [hlast] using hp1.2
            have hsplit : counterSum s i.val (N - 1) = s.counter i + counterSum s (i.val + 1) (N - 1) :=
              counterSum_insert_left s (ha := rfl) (hab := by omega)
            rw [hq, hsplit]
            ring
      · right; left
        rw [hpos_eq] at hp2
        rw [htp, htq]
        rw [counterSum_congr hcnt.symm]
        have hsplit : counterSum s 0 i.val = counterSum s 0 (i.val - 1) + s.counter i :=
          counterSum_insert_right s (hb := rfl) (hab := hi_pos)
        have hgoal : counterSum s 0 (i.val - 1) + (s.token.q + s.counter i) = counterSum s 0 i.val + s.token.q := by
          calc
            counterSum s 0 (i.val - 1) + (s.token.q + s.counter i)
                = (counterSum s 0 (i.val - 1) + s.counter i) + s.token.q := by ring
            _ = counterSum s 0 i.val + s.token.q := by rw [← hsplit]
        rw [hgoal]
        exact hp2
      · rcases hp3 with ⟨j, hjle, hjcol⟩
        by_cases hji : j = i
        · right; right; right
          subst j
          rw [htc]
          simp [hjcol]
        · right; right; left
          refine ⟨j, ?_, ?_⟩
          · rw [hpos_eq] at hjle
            have hjval_ne : j.val ≠ i.val := by intro h; exact hji (Fin.ext h)
            rw [htp]
            omega
          · rw [hcol]
            simp [hji, hjcol]
      · right; right; right
        rw [htc]
        by_cases hcol : s.color i = Color.black <;> simp [hcol, hp4]
  have inv_send : ∀ {s t : State N} {i : Node N}, SendMsg i s t → Inv s → Inv t := by
    intro s t i h ih
    rcases h with ⟨hact, hex, hcnt, hpend, hactEq, hcolEq, htokEq⟩
    rcases ih with ⟨hp0s, hdisj⟩
    unfold Inv
    constructor
    · unfold B
      rw [hpend, hcnt]
      rw [sum_update_nat, sum_update_int]
      have hb1 : ((s.pending i + 1 : ℕ) : ℤ) - (s.pending i : ℤ) = 1 := by omega
      have hc1 : (s.counter i + 1) - s.counter i = 1 := by ring
      rw [hb1, hc1]
      have hbase : ∑ j : Node N, (s.pending j : ℤ) = ∑ j : Node N, s.counter j := by
        simpa [B] using hp0s
      rw [hbase]
    · rcases hdisj with hp1 | hp2 | hp3 | hp4
      · have hile : i.val ≤ s.token.pos.val := by
          by_contra hgt
          have hlt : s.token.pos.val < i.val := by omega
          have hpass : s.active i = false := hp1.1 i hlt
          rw [hact] at hpass
          simp at hpass
        have hnot : i ∉ Rng (N := N) (s.token.pos.val + 1) (N - 1) := by
          simp [Rng]
          omega
        have hcs : counterSum t (s.token.pos.val + 1) (N - 1) = counterSum s (s.token.pos.val + 1) (N - 1) := by
          unfold counterSum
          rw [hcnt]
          rw [Finset.sum_update_of_notMem hnot]
        left
        constructor
        · intro j hj
          have htp : t.token = s.token := htokEq.symm
          rw [htp] at hj
          rw [← hactEq]
          exact hp1.1 j hj
        · have htp : t.token = s.token := htokEq.symm
          rw [htp]
          simpa [hcs] using hp1.2
      · right; left
        have htp : t.token = s.token := htokEq.symm
        rw [htp]
        by_cases hle : i.val ≤ s.token.pos.val
        · have hmem : i ∈ Rng (N := N) 0 s.token.pos.val := by
            simp [Rng]
            omega
          have hcs : counterSum t 0 s.token.pos.val = counterSum s 0 s.token.pos.val + 1 := by
            unfold counterSum
            rw [hcnt]
            rw [Finset.sum_update_of_mem hmem]
            rw [Finset.sdiff_singleton_eq_erase]
            rw [Finset.sum_erase_eq_sub hmem]
            ring
          rw [hcs]
          omega
        · have hnot : i ∉ Rng (N := N) 0 s.token.pos.val := by
            simp [Rng]
            omega
          have hcs : counterSum t 0 s.token.pos.val = counterSum s 0 s.token.pos.val := by
            unfold counterSum
            rw [hcnt]
            rw [Finset.sum_update_of_notMem hnot]
          rw [hcs]
          exact hp2
      · right; right; left
        rcases hp3 with ⟨j, hjle, hjcol⟩
        refine ⟨j, ?_, ?_⟩
        · rw [htokEq.symm]
          exact hjle
        · rw [hcolEq.symm]
          exact hjcol
      · right; right; right
        rw [htokEq.symm]
        exact hp4
  have inv_recv : ∀ {s t : State N} {i : Node N}, RecvMsg i s t → Inv s → Inv t := by
    intro s t i h ih
    rcases h with ⟨hpend_i, hpend, hcnt, hcol, hact, htok⟩
    rcases ih with ⟨hp0s, hdisj⟩
    unfold Inv
    constructor
    · unfold B
      rw [hpend, hcnt]
      rw [sum_update_nat, sum_update_int]
      have hb : ((s.pending i - 1 : ℕ) : ℤ) - (s.pending i : ℤ) = -1 := by
        rw [Nat.cast_pred (R := ℤ) hpend_i]
        ring
      have hc : (s.counter i - 1) - s.counter i = -1 := by ring
      rw [hb, hc]
      have hbase : ∑ j : Node N, (s.pending j : ℤ) = ∑ j : Node N, s.counter j := by
        simpa [B] using hp0s
      rw [hbase]
    · by_cases hle : i.val ≤ s.token.pos.val
      · right; right; left
        refine ⟨i, ?_, ?_⟩
        · rw [htok.symm]
          exact hle
        · rw [hcol]
          simp
      · have hnot_prefix : i ∉ Rng (N := N) 0 s.token.pos.val := by
          simp [Rng]
          omega
        have hcs_prefix : counterSum t 0 s.token.pos.val = counterSum s 0 s.token.pos.val := by
          unfold counterSum
          rw [hcnt]
          rw [Finset.sum_update_of_notMem hnot_prefix]
        rcases hdisj with hp1 | hp2 | hp3 | hp4
        · have hP2s : counterSum s 0 s.token.pos.val + s.token.q > 0 := by
            have hBpos : 0 < B s := B_pos_of_pending hpend_i
            have hsum : B s = ∑ j : Node N, s.counter j := hp0s
            by_cases hlast : s.token.pos.val = N - 1
            · have hq0 : s.token.q = 0 := by simpa [hlast] using hp1.2
              rw [hq0]
              have hall : counterSum s 0 (N - 1) = ∑ j : Node N, s.counter j := counterSum_all s
              rw [hlast, hall]
              rw [← hsum]
              omega
            · have hq : s.token.q = counterSum s (s.token.pos.val + 1) (N - 1) := by
                simpa [hlast] using hp1.2
              rw [hq]
              have hsplit := counterSum_split (s := s) (p := s.token.pos.val) (hp := by omega)
              rw [hsplit]
              rw [← hsum]
              omega
          right; left
          rw [htok.symm]
          rw [hcs_prefix]
          exact hP2s
        · right; left
          rw [htok.symm]
          rw [hcs_prefix]
          exact hp2
        · right; right; left
          rcases hp3 with ⟨j, hjle, hjcol⟩
          refine ⟨j, ?_, ?_⟩
          · rw [htok.symm]
            exact hjle
          · rw [hcol]
            have hji : j ≠ i := by
              intro hj
              subst j
              omega
            simp [hji, hjcol]
        · right; right; right
          rw [htok.symm]
          exact hp4
  have inv_deact : ∀ {s t : State N} {i : Node N}, Deactivate i s t → Inv s → Inv t := by
    intro s t i h ih
    rcases h with ⟨hact, hact', hcol, hcnt, hpend, htok⟩
    rcases ih with ⟨hp0s, hdisj⟩
    unfold Inv
    constructor
    · unfold B
      rw [← hpend, ← hcnt]
      exact hp0s
    · rcases hdisj with hp1 | hp2 | hp3 | hp4
      · have hile : i.val ≤ s.token.pos.val := by
          by_contra hgt
          have hlt : s.token.pos.val < i.val := by omega
          have hpass : s.active i = false := hp1.1 i hlt
          rw [hact] at hpass
          simp at hpass
        left
        constructor
        · intro j hj
          rw [htok.symm] at hj
          rw [hact']
          by_cases hji : j = i
          · subst j
            simp
          · simp [hji]
            apply hp1.1 j hj
        · rw [htok.symm]
          simpa [counterSum_congr hcnt.symm] using hp1.2
      · right; left
        rw [htok.symm]
        rw [counterSum_congr hcnt.symm]
        exact hp2
      · right; right; left
        rcases hp3 with ⟨j, hjle, hjcol⟩
        refine ⟨j, ?_, ?_⟩
        · rw [htok.symm]
          exact hjle
        · rw [hcol.symm]
          exact hjcol
      · right; right; right
        rw [htok.symm]
        exact hp4
  induction hs with
  | init hInit => exact inv_init hInit
  | step hReach hStep ih =>
      rcases hStep with hNext | hEq
      · rcases hNext with hSys | hEnv
        · rcases hSys with hIP | hPass
          · exact inv_ip hIP ih
          · rcases hPass with ⟨i, hi0, hpass⟩
            exact inv_pass hi0 hpass ih
        · rcases hEnv with ⟨i, hAction⟩
          rcases hAction with hSend | hRecv | hDeact
          · exact inv_send hSend ih
          · exact inv_recv hRecv ih
          · exact inv_deact hDeact ih
      · rw [hEq]
        exact ih

end EWD998
