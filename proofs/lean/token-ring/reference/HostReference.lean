/-
A **host-side reference proof** of `TokenRing.mutex` (the tier-2 seed), written by the conducting
session on 2026-09-26 in one pass plus two elaboration fixes, purely as a control.

Status: **not the loop's work, and not input to the loop.** It exists to answer one question — is the
seed closable at all, and if so how hard is it really? It is: 67 lines, no helper lemmas, and *no
`ringSucc` arithmetic*, because the strengthening `Mutex s ∧ ∀ i, pc i = crit → token = i` *implies*
`Mutex` — two critical nodes would both hold the token, hence be equal (`Finset.card_le_one`). That is
the strategic move the closure loop kept missing: it attacked `Mutex` directly, which walks into goals
like `⊢ ringSucc w = i` that are not provable on their own.

`lake env lean` on this file exits 0 with no `sorry`. Do not place it anywhere the loop's prompt could
read it: the loop must find a proof, not copy one.
-/

import TokenRing

namespace TokenRing

theorem mutex_mine (N : ℕ) (hN : 2 ≤ N) (s : State N) (hs : Reachable hN s) : Mutex s :=
  (inv_mine N hN s hs).1
where
  inv_mine : ∀ (N : ℕ) (hN : 2 ≤ N) (s : State N), Reachable hN s →
      Mutex s ∧ ∀ i : Node N, s.pc i = Phase.crit → s.token = i := by
    intro N hN s hs
    induction hs with
    | init h =>
        refine ⟨?_, ?_⟩
        · simp [Mutex, h.2]
        · intro i hi; rw [h.2] at hi; simp at hi
    | step =>
        rename_i s t hs hstep ih
        rcases hstep with hnext | heq
        · rcases hnext with ⟨i, hreq | hent | hrel⟩
          · rcases hreq with ⟨hidle, hpc, htok⟩
            have hcrit : ∀ j : Node N, t.pc j = Phase.crit → t.token = j := by
              intro j hj
              rw [hpc] at hj
              by_cases hji : j = i
              · subst hji; simp [hidle] at hj
              · simp [Function.update, hji] at hj
                rw [htok]; exact ih.2 j hj
            refine ⟨?_, hcrit⟩
            simp only [Mutex]
            rw [Finset.card_le_one]
            intro a ha b hb
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
            rw [← hcrit a ha, ← hcrit b hb]
          · rcases hent with ⟨hwait, htok_i, hpc, htok'⟩
            have hcrit : ∀ j : Node N, t.pc j = Phase.crit → t.token = j := by
              intro j hj
              rw [hpc] at hj
              by_cases hji : j = i
              · subst hji; simp [Function.update] at hj; rw [htok']; exact htok_i
              · simp [Function.update, hji] at hj
                rw [htok']; exact ih.2 j hj
            refine ⟨?_, hcrit⟩
            simp only [Mutex]
            rw [Finset.card_le_one]
            intro a ha b hb
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
            rw [← hcrit a ha, ← hcrit b hb]
          · rcases hrel with ⟨hcrit_i, hpc, htok⟩
            have hcrit : ∀ j : Node N, t.pc j = Phase.crit → t.token = j := by
              intro j hj
              have hji : j ≠ i := by
                intro hji; rw [hji] at hj; rw [hpc] at hj
                simp [Function.update] at hj
              have hsj : s.pc j = Phase.crit := by
                rw [hpc] at hj; simpa [Function.update, hji] using hj
              have h1 : s.token = i := ih.2 i hcrit_i
              have h2 : s.token = j := ih.2 j hsj
              exact absurd ((h1.symm.trans h2).symm) hji
            refine ⟨?_, hcrit⟩
            simp only [Mutex]
            rw [Finset.card_le_one]
            intro a ha b hb
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
            rw [← hcrit a ha, ← hcrit b hb]
        · subst heq; exact ih

end TokenRing
