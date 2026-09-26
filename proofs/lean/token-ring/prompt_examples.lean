import Mathlib

/-
Few-shot examples of proof technique for Route B's prompt (plan D19, version `d19-1`).

What these are for: the model is shown them on every turn, and they teach *how to work* — how to run an
induction, how to split a case, when to generalise a statement before inducting, how to handle a finite
set's cardinality, and how to let the named automation finish a goal. They are technique, never content:
nothing here states, hints at, or exemplifies the auxiliary statement the task under test needs, and
`tests/test_route_b_row.py` asserts this file contains none of that task's own names or phrases. A reader
who wants to know whether the prompt said too much reads this file.

Everything is stated over `Nat` and `List`, with no operator from the model under test, so nothing here
is a lemma that could be lifted into that proof. The examples are written to compile as they stand:
`lake env lean prompt_examples.lean` should succeed with no errors and no `sorry`.

The examples, and what each one teaches:

1. `sum_first_n`        — induction over `Nat`, with `simp` doing the arithmetic and `ih` used in the step.
2. `even_or_odd`        — a step that needs the hypothesis split (`rcases … | …`), then `omega`.
3. `mem_append`         — induction over a list. The statement is generalised over the tail *before* the
                          induction: a claim fixed to one particular tail makes the step unprovable.
4. `card_filter_le`     — a finite-set cardinality goal, finished by the library's own `≤` lemma.
5. `mem_range_succ`     — a goal that is one rewrite: name the automation and let it close.
-/

namespace PromptExamples

-- 1. Induction over `Nat`: `simp` splits the successor's range and `nlinarith` does the arithmetic
-- with the induction hypothesis.
theorem sum_first_n (n : Nat) : 2 * (List.range (n + 1)).sum = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- the successor's range is the previous range plus the new last index, stated for *this* index so
    -- the induction hypothesis stays usable
    have step : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := List.range_succ
    rw [step, List.sum_append]
    simp only [List.sum_cons, List.sum_nil]
    nlinarith

-- 2. The step needs a case split on the induction hypothesis before `omega` can finish.
theorem even_or_odd (n : Nat) : (∃ k, n = 2 * k) ∨ (∃ k, n = 2 * k + 1) := by
  induction n with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ n ih =>
    rcases ih with ⟨k, hk⟩ | ⟨k, hk⟩
    · right; exact ⟨k, by omega⟩
    · left; exact ⟨k + 1, by omega⟩

-- 3. Generalise before inducting. The statement quantifies over both lists, so the induction runs with
-- the tail arbitrary — a version fixed to one particular tail has an unprovable step.
theorem mem_append {α : Type} (a : α) (xs ys : List α) :
    a ∈ xs ++ ys ↔ a ∈ xs ∨ a ∈ ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, or_assoc]

-- 4. A cardinality goal over a finite set: the library's own bound closes it in one step.
theorem card_filter_le {α : Type} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [(a : α) → Decidable (p a)] : (s.filter p).card ≤ s.card :=
  Finset.card_filter_le s p

-- 5. One rewrite away: state the automation tactic the harness also tries and let it finish.
theorem mem_range_succ {n m : Nat} : m ∈ List.range (n + 1) ↔ m < n + 1 := by
  simp

end PromptExamples
