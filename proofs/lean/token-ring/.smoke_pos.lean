import Mathlib

theorem smoke_two_mul_sum (n : Nat) : 2 * (List.range (n + 1)).sum = n * (n + 1) := by
  
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.sum_append]; simp [mul_add, ih]; ring
