import Mathlib

/-
Capability battery seed (plan D22), case `gauss_sum`: induction over Nat with a nonlinear arithmetic finish (the model's work)

One `sorry`, and the statement under test is the whole file — `harness.route_b` refuses a seed whose
elaboration presents anything but one goal with a proof state. The battery runs the same eight cases
after every setup change; this file is data, not a proof, and a run closes it in place (the committed
seed is never written).
-/

namespace Battery

theorem gauss_sum (n : Nat) : 2 * (List.range (n + 1)).sum = n * (n + 1) := by
  sorry

end Battery
