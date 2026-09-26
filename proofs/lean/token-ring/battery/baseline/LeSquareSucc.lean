import Mathlib

/-
Capability battery seed (plan D22), case `le_square_succ`: arithmetic with a product: nonlinear, so the pass's linear omega is not enough

One `sorry`, and the statement under test is the whole file — `harness.route_b` refuses a seed whose
elaboration presents anything but one goal with a proof state. The battery runs the same eight cases
after every setup change; this file is data, not a proof, and a run closes it in place (the committed
seed is never written).
-/

namespace Battery

theorem le_square_succ (n : Nat) : n ≤ n * n + 1 := by
  sorry

end Battery
