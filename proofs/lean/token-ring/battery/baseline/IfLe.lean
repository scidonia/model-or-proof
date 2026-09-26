import Mathlib

/-
Capability battery seed (plan D22), case `if_le`: a case split on a decidable proposition (the model's work)

One `sorry`, and the statement under test is the whole file — `harness.route_b` refuses a seed whose
elaboration presents anything but one goal with a proof state. The battery runs the same eight cases
after every setup change; this file is data, not a proof, and a run closes it in place (the committed
seed is never written).
-/

namespace Battery

theorem if_le (n : Nat) (p : Prop) [Decidable p] : (if p then n else 0) ≤ n := by
  sorry

end Battery
