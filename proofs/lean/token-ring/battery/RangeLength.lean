import Mathlib

/-
Capability battery seed (plan D22), case `range_length`: `simp` on a list: automation or one model tactic

One `sorry`, and the statement under test is the whole file — `harness.route_b` refuses a seed whose
elaboration presents anything but one goal with a proof state. The battery runs the same eight cases
after every setup change; this file is data, not a proof, and a run closes it in place (the committed
seed is never written).
-/

namespace Battery

theorem range_length (n : Nat) : (List.range n).length = n := by
  sorry

end Battery
