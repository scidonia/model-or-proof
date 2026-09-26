import Mathlib

/-
Capability battery seed (plan D22), case `range_card`: a `Finset` lookup: automation or the model

One `sorry`, and the statement under test is the whole file — `harness.route_b` refuses a seed whose
elaboration presents anything but one goal with a proof state. The battery runs the same eight cases
after every setup change; this file is data, not a proof, and a run closes it in place (the committed
seed is never written).
-/

namespace Battery

theorem range_card (n : Nat) : (Finset.range n).card = n := by
  sorry

end Battery
