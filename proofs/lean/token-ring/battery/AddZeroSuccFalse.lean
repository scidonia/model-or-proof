import Mathlib

/-
Capability battery seed (plan D22), case `add_zero_succ_false`: **false**: the negative control, which a witness must refute within a small budget

One `sorry`, and the statement under test is the whole file — `harness.route_b` refuses a seed whose
elaboration presents anything but one goal with a proof state. The battery runs the same eight cases
after every setup change; this file is data, not a proof, and a run closes it in place (the committed
seed is never written).
-/

namespace Battery

theorem add_zero_succ_false (n : Nat) : n + 0 = n + 1 := by
  sorry

end Battery
