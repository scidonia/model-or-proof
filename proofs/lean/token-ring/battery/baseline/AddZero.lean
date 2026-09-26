import Mathlib

/-
Capability battery seed (plan D22), case `add_zero_self`: trivial arithmetic: the automation pass should carry it (omega)

One `sorry`, and the statement under test is the whole file — `harness.route_b` refuses a seed whose
elaboration presents anything but one goal with a proof state. The battery runs the same eight cases
after every setup change; this file is data, not a proof, and a run closes it in place (the committed
seed is never written).
-/

namespace Battery

theorem add_zero_self (n : Nat) : n + 0 = n := by
  sorry

end Battery
