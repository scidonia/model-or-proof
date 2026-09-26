/-
EWD998's invariance at `N₀` — the tier-1 seed for Route B (protocol §2).

Tier 1 is "instantiate the general theorem at `N₀` (one tactic)", so this file imports the model and states
the corollary over it: it adds no model of its own, and it does not restate the general theorem. `N₀` is the
calibrated instance from `tasks/ewd998.json` — **3**, on measured grounds: the TLC sweep completes at N=3
(1,520,618 distinct states in 35.7 s) and does not at N=4 (75,753,775 states, 2,506.9 s, then a disk-pool
read failure). So the bounded instance is a genuine instance of a claim the tool could check, not a reduced
one.

The module's `ASSUME N \in Nat \ {0}` becomes two things here, as in the model: `N₀ = 3` makes the
assumption true by arithmetic, and `Reachable` still takes its `0 < N` hypothesis, discharged at this
instance rather than asserted.

This file carries exactly one statement under test, so the closure loop's seed presents exactly one `sorry`
— the shape `harness.lean_repl.LeanReplProver` requires and the shape `count_unclosed` needs the artifact to
end in (plan D5/D6).

**The import is the tier-2 seed's module, and promotion re-points it.** `EWD998.lean` carries the general
`inv` with a `sorry` until a run closes it; `promote.py` then writes the proved proof to
`EWD998Proved.lean`, a module of its own, and leaves `EWD998.lean` byte-identical — so this line becomes
`import EWD998Proved` once that has happened, exactly as `TokenRingN0.lean`'s, `LCRN0.lean`'s and
`BakeryN0.lean`'s do. Until then this file elaborates against the seed, which is what makes it buildable
from the moment it is written.
-/
import EWD998Proved

namespace EWD998N0

-- The model's names (`State`, `Reachable`, `Inv`) live in `EWD998`; this file states a corollary *of* that
-- model, so it opens the namespace rather than redeclaring anything.
open EWD998

/-- The calibrated tier-1 instance: `tasks/ewd998.json`'s `n0`. -/
abbrev N₀ : ℕ := 3

/-- TLA+ `Inv` at `N₀`, as `EWD998.tla` states it under `CONSTANT N = 3`. `Reachable`'s `0 < N`
hypothesis is the model's `ASSUME N \in Nat \ {0}`, here discharged at the instance rather than assumed. -/
theorem inv_n0 (s : State N₀) (hs : Reachable (by decide) s) : Inv s := by
  exact inv (by decide) s hs

end EWD998N0
