/-
Bakery mutual exclusion at `N₀` — the tier-1 seed for Route B (protocol §2).

Tier 1 is "instantiate the general theorem at `N₀` (one tactic)", so this file **imports the model**
(`Bakery.lean`) and states the corollary over it: it adds no model of its own, and it does not restate
the general theorem. It carries exactly one statement under test, so the closure loop's seed presents
exactly one `sorry` — the shape `harness.lean_repl.LeanReplProver` requires and the shape `count_unclosed`
needs the artifact to end in (plan D5/D6).

As in `Bakery.lean`, the statement is the human's and the proof is the loop's.

The instance is `tasks/bakery.json`'s `n0`, calibrated by Route A at `N₀ = 9`
(`specs/tla/bakery/BakeryN9.cfg`), so this is the same number the Route A cell runs at and the two rows
are comparable by instance rather than only by task.
-/
import BakeryProved

namespace Bakery

/-- The task's instance — `tasks/bakery.json`'s `n0`, the instance Route A calibrates. -/
abbrev N₀ : ℕ := 9

/-- **Mutual exclusion at `N₀`** (tier 1): the general `mutual_exclusion` at the task's instance — the
same reachability hypothesis and the same `MutualExclusion`, at `N = 9`. `Bakery.Reachable` carries no
`N ≥ 2` argument (unlike token-ring's), so the instance bound lives in the proof rather than in the
statement, and the proof is the trivial instantiation:
`exact mutual_exclusion (by decide : 2 ≤ 9) s hs`. -/
theorem mutual_exclusion_n0 (s : State N₀) (hs : Reachable s) : MutualExclusion s := by
  exact mutual_exclusion (by decide : 2 ≤ 9) s hs

end Bakery
