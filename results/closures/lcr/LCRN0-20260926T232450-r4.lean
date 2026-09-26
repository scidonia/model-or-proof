/-
LCR unique leadership at `N₀` — the tier-1 seed for Route B (protocol §2).

Tier 1 is "instantiate the general theorem at `N₀` (one tactic)", so this file imports the model and
states the corollary over it: it adds no model of its own, and it does not restate the general theorem.
`N₀` is the calibrated instance from `tasks/lcr.json` — the sweep's largest `N` (10), which exhausted in
2.7 s with 177,147 distinct states, so the bounded instance is a genuine instance of the general claim
rather than a reduced one.

This file carries exactly one statement under test, so the closure loop's seed presents exactly one
`sorry` — the shape `harness.lean_repl.LeanReplProver` requires and the shape `count_unclosed` needs the
artifact to end in (plan D5/D6).

**The import is the tier-2 seed's module, and promotion re-points it.** `LCR.lean` carries the general
`unique_leader` with a `sorry` until a run closes it; `promote.py` then writes the proved proof to
`LCRProved.lean`, a module of its own, and leaves `LCR.lean` byte-identical — so this line becomes
`import LCRProved` once that has happened, exactly as `TokenRingN0.lean`'s does. Until then this file
elaborates against the seed, which is what makes it buildable from the moment it is written.
-/
import LCRProved

namespace LCRN0

-- The model's names (`State`, `Reachable`, `UniqueLeader`) live in `LCR`; this file states a corollary
-- *of* that model, so it opens the namespace rather than redeclaring anything.
open LCR

/-- The calibrated tier-1 instance: `tasks/lcr.json`'s `n0`. -/
abbrev N₀ : ℕ := 10

/-- TLA+ `UniqueLeader` at `N₀`, as `LCR.tla` states it under `CONSTANT N = 10`. -/
theorem unique_leader_n0 (s : State N₀) (hs : Reachable s) : UniqueLeader s := by
  exact unique_leader (by norm_num : 2 ≤ N₀) s hs

end LCRN0
