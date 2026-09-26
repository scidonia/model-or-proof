/-
Token-ring mutual exclusion at `N₀` — the tier-1 seed for Route B (protocol §2).

Tier 1 is "instantiate the general theorem at `N₀` (one tactic)", so this file **imports the promoted
model** (`TokenRingProved.lean`) and states the corollary over it: it adds no model of its own, and it does not
restate the general theorem. The seed itself (`TokenRing.lean`) is not imported: a promotion writes the
proved module beside it and leaves the seed byte-identical, so nothing proved ever sits at a seed's path. It carries exactly one statement under test, so the closure loop's seed
presents exactly one `sorry` — the shape `harness.lean_repl.LeanReplProver` requires and the shape
`count_unclosed` needs the artifact to end in (plan D5/D6).

As in `TokenRing.lean`, the statement is the human's and the proof is the loop's.
-/
import TokenRingProved
namespace TokenRing

/-- The task's instance — `tasks/token-ring.json`'s `n0`, the last instance Route A calibrates
(`specs/tla/token-ring/TokenRingN23.cfg`). -/
abbrev N₀ : ℕ := 23

/-- **Mutual exclusion at `N₀`** (tier 1): the general `mutex` at the task's instance — the same
reachability hypothesis and the same `Mutex`, at `N = 23`. -/
theorem mutex_n0 (s : State N₀) (hs : Reachable (by norm_num : 2 ≤ N₀) s) : Mutex s := by
  exact mutex (by norm_num : 2 ≤ N₀) s hs

end TokenRing
