/-
Paxos agreement at a fixed six-acceptor instance — a **pilot**, not the calibrated corollary.

`n0` is deliberately null in `tasks/paxos.json`. The plan's rule selects it from the crossing's own
medians ("first adjacent under-cap successful TLC pair that brackets median theorem+own-corollary
totals", `plans/2026-09-27-paxos-agreement.md`), and this file does not presume that selection. It is the
candidate-instance pilot the plan sanctions while `n0` is null — run with an explicit `--param-N 6` — so
that the **instantiation** cost is measured once against the general theorem's median. `PaxosN0.lean` is
a different artifact, authored only after `n0` is fixed, and its `N₀` will be whatever that rule selects.
Naming this file `PaxosN0.lean`, or letting its prose imply a calibrated instance, would report a
decision the measurements have not made.

The instance is the TLC family's largest successfully exhausted one (`specs/tla/paxos/PaxosN6.cfg`,
`CONSTANT N = 6`), two values, strict majorities — the reference's
`Quorums == {Q \in SUBSET Acceptors : Cardinality(Q) > N \div 2}` (`specs/tla/paxos/PaxosFinite.tla:35`).

**It is not the same claim as that TLC row.** The config bounds `B = 1` while this model's ballot type is
`ℕ` (`Paxos.lean:260`), so the corollary at any `N` is *stronger* than the bounded row it is priced
against. The two wall-clock numbers are not two measurements of one claim, and a reader comparing them
must not assume they are. The pairwise-intersection premise is a **hypothesis** here, as it is in the
general theorem, where the TLC side has TLC assert it — the difference is in the equivalence audit's
territory, not smoothed over here.

The import is the promoted general theorem: the loop closes this file by instantiating `Paxos.agreement`
at `N₆`, which is the "instantiation is free" claim the cost figure exists to test. This file carries
exactly one `sorry`, so it is the one hole the run closes and nothing else.
-/
import PaxosProved

namespace PaxosN6Pilot

-- The model's names live in `Paxos`; this file states a corollary *of* that model.
open Paxos

/-- The pilot instance: six acceptors, the largest successfully exhausted TLC row. Not `n0`. -/
abbrev N₆ : ℕ := 6

/-- The reference's two values at the pilot instance (`Values == {"v0", "v1"}`, no sentinel). -/
abbrev V₆ : Type := Fin 2

/-- Strict-majority quorums over the pilot instance: `PaxosFinite.tla:35` with `N = 6`. -/
def Quorums₆ : Set (Set (Fin N₆)) := {Q | Q.ncard > N₆ / 2}

/-- TLA+ `Spec => []Consistency` at `N = 6`, as `PaxosN6.cfg` states it under `CONSTANT N = 6`. -/
theorem agreement_n6 (h : QuorumAssumption Quorums₆) (s : State N₆ V₆)
    (hs : Reachable Quorums₆ s) : Consistency Quorums₆ s := by
  sorry

end PaxosN6Pilot
