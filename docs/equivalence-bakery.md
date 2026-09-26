# Equivalence audit: Bakery, TLA+ ↔ Lean (Route B)

Protocol §4.1 requires the Lean port to be audited **statement by statement** against the reference
specification, so that Route B answers the same question Route A answered. This file is that audit
(plan D23 rung 1), and it is data: it is pinned by `tests/test_equivalence_bakery.py` and read by no
code.

- **TLA+ reference** — `specs/tla/bakery/Bakery.tla` (P1's task instance; `MutualExclusion`, safety)
- **Lean model** — `proofs/lean/bakery/Bakery.lean` (module `Bakery`), the tier-2 seed
- **Lean tier-1 seed** — `proofs/lean/bakery/BakeryN0.lean` (module `BakeryN0`): written — `mutual_exclusion_n0` at `N₀ = 9`, the tier-1 seed (§2)
- **TLA+ mutant** — `specs/tla/bakery/BakeryMutant.tla`
- **Lean mutant** — `proofs/lean/bakery/BakeryMutant.lean` (module `BakeryMutant`)
- **Toolchain** — `leanprover/lean4:v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`; the same pin as `proofs/lean/token-ring/`, whose resolved `lake-manifest.json` this package copies
- **Route A instance** — `tasks/bakery.json`'s `n0` is **9**: Route A's calibration landed, so the tier-1 corollary is stated at that instance and the two rows are comparable by instance
- **Enumerator** — deferred: no `scripts/equivalence_bakery.py` has been written yet; the TLC logs a state-graph check would consume now exist under `results/logs/` (§6)

What the reference spec is *not*: the imported IJCAR 2010 artifact
(`specs/tla/ijcar2010/bakery/Bakery.tla`, `machine_checked: false`) is the provenance, and it is
infinite-state by construction — its safe-register writes may take any type-correct value and its
`max` is unbounded — so it is not model checkable and is not the reference here. `specs/tla/bakery/Bakery.tla`
is the bounded atomic-register derivation (plan P1 close-out), and it is the semantics this audit maps.

Each Lean artifact is the closure loop's **seed** (plan D5), and one seed carries exactly one statement
under test: `Bakery.lean` holds the model and the general theorem, and `BakeryMutant.lean` holds only
the mutated theorem. That is what makes a run's artifact a single closed goal (§8's zero-`sorry`
assertion applies to the whole file). The model and the theorem statement are the human's; the proof is
the loop's. This audit is therefore about the *statements* — what is being claimed and whether it is the
same claim TLA+ makes — not about the tactics that close them. Closure is asserted separately and
structurally by the harness (zero `sorry`/`Admitted`/`axiom` in the artifact, plan D6).

## 1. Line correspondence

Every operator of `Bakery.tla`, against its Lean counterpart. This is the table the audit's contract
parses (`tests/test_equivalence_bakery.py`): each operator's **bare name** is the first cell of its row
and its Lean counterpart the second, so "every operator has a Lean correspondence" is checkable rather
than aspirational. "Exact" means the two declarations constrain the same thing, conjunct for conjunct;
"idiomatic" means the representation of that notion differs in kind, and §4 says how.

| TLA+ operator | Lean (`Bakery.`) | TLA+ source (line) | Kind and correspondence |
| --- | --- | --- | --- |
| ASSUME NAssumption | the hypothesis `hN : 2 ≤ N`, the first argument of `mutual_exclusion` | `CONSTANT N`, `ASSUME NAssumption == N \in Nat /\ N >= 2` (18–19) | exact — `N ∈ Nat` is the type `ℕ`; `N >= 2` is carried as the hypothesis `hN`, and no declaration of the model holds for smaller `N`. Unlike token-ring's `nodeZero hN`, nothing in `Init` needs it, so it is on the theorem rather than on `Reachable` (§4.4) |
| P | `abbrev Process (N : ℕ) := Fin N` | `P == 1 .. N` (21) | idiomatic — `Fin N` is the same number of processes in the same order; the module's `1 .. N` is written `0 .. N-1` in Lean, a re-indexing that preserves the order the ticket tie-break reads (§4.2) |
| TypeOK | *the type `State N` itself*: `num : Process N → Ticket N`, `flag : Process N → Bool`, `pc : Process N → Phase`, with `Ticket N := Fin (N + 1)` | `TypeOK == /\ num \in [P -> 0 .. N] /\ flag \in [P -> BOOLEAN] /\ pc \in [P -> {"idle", "doorway", "wait", "crit"}]` (27–30) | idiomatic — see §4.1: the ticket bound `0 .. N` is the type `Fin (N + 1)`, so no value of `State N` can leave it, exactly as `flag`'s booleans and `pc`'s four phases are the type rather than a predicate |
| Init | `Init (s : State N) := s.num = fun _ => (0 : Ticket N) ∧ s.flag = fun _ => false ∧ s.pc = fun _ => Phase.idle` | `Init == num = [i \in P \|-> 0] /\ flag = [i \in P \|-> FALSE] /\ pc = [i \in P \|-> "idle"]` (32–35) | exact — the three constant functions in the module's order; every ticket `0` (no ticket held), every flag down, every process idle |
| LL | `LL (s : State N) (i j : Process N) := s.num i < s.num j ∨ (s.num i = s.num j ∧ i ≤ j)` | `LL(i, j) == \/ num[i] < num[j] \/ /\ num[i] = num[j] /\ i <= j` (40–43) | exact — the same two disjuncts over the same two registers; `<` on `Ticket N` and `≤` on `Process N` are the value orders, so this *is* the lexicographic ticket order. The module calls the tie-break defensive (a ticket is taken strictly greater than every ticket held), and the Lean side keeps it for the same reason |
| SetFlag | `SetFlag (i : Process N) (s t : State N) := s.pc i = Phase.idle ∧ t.flag = Function.update s.flag i true ∧ t.pc = Function.update s.pc i Phase.doorway ∧ t.num = s.num` | `SetFlag(i) == /\ pc[i] = "idle" /\ flag' = [flag EXCEPT ![i] = TRUE] /\ pc' = [pc EXCEPT ![i] = "doorway"] /\ UNCHANGED num` (47–51) | exact — the four conjuncts in order; `EXCEPT ![i] = v` is `Function.update … i v`, `UNCHANGED num` is `t.num = s.num` |
| ChooseTicket | `ChooseTicket (i : Process N) (s t : State N) := s.pc i = Phase.doorway ∧ ∃ ticket : Ticket N, (∀ j : Process N, j ≠ i → s.num j < ticket) ∧ t.num = Function.update s.num i ticket ∧ t.flag = Function.update s.flag i false ∧ t.pc = Function.update s.pc i Phase.wait` | `ChooseTicket(i) == /\ pc[i] = "doorway" /\ \E t \in 0 .. N : /\ \A j \in P \ {i} : t > num[j] /\ num' = [num EXCEPT ![i] = t] /\ flag' = [flag EXCEPT ![i] = FALSE] /\ pc' = [pc EXCEPT ![i] = "wait"]` (57–63) | exact — the ticket is a `Ticket N`, i.e. the bound `0 .. N`, so a process that would need a ticket above `N` has no step here (the disabled step the config's deadlock note describes); `\A j \in P \ {i}` is `∀ j, j ≠ i →`; and `flag'`/`pc'` sit outside the module's `\E` and do not mention `t`, which is why they are independent updates in Lean too |
| Enter | `Enter (i : Process N) (s t : State N) := s.pc i = Phase.wait ∧ (∀ j : Process N, j ≠ i → s.flag j = false ∧ (s.num j = (0 : Ticket N) ∨ LL s i j)) ∧ t.pc = Function.update s.pc i Phase.crit ∧ t.num = s.num ∧ t.flag = s.flag` | `Enter(i) == /\ pc[i] = "wait" /\ \A j \in P \ {i} : flag[j] = FALSE /\ (num[j] = 0 \/ LL(i, j)) /\ pc' = [pc EXCEPT ![i] = "crit"] /\ UNCHANGED <<num, flag>>` (67–71) | exact — both halves of the guard, the doorway half (`flag[j] = FALSE`) and the ticket half (`num[j] = 0 \/ LL(i, j)`), in the module's conjunction order; the ticket half is the half the mutant (§5) drops |
| Exit | `Exit (i : Process N) (s t : State N) := s.pc i = Phase.crit ∧ t.num = Function.update s.num i (0 : Ticket N) ∧ t.pc = Function.update s.pc i Phase.idle ∧ t.flag = s.flag` | `Exit(i) == /\ pc[i] = "crit" /\ num' = [num EXCEPT ![i] = 0] /\ pc' = [pc EXCEPT ![i] = "idle"] /\ UNCHANGED flag` (73–77) | exact — the critical section is left, the ticket is given back (`num[i] = 0`) and the process returns to idle; `UNCHANGED flag` is `t.flag = s.flag` |
| Next | `Next (s t : State N) := ∃ i : Process N, SetFlag i s t ∨ ChooseTicket i s t ∨ Enter i s t ∨ Exit i s t` | `Next == \E i \in P : SetFlag(i) \/ ChooseTicket(i) \/ Enter(i) \/ Exit(i)` (79–80) | exact — the same existential over `P` and the same four-way disjunction |
| MutualExclusion | `MutualExclusion (s : State N) := ∀ i j : Process N, i ≠ j → ¬ (s.pc i = Phase.crit ∧ s.pc j = Phase.crit)` | `MutualExclusion == \A i, j \in P : (i # j) => ~(pc[i] = "crit" /\ pc[j] = "crit")` (82–83) | exact — the same quantifier over the same process set, the same distinctness hypothesis and the same negated conjunction |
| vars | *the whole `State N` structure* | `vars == <<num, flag, pc>>` (25) | exact — "the tuple of variables" is the structure itself, so `UNCHANGED vars` is `t = s` |
| Spec | `Reachable : State N → Prop` (constructors `init`, `step`) | `Spec == Init /\ [][Next]_vars` (85) | idiomatic — see §4.3: `Spec` is a predicate on *executions*; `Reachable` is the induced predicate on *states*, which is the standard reading of a safety property and the only one the two tiers need |

One derived notion appears in the Lean model and has no line of its own: `Ticket N` (§4.1), the bounded
ticket domain the module carries inside `TypeOK` and inside `ChooseTicket`'s quantifier.

## 2. The two tiers

Tier 2 stands verbatim, as it does in the seed:

```lean
-- proofs/lean/bakery/Bakery.lean
theorem mutual_exclusion (hN : 2 ≤ N) (s : State N) (hs : Reachable s) : MutualExclusion s
```

- **Tier 2 — the general theorem.** `mutual_exclusion`: *every* state reachable under `Spec`, at every
  `N ≥ 2`, has at most one process in its critical section. This is the statement the module makes as
  `Spec => []MutualExclusion` under `ASSUME N >= 2`; it is not restricted to any instance, so it is
  strictly stronger than anything a bounded TLC run establishes.
- **Tier 1 — the corollary at `N₀`.** `mutual_exclusion_n0`: the general `mutual_exclusion` at the task's
  instance, `N₀ = 9` (`tasks/bakery.json`'s `n0`, Route A's calibration). The file imports `Bakery` and
  adds no model of its own, concluding `MutualExclusion` from the same `Reachable` — the same shape
  token-ring's tier-1 seed has (protocol §2) — and it carries exactly one statement under test with one
  `sorry`, which is what the closure loop requires of a seed (plan D5/D6). One asymmetry to note:
  `Bakery.Reachable` takes no `N ≥ 2` argument, unlike token-ring's, so the instance bound lives in the
  proof rather than in the statement — promoting the closed artifact makes the proof the trivial
  instantiation `exact mutual_exclusion (by decide : 2 ≤ 9) s hs`.

## 3. Faithfulness: no strengthened assumption, no weakened goal

**The Lean model neither strengthens an assumption nor weakens the goal.** Concretely, in the
direction that would matter if it did:

- **Assumptions.** The only assumption is `N ≥ 2` (the module's `ASSUME NAssumption`). Nothing else is
  assumed: no progress or fairness hypothesis, no `Decidable` instance used as a mathematical fact, no
  extra guard beyond the spec's own, no restriction to an instance. In particular the general theorem
  is not derived from a bounded statement.
- **The goal.** `MutualExclusion` is the module's own bound, not a weaker consequence of it: it is not
  a bound on a restricted process set, not "no two processes are critical *after* some step", and not a
  claim about a hand-picked set of states. `Reachable` is defined from `Init` and `[Next]_vars` alone —
  every state any `Spec` execution passes through, including the initial one and including stuttering
  steps.
- **Actions.** Each action is the module's action conjunct for conjunct, `Next` is the module's
  disjunction over the same processes, and the two register updates are atomic as the module's are.
  Dropping a conjunct would enlarge the reachable set and make the theorem *stronger* than the spec's;
  adding one would make it *weaker*. §1 records that neither happened — and the ticket bound, the one
  place where the bounded spec is narrower than the IJCAR artifact, is carried by the type rather than
  quietly dropped, so the Lean model has exactly the module's state space and not a larger one.
- **The guards are present.** `Enter` carries both halves (§1). The mutant is the file that drops the
  ticket half, and is kept separate (§5) rather than being any part of this model.

Nothing about the safety property is relaxed, and nothing about `Spec` is assumed beyond its
definition.

**One honesty note about what the proof requires.** `MutualExclusion` is **not inductive as stated**:
the induction hypothesis at a reachable state is too weak to carry the `Enter` step, and closing it
needs a stronger invariant — a ticket-ordering property relating a process's ticket to the tickets of
the processes it is waiting behind. That strengthening is the *loop's work*, not this audit's, and it
is recorded here only so a reader knows the statement is honest rather than easy: the seed carries no
hint of it, and neither the seed nor the prompt names it (plan D19's boundary — the activity may be
invited, the content may not be supplied). This file is human-facing documentation; it is not part of
what the model reads.

## 4. Where the model is idiomatic, and where the correspondence is exact

**Exact**: `Init`, `LL`, `SetFlag`, `ChooseTicket` (bound included), `Enter` (both guard halves),
`Exit`, `Next`, `MutualExclusion`, `vars`, and the `N ≥ 2` of `ASSUME NAssumption`.

**Idiomatic**, in four places, each narrowing the gap between a mathematised spec and a type theory:

1. **`TypeOK` is the state type, and the ticket bound is the ticket type.** TLA+ is untyped, so
   `TypeOK` is a predicate an invariant proof must carry and `num` may in principle hold anything. In
   Lean `num : Process N → Ticket N` with `Ticket N := Fin (N + 1)`, `flag : Process N → Bool` and
   `pc : Process N → Phase` *are* the constraint: no value of `State N` leaves `0 .. N`, names a
   non-boolean flag or a fifth phase. The "invariant" holds by construction rather than by induction.
   This is a representational simplification, not an assumption: it removes states the module's
   `TypeOK` would have to exclude, and it excludes no state the module admits. It is also what keeps
   the bounded model finite — `ChooseTicket`'s ticket cannot exceed `N` because there is no such
   value.
2. **Processes are indexed from zero.** The module's `P == 1 .. N` becomes `Fin N`, i.e. `0 .. N-1`.
   The count is the same and the order is the same, which is all the tie-break `i <= j` in `LL` reads,
   so this is a re-indexing and not a change of the model. Ticket *values* are not re-indexed: they
   stay `0 .. N`, since `0` means "no ticket" and is load-bearing in `Enter`'s guard.
3. **`Spec` is read as a state predicate.** The module's `Spec` is a predicate on executions; the Lean
   `Reachable` is the set of states those executions pass through. For a state invariant this is the
   standard translation — `Spec => []MutualExclusion` becomes "every reachable state satisfies
   `MutualExclusion`" — and it is exactly the fragment the experiment measures (safety only, protocol
   §11 decision 4). Stuttering steps are kept (`Step` includes `t = s`) so that no `Spec` execution is
   excluded; because a stuttering step changes no state, they add no reachable states either. What the
   Lean model does **not** formalise is `Spec`'s temporal character itself (fairness, liveness,
   eventualities): out of scope here, and no claim in this audit or in the theorem depends on it.
4. **The assumption sits on the theorem, not on `Reachable`.** `ASSUME N >= 2` is the module's
   spec-level assumption. Token-ring's model needs it earlier (its `Init` names node `0`, which exists
   by `hN`), so there it is a parameter of `Reachable`; Bakery's `Init` names no distinguished process
   and holds at every `N`, so carrying `hN` into `Reachable` would be noise. It is the first argument
   of `mutual_exclusion` instead, which is the same claim about the same instances.

Where the audit is *not* a line-by-line identity, it is because Lean's type is stronger than TLA+'s
predicate, or because an execution predicate has been read as its set of states — in both cases the
Lean statement is a faithful account of the same question, and the reductions are recorded here rather
than hidden.

## 5. The mutant

`BakeryMutant.lean` is the analogue of `BakeryMutant.tla`: the same model with the **ticket half** of
`Enter`'s guard dropped, the flag half kept. Its `Enter` is therefore

```lean
def Enter (i : Process N) (s t : State N) : Prop :=
  s.pc i = Phase.wait ∧
    (∀ j : Process N, j ≠ i → s.flag j = false) ∧
    t.pc = Function.update s.pc i Phase.crit ∧
    t.num = s.num ∧
    t.flag = s.flag
```

and its `theorem mutual_exclusion` has the same statement as the positive model's — which is precisely
why it cannot be closed. The theorem is **false** there, not merely unproved, and a reader can check
that by hand at `N = 2` (processes `0` and `1` in the Lean indexing, positions `1` and `2` in the
module's): `Init`, then `SetFlag(0)`, `ChooseTicket(0)` (taking ticket `1`), `Enter(0)` (into `crit`),
then `SetFlag(1)`, `ChooseTicket(1)` (taking ticket `2`, which is greater than the `1` held) and
`Enter(1)` — whose only guard left is that the other flags are down, which they are — reaches
`num = (1, 2)`, `flag = (FALSE, FALSE)`, `pc = (crit, crit)`. Every step is one of the mutated
module's own actions. The expected Route B outcome is `fail_to_close`, and a `success` on this file is
a broken rig whose numbers are discarded (protocol §5, plan D7). The disproof branch is out of this
slice's contract coverage (plan D7).

The mutant seed is a separate file rather than a mode of the positive seed, so the driver cannot splice
the two: `BakeryMutant.lean` is its own seed with its own recorded baseline, and a run either works on
the honest statement or is refused.

## 6. What is checked mechanically, and what is not yet

The transcription risk §3 cannot close by reading is a *mis-transcription*: declarations that look like
the module's but constrain something else. Token-ring closes it with a committed enumerator of its
transition relation compared against TLC's own state graph (`scripts/equivalence_token_ring.py`,
`docs/equivalence-token-ring.md` §6). **Bakery has no such check committed yet**, and this audit does
not pretend otherwise:

- there is no `scripts/equivalence_bakery.py` to make the comparison: the Bakery TLC logs a state-graph
  check would consume now exist under `results/logs/` (committed), but nothing reads them into a
  reachable-state comparison yet;
- the enumerator is deferred (plan D23 rung 1), so no reachable-state count, depth or outdegree
  figure for this model is asserted anywhere in this file. A number a reader cannot reproduce from the
  tree would be exactly the kind of claim §6 of token-ring's audit had to repair.

What is checked today is §1's statement-by-statement reading, the mutant witness in §5 (a concrete path
a reader can walk through the guards — and one checked by enumerating the transcription's reachable
states at `N = 2` during authoring, which a reader can repeat only once the committed enumerator lands),
and the structural checks the harness performs on any artifact (zero `sorry`/`Admitted`/`axiom`,
statement unchanged, imports clean — plans D6/D13). When the enumerator is written, it and the
TLC comparison follow the token-ring precedent: same relation, same metrics, same named depth
convention, and the figures locked by a `--check` that compares them against the committed log.

## 7. What this audit does not claim

- It does not claim the proof is closed; it is the loop's, and the harness asserts closure from the
  artifact (plan D6). §3 records that the statement needs a strengthening the loop has to find.
- It does not claim the compile succeeded: the Lean files here have not been built at the time of
  writing (the host is running the Route B capability work), so what this audit asserts about them is
  their *content*, not that Lean accepts them.
- It does not cover liveness or temporal properties: no fairness, no starvation freedom, no
  deadlock-freedom. The bounded ticket domain disables `ChooseTicket` at `max(others) = N`, a deadlock
  that is an artifact of the projection rather than a property violation — which is why both Bakery
  configs carry `CHECK_DEADLOCK FALSE`, and why this audit claims nothing about it (protocol §11
  decision 4).
- It does not cover the mutant's `disproof` branch, which is a recorded heuristic for this slice
  (plan D7).
- The tier-1 statement is `mutual_exclusion_n0` in `proofs/lean/bakery/BakeryN0.lean` (§2), stated at
  `N₀ = 9`. This audit's statement-by-statement reading covers the *model*, and the corollary adds no
  model of its own: it imports `Bakery` and concludes `MutualExclusion` from the same `Reachable`, so
  nothing here needs a second reading for it.
- It says nothing about Route A's rows for Bakery, because there are none yet.
