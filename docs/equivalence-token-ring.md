# Equivalence audit: token ring, TLA+ ↔ Lean (Route B)

Protocol §4.1 requires the Lean port to be audited **statement by statement** against the reference
specification, so that Route B answers the same question Route A answered. This file is that audit
(plan D9), and it is data: it is pinned by `tests/test_equivalence_token_ring.py` and read by no code.

- **TLA+ reference** — `specs/tla/token-ring/TokenRing.tla` (P1's task instance; `Mutex`, safety)
- **Lean model** — `proofs/lean/token-ring/TokenRing.lean` (module `TokenRing`), the tier-2 seed
- **Lean tier-1 seed** — `proofs/lean/token-ring/TokenRingN0.lean` (imports the model), the `N₀` corollary
- **TLA+ mutant** — `specs/tla/token-ring/TokenRingMutant.tla`
- **Lean mutant** — `proofs/lean/token-ring/TokenRingMutant.lean` (module `TokenRingMutant`)
- **Toolchain** — `leanprover/lean4:v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`
- **Enumerator** — `scripts/equivalence_token_ring.py`, which re-derives §6's state-graph figures from the tree
- **Instance** — `N₀ = 23`: `tasks/token-ring.json`'s `n0`, `specs/tla/token-ring/TokenRingN23.cfg`

Each Lean artifact is the closure loop's **seed** (plan D5), and one seed carries exactly one statement
under test: `TokenRing.lean` holds the model and the general theorem, `TokenRingN0.lean` holds only the
corollary over that model, and `TokenRingMutant.lean` holds only the mutated theorem. That is what
makes a run's artifact a single closed goal (§8's zero-`sorry` assertion applies to the whole file).
The model and the theorem statements are the human's; the proofs are the loop's. This audit is
therefore about the *statements* — what is being claimed and whether it is the same claim TLA+ makes —
not about the tactics that close them. Closure is asserted separately and structurally by the harness
(zero `sorry`/`Admitted`/`axiom` in the artifact, plan D6).

## 1. Line correspondence

Every operator of `TokenRing.tla`, against its Lean counterpart. This is the table the audit's
contract parses (`tests/test_equivalence_token_ring.py`): each operator's **bare name** is the first
cell of its row and its Lean counterpart the second, so "every operator has a Lean correspondence" is
checkable rather than aspirational. "Exact" means the two declarations constrain the same thing,
conjunct for conjunct; "idiomatic" means Lean's representation of that notion differs in kind, and the
paragraph below the table says how.

| TLA+ operator | Lean (`TokenRing.`) | TLA+ source (line) | Kind and correspondence |
| --- | --- | --- | --- |
| ASSUME NAssumption | the type `ℕ` and the hypothesis `hN : 2 ≤ N` | `CONSTANT N`, `ASSUME NAssumption == N \in Nat /\ N >= 2` (8–9) | exact — `N ∈ Nat` is the type of `N`; `N >= 2` is carried as the hypothesis `hN`, which is the first argument of `Init` and of `Reachable`; no declaration of the model holds for smaller `N` |
| Nodes | `abbrev Node (N : ℕ) := Fin N` | `Nodes == 0 .. (N - 1)` (11) | exact — `Fin N` *is* the type of naturals below `N`, ordered; `0 .. (N-1)` under `N >= 2` has the same three inhabitants-with-order for every instance |
| VARIABLES token, pc | `structure State` with fields `token : Node N`, `pc : Node N → Phase`; `vars` is the whole structure | `VARIABLES token, pc` (13), `vars == <<token, pc>>` (15) | exact — `token`'s type is `Nodes` and `pc` is a function from `Nodes`; "the tuple of variables" is the structure itself |
| TypeOK | *the type `State N` itself* (with `inductive Phase`, constructors `idle`, `wait`, `crit`) | `TypeOK == /\ token \in Nodes /\ pc \in [Nodes -> {"idle", "wait", "crit"}]` (17–19) | idiomatic — see §4: the reference spec needs `TypeOK` because its variables are untyped; in Lean the state type makes it a construction invariant rather than a predicate needing an invariant proof |
| Init | `Init (hN : 2 ≤ N) (s : State N) := s.token = nodeZero hN ∧ s.pc = fun _ => Phase.idle` | `Init == /\ token = 0 /\ pc = [i \in Nodes \|-> "idle"]` (21–23) | exact — `0` is `nodeZero hN`, the ring's node `0` (it exists because of `hN`); the everywhere-`idle` record is the constant function `fun _ => Phase.idle` |
| Request | `Request (i : Node N) (s t : State N) := s.pc i = Phase.idle ∧ t.pc = Function.update s.pc i Phase.wait ∧ t.token = s.token` | `Request(i) == /\ pc[i] = "idle" /\ pc' = [pc EXCEPT ![i] = "wait"] /\ UNCHANGED token` (25–28) | exact — the three conjuncts in order; `EXCEPT ![i] = v` is `Function.update s.pc i v`, `UNCHANGED token` is `t.token = s.token` |
| Enter | `Enter (i : Node N) (s t : State N) := s.pc i = Phase.wait ∧ s.token = i ∧ t.pc = Function.update s.pc i Phase.crit ∧ t.token = s.token` | `Enter(i) == /\ pc[i] = "wait" /\ token = i /\ pc' = [pc EXCEPT ![i] = "crit"] /\ UNCHANGED token` (30–34) | exact — the four conjuncts in order, **including the token-holding guard `token = i` on line 32** — the conjunct whose removal defines the mutant (§5) |
| Release | `Release (i : Node N) (s t : State N) := s.pc i = Phase.crit ∧ t.pc = Function.update s.pc i Phase.idle ∧ t.token = ringSucc i`, with `ringSucc i := ⟨(i.val + 1) % N, …⟩` | `Release(i) == /\ pc[i] = "crit" /\ pc' = [pc EXCEPT ![i] = "idle"] /\ token' = (i + 1) % N` (36–39) | exact — `(i + 1) % N` is `ringSucc i`; the pass is counter-clockwise once around `Nodes`, and `ringSucc` is total on every nonempty ring |
| Next | `Next (s t : State N) := ∃ i : Node N, Request i s t ∨ Enter i s t ∨ Release i s t` | `Next == \E i \in Nodes : Request(i) \/ Enter(i) \/ Release(i)` (41–42) | exact — the same existential over `Nodes` and the same three-way disjunction |
| [Next]_vars | `Step (s t : State N) := Next s t ∨ t = s` | `[Next]_vars` (47) | exact — `UNCHANGED vars` is `t = s`, since `vars` is the whole state |
| Mutex | `Mutex (s : State N) := (Finset.univ.filter fun i => s.pc i = Phase.crit).card ≤ 1` | `Mutex == Cardinality({i \in Nodes : pc[i] = "crit"}) <= 1` (44–45) | exact — the filtered set of critical nodes and the same bound; `Cardinality` of a finite set of nodes is `Finset.card` |
| Spec | `Reachable (hN : 2 ≤ N) : State N → Prop` (`init`, `step` constructors) | `Spec == Init /\ [][Next]_vars` (47) | idiomatic — see §4: `Spec` is a predicate on *executions*; `Reachable` is the induced predicate on *states*, which is the standard reading of a safety property and the only one the two tiers need |

Two derived notions appear in the Lean model and have no TLA+ line of their own: `Phase` (§4) and
`ringSucc`, which exists only to make `token' = (i + 1) % N` a total function on `Node N`.

## 2. The two tiers

Stated verbatim, as they stand in the two seed files:

```lean
-- proofs/lean/token-ring/TokenRing.lean
theorem mutex (hN : 2 ≤ N) (s : State N) (hs : Reachable hN s) : Mutex s

-- proofs/lean/token-ring/TokenRingN0.lean  (import TokenRing; N₀ is an abbrev for 23)
theorem mutex_n0 (s : State N₀) (hs : Reachable (by norm_num : 2 ≤ N₀) s) : Mutex s
```

- **Tier 2 — the general theorem.** `mutex`: *every* state reachable under `Spec`, at *every* `N ≥ 2`,
  has at most one node in its critical section. This is the statement TLA+ makes as `Spec => []Mutex`;
  it is not restricted to any instance, so it is strictly stronger than what TLC established.
- **Tier 1 — the corollary at `N₀`.** `mutex_n0`: the same statement instantiated at `N₀ = 23`, the
  largest instance Route A calibrates (`TokenRingN23.cfg`, and `n0` in `tasks/token-ring.json`). It is
  a corollary, not an independent theorem: it concludes `Mutex`, under the same reachability
  hypothesis, at `N = 23` — exactly the instance whose TLC run took 6748.6 s
  (`results/logs/token-ring-20260925T184838-r1.log`). It is stated **over the model by import**
  (`TokenRingN0.lean` imports `TokenRing` and adds no model of its own), which is protocol §2's
  definition of tier 1 — the general theorem applied at one instance — and means the corollary cannot
  drift away from the statement it instantiates.

The two tiers are the protocol §2 measurement targets (§4.1's audit is what makes them comparable to
the TLC rows), and each is its own seed because a seed carries exactly one statement under test: a
tier-1 run must not be forced to re-derive the general theorem (protocol §2: tier 1 is "one tactic"),
and an artifact with a second unclosed goal could not be recorded as a success (plan D6).

## 3. Faithfulness: no strengthened assumption, no weakened goal

**The Lean model neither strengthens an assumption nor weakens the goal.** Concretely, in the
direction that would matter if it did:

- **Assumptions.** The only assumptions in the Lean model are `N ≥ 2` (TLA+'s `ASSUME NAssumption`)
  and the types themselves. Nothing else is assumed: no totality or progress hypothesis, no
  `Decidable` instance used as a mathematical fact, no extra guard beyond the spec's own, no
  restriction to an instance. In particular the general theorem is not derived from a `N₀`-only
  statement, nor from a bounded `N`, and the tier-1 corollary does not smuggle in a different
  hypothesis: it states the same `Mutex` over the same `Reachable`, at one instance, and it is stated
  in a file that imports the general model rather than restating any part of it.
- **The goal.** `Mutex` is the spec's own bound, not a weaker consequence of it: it is not
  `≤ 1`-on-a-restricted-set, not "no *two* nodes are critical *after* some step", and not a
  reachability claim about a hand-picked state set. `Reachable` is defined from `Init` and
  `[Next]_vars` alone — every state any `Spec` execution passes through, including the initial one and
  including stuttering steps.
- **Actions.** Each action is the spec's action conjunct for conjunct, and `Next` is the spec's
  disjunction over the same `Nodes`. Dropping any conjunct would enlarge the reachable set and make
  the theorem *stronger* than the spec's; adding any would make it *weaker*. §1 records that neither
  happened.
- **The guard is present.** `Enter` carries `s.token = i` (TLA+ line 32). The mutant is the file that
  drops it, and is kept separate (§5) rather than being any part of this model.

Nothing about the safety property is relaxed, and nothing about `Spec` is assumed beyond its
definition. The audit's remaining risk is not weakening but mis-*transcription*; §6 is the mechanical
check against TLC's own state graph.

## 4. Where the model is idiomatic, and where the correspondence is exact

**Exact** (the TLA+ operator is present as a declaration constraining the same thing, and the two can
be read off one another line by line): `Nodes`, `Init`, `Request`, `Enter` (guard included),
`Release`, `Next`, `[Next]_vars`, `Mutex`, and the `N ≥ 2` of `ASSUME NAssumption`.

**Idiomatic**, in three places, each narrowing the gap between a mathematised spec and a type theory:

1. **`TypeOK` is the state type.** TLA+ is untyped, so `TypeOK` is a predicate that an invariant proof
   must carry. Lean's `State N` *is* the constraint: `token : Node N`, `pc : Node N → Phase`, and
   `Phase` has exactly the three constructors `idle`, `wait`, `crit`. No value of `State N` can violate
   `TypeOK`, and none can name a fourth phase; the "invariant" holds by construction rather than by
   induction. This is a representational simplification, not an assumption: it removes states TLA+
   would have to exclude, and it excludes no state TLA+ admits.
2. **States are functions, not tuples.** `vars` in TLA+ is the tuple `<<token, pc>>`; in Lean the state
   is the structure carrying both fields, and `pc` is a plain function `Node N → Phase` (TLA+ `pc` is
   the same function, written as a `[Nodes -> …]` array). `[pc EXCEPT ![i] = v]` becomes
   `Function.update s.pc i v`, which for the domain `Node N` is the same function.
3. **`Spec` is read as a state predicate.** TLA+ `Spec` is a predicate on executions; `Reachable` is
   the set of states those executions pass through. For a state invariant this is the standard
   translation — `Spec => []Mutex` becomes "every reachable state satisfies `Mutex`" — and it is
   exactly the fragment the experiment measures (safety only, protocol §11 decision 4). Stuttering
   steps are kept (`Step` includes `t = s`) so that no `Spec` execution is excluded; because a
   stuttering step changes no state, they add no reachable states either. What the Lean model does
   **not** formalise is `Spec`'s temporal character itself (fairness, liveness, eventualities): out of
   scope here, and no claim in this audit or in the theorem depends on it.

Where the audit is *not* a line-by-line identity, it is because Lean's type is stronger than TLA+'s
predicate, or because an execution predicate has been read as its set of states — in both cases the
Lean statement is a faithful account of the same question, and the reductions are recorded here rather
than hidden.

## 5. The mutant

`TokenRingMutant.lean` is the analogue of `TokenRingMutant.tla`: the same model with `Enter`'s
guard dropped (line 32 of the upstream spec has no counterpart there; `TokenRingMutant.tla` lines
25–28). Its `Enter` is therefore

```lean
def Enter (i : Node N) (s t : State N) : Prop :=
  s.pc i = Phase.wait ∧ t.pc = Function.update s.pc i Phase.crit ∧ t.token = s.token
```

and its `theorem mutex` has the same statement as the positive model's — which is precisely why it
cannot be closed. The theorem is **false** there, not merely unproved: two waiting nodes may enter
one after the other, and at `N = 3` the state with `token = 1` and `pc = (crit, wait, crit)` is
reachable from `Init` (found by complete enumeration of the mutant's reachable states —
`scripts/equivalence_token_ring.py`, where it sits at BFS level 8, §6). TLC refutes
the same mutation at `N = 3` (`TokenRingMutant.cfg`; `results/logs/token-ring-mutant-*.log`,
`outcome: violation`). The expected Route B outcome is `fail_to_close`, and a `success` on this file
is a broken rig whose numbers are discarded (protocol §5, plan D7). The mutant's Route B outcome is
always `fail_to_close`: plan D7 dropped the `disproof` branch — it was unsound and unreachable through
the repl's tactic channel — so no counterexample is claimed; `proof.tactics` is applied-only and
`proof.failures` records what the prover refused.

## 6. Evidence that the transcription is the spec's, not a lookalike

The risk §3 cannot close by reading is a *mis-transcription* — a transition relation that happens to
preserve `Mutex` while not being the spec's. The check is TLC's own state graph, which is a complete
description of `Spec` at an instance, against an exhaustive enumeration of the relation **as
`TokenRing.lean` defines it**. The enumerator is committed, not a session scratch file:

```bash
python3 scripts/equivalence_token_ring.py          # metrics for N = 2, 3, 4 (positive and mutant)
python3 scripts/equivalence_token_ring.py --check  # ... and compare with the committed TLC logs
```

It is pure Python 3 standard library — no Lean, no TLC, no network — so the check reproduces while the
prover is busy. For each `N` it prints the distinct reachable states, the number of `Next` successors
(TLC's "states generated" is that count plus the initial state), the depth **in both conventions**
(§6.1), the minimum/mean/maximum outdegree (§6.2) and, for the mutant, the number of reachable states
with two critical nodes plus the BFS level of the shortest one. `--check` compares the `N = 3`
figures with `results/logs/token-ring-20260925T153629-r1.log` (positive) and
`results/logs/token-ring-mutant-20260925T153632-r1.log` (mutant), locks the rest against the figures
below, and exits non-zero on any mismatch; it exits 0 on this tree (a deliberately doctored figure
makes it report the mismatch and return 1, so the check is not vacuous).

| quantity at `N = 3` | TLC (`token-ring-20260925T153629-r1.log`) | Lean relation (`scripts/equivalence_token_ring.py`) |
| --- | --- | --- |
| distinct states | 36 | 36 |
| successors of `Next` (the log's "73 states generated" is this plus the initial state) | 73 | 72 successors + the initial state = 73 |
| depth | 11, counting the initial state as depth 1 (§6.1) | 10 BFS levels from `Init` (`Init` at level 0) — i.e. 11 under TLC's convention |
| maximum outdegree | 3, the maximum in the log's outdegree line (§6.2) | 3 |
| `MUTEX` verdict | holds (`outcome: success`) | no reachable state has two critical nodes |

### 6.1 The depth convention, named

Both sides count the same graph and differ only in where the count starts, so that graph is "10" or
"11" depending on the convention. Stated explicitly so a re-derivation does not read as a
disagreement:

- **BFS levels from `Init`**, the initial state at level 0: **10** at `N = 3`.
- **TLC's printed "depth of the complete state graph search"**, which counts the initial state as
  depth 1: **11** at `N = 3`.

The mutant log corroborates the second convention independently of the positive one: the
counterexample it prints is a 5-state behavior whose violating state is State 5, and that state — the
enumeration reaches it at **BFS level 4** — is where TLC reports the run's depth **5**, the number of
states in the behavior it printed, not the state's BFS level. Both logs therefore read as "TLC depth =
BFS level + 1", and the committed pair is `10` (BFS levels) / `11` (TLC), not 11 levels from `Init`.
The convention is the one the recorded rows carry: all five positive repetition logs agree on depth 11
and on the outdegree line quoted in §6.2, `harness/tlc_run.py` parses that printed number, and
`results/tlc.jsonl` stores it as `tlc.depth` (`11` at `N = 3`, `5` for the mutant run) — so the audit
and Route A's rows name the same quantity.

### 6.2 What each column of that table is

TLC's outdegree line reads, in full:

```text
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 3 and the 95th
percentile is 3).
```

The compared quantity is the **maximum**, `3`, the parenthetical's third figure, against the
enumeration's maximum outdegree `3`. TLC's headline average (`1`) is *not* the mean outdegree of the
state graph, which the enumeration puts at `2.0` at `N = 3`; whatever statistic TLC prints there, it
is a different quantity, and nothing in this audit is read from it — nor from TLC's printed minimum
(`0`), which the positive graph does not have (every reachable state has at least one successor: its
minimum outdegree is `1`). The row is a maximum-to-maximum comparison with that stated, not an
average silently standing in for a maximum, and nothing else is claimed from the outdegree line.
Likewise the depth row compares TLC's printed depth (11) with the enumeration's depth in TLC's
convention (11), while also reporting the BFS-level figure (10) that §6.1 names.

The rest of the check:

- the positive relation has 12 reachable states at `N = 2` and 96 at `N = 4`;
- the guarded and unguarded relations differ only in `Enter`, and the unguarded one has reachable
  two-critical-node states at `N = 2, 3, 4` (2, 21 and 132 of them);
- the violating state is reachable from `Init`: TLC's printed counterexample ends at `token = 0`,
  `pc = (crit, crit, idle)` (BFS level 4), and §5's `token = 1`, `pc = (crit, wait, crit)` is
  reachable too, at BFS level 8.

Only the `N = 3` quantities in the table above are compared with a committed TLC log. The `N = 2` and
`N = 4` counts and the `2`/`21`/`132` two-critical-node counts have no TLC run in this tree, so they
are the enumeration's own figures, recorded here because they are what this transcription predicts and
locked by `--check` against this text (a regression guard on the transcription, not a cross-check);
the BFS levels of the two hand-named states are locked the same way.

What the enumeration therefore checks is the **Lean file against TLC's graph**: it encodes the same
conjuncts as `TokenRing.lean` (`Enter` with the guard in one mode, without it in the other), so a
mis-transcription *of the Lean file* would be reproduced here rather than caught. The TLA+ ↔ Lean
correspondence itself is §1's statement-by-statement reading, and this section does not replace it.

The state graph agreeing exactly — same distinct states, same edge count, same depth under one named
convention, same maximum outdegree — is what makes "same theorem" a checked claim rather than a
reviewer's reading. The mutant's TLC figures are **partial** and are not compared as a completed
graph: that run aborts at the violation ("10 states left on queue", 23 of the unguarded relation's 81
reachable states at `N = 3`), so its depth 5 is where the search stopped and its outdegree line comes
from that partial graph. What the mutant supports is the counterexample's depth and the
two-critical-node counts above, which is exactly what `--check` asserts.

## 7. What this audit does not claim

- It does not claim the proofs are closed; they are the loop's, and the harness asserts closure from
  the artifact (plan D6).
- It does not cover liveness or temporal properties: no fairness, no eventual entry, no starvation
  freedom is stated on either side (protocol §11 decision 4).
- It does not cover the mutant's Route B run, whose outcome is always `fail_to_close`.
- It says nothing about Route A's measurement rows or about `N₀`'s calibration time; those live in
  `results/`.
