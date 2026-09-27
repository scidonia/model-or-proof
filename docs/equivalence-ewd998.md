# Equivalence audit: EWD998, TLA+ ↔ Lean (Route B)

Protocol §4.1 requires the Lean port to be audited **statement by statement** against the reference
specification, so that Route B answers the same question Route A answered. This file is that audit, and it
is data: it is read by no code.

- **TLA+ reference** — `specs/tla/ewd998/EWD998.tla`, imported at pinned provenance with its TLAPS proofs
  (`EWD998_proof.tla`); the publication-era revision is `specs/tla/ewd998-paper/` (see `PROVENANCE.md`)
- **Lean model** — `proofs/lean/ewd998/EWD998.lean` (module `EWD998`), the tier-2 seed
- **Lean tier-1 seed** — not written yet; `tasks/ewd998.json`'s `n0` is now **3**, so its statement is
  determined and only the seed itself is outstanding
- **TLA+ mutant** — **not defined**; the manifest carries `mutant: null`
- **Lean mutant** — **not written**
- **Toolchain** — `leanprover/lean4:v4.35.0-rc3`, the same pin as the other Route B packages
- **Route A instance** — `n0` is **3**: the calibration completed at N=3 (1,520,618 states in 35.7 s) and has
  not at N=4 (75,753,775 states, 2,506.9 s, then `Error: when reading the disk (StatePoolReader.run)`). The
  manifest lists N=3..6 with generated configs; only `N=3` has completed
- **Enumerator** — deferred, as elsewhere

**Scope: the ring layer only.** The plan's ruling, and it is what makes the port tractable: the
asynchronous termination-detection layer enters `EWD998.tla` solely at
`TD == INSTANCE AsyncTerminationDetection` (`EWD998.tla:203`), a **parse-time** dependency referenced only
by `TDSpec`/`Refinement`. The port is therefore the ring's five state variables and five actions, and the
invariance theorem over them.

**Three non-conflations, stated up front because a reader will otherwise look for them:**

1. **No fairness.** `Spec == Init /\ [][Next]_vars /\ WF_vars(System)` (`EWD998.tla:114`) carries
   fairness for the liveness theorem. The invariance claim — `THEOREM Invariance == Init /\
   [][Next]_vars => []Inv` (`EWD998_proof.tla:176`) — has none, and that is what the Lean `Reachable`
   models.
2. **`TypeOK` is not in the statement.** `THEOREM TypeCorrect` is proved separately (`EWD998_proof.tla:12`)
   and the invariance proof inlines `TypeOK /\ TypeOK'` in its step case, so `TypeOK` is a proof-level
   strengthening. The Lean port carries it in the types of `State` instead, which makes it a fact about
   the representation rather than a conjunct of the seed.
3. **`Termination` and `TerminationDetection` are different properties.** They are the module's "main
   safety property" (`EWD998.tla:155`), grouped with the refinement theorem rather than with invariance.
   They are not stated in the port.

**A fourth, unresolved and flagged rather than assumed:** `tasks/ewd998.json`'s `property` names
`TerminationDetection`, while the seed states `Inv`. The row's `property` field is how a Route B closure is
matched against its Route A calibration, so the two cannot disagree without saying so. This is a plan
question, raised with the planner, and the table below marks the property operators as *not ported* rather
than pretending the manifest and the seed already agree.

## 1. Line correspondence

Every operator of `EWD998.tla` that the port covers, against its Lean counterpart. Each operator's **bare
name** is the first cell of its row and its Lean counterpart the second. "Exact" means the two
declarations constrain the same thing, conjunct for conjunct; "idiomatic" means the representation differs
in kind and §3 says how; "not ported" means the operator is outside the ring layer or is a different
property, and says which.

| TLA+ operator | Lean (`EWD998.`) | TLA+ source (line) | Kind and correspondence |
| --- | --- | --- | --- |
| NAssumption | the hypothesis `hN : 0 < N` on the actions, and `hN : 1 ≤ N` on `inv` | `ASSUME NAssumption == N \in Nat \ {0}` (19) | exact — `N ∈ Nat` is the type `ℕ` and `N ≠ 0` is `0 < N`. It is threaded through `Init`, `InitiateProbe`, `System`, `Next`, `Step` and `Reachable` rather than stated once, because node `0` has to exist for those declarations to be about anything — the `Fin N` index carries "there is a node 0" as its own precondition (§3.1) |
| Node | `abbrev Node (N : ℕ) := Fin N` | `Node == 0 .. N-1` (22) | idiomatic — the same nodes in the same order, re-indexed to `Fin N`; `i.val` is the module's node number, so every comparison with a TLA+ node value is a comparison on `val` (§3.2) |
| Color | `inductive Color where white \| black` | `Color == {"white", "black"}` (23) | exact — a two-constructor inductive, so a third colour is not representable, as in the module |
| Token | `structure Token (N : ℕ) where pos : Node N; q : ℤ; color : Color` | `Token == [pos : Node, q : Int, color : Color]` (24) | exact — a record with the same three fields; `Int` is `ℤ` |
| TypeOK | *the types of `State N` and `Token N`* | `TypeOK == /\ active \in [Node -> BOOLEAN] /\ color \in [Node -> Color] /\ counter \in [Node -> Int] /\ pending \in [Node -> Nat] /\ token \in Token` (32–37) | idiomatic — each conjunct is the type of the corresponding field (`Node → Bool`, `Node → Color`, `Node → ℤ`, `Node → ℕ`, `Token N`), so no value of `State N` can violate it. Not pinned into the seed (§"Three non-conflations", 2) |
| Init | `Init (hN : 0 < N) (s : State N) := s.counter = (fun _ => 0) ∧ s.pending = (fun _ => 0) ∧ s.token.pos = ⟨0, hN⟩ ∧ s.token.q = 0 ∧ s.token.color = Color.black` | `Init == /\ active \in [Node -> BOOLEAN] /\ color \in [Node -> Color] /\ counter = [i \in Node \|-> 0] /\ pending = [i \in Node \|-> 0] /\ token \in [ pos: Node, q: {0}, color: {"black"} ]` (43–49) | idiomatic — the module's first two conjuncts are *unconstrained* choices (`∈` at a function type admits every value), so they constrain nothing and the Lean `Init` omits them rather than writing a tautology (§3.3). The rest is exact: both counters zero, the token at node 0 with count 0 and colour black |
| InitiateProbe | `InitiateProbe (hN : 0 < N) (s t : State N) := s.token.pos = ⟨0, hN⟩ ∧ (s.token.color = Color.black ∨ s.color ⟨0, hN⟩ = Color.black ∨ s.counter ⟨0, hN⟩ + s.token.q > 0) ∧ t.token = ⟨lastNode hN, 0, Color.white⟩ ∧ t.color = Function.update s.color ⟨0, hN⟩ Color.white ∧ s.active = t.active ∧ s.counter = t.counter ∧ s.pending = t.pending` | `InitiateProbe == /\ token.pos = 0 /\ \/ token.color = "black" \/ color[0] = "black" \/ counter[0] + token.q > 0 /\ token' = [pos \|-> N-1, q \|-> 0, color \|-> "white"] /\ color' = [ color EXCEPT ![0] = "white" ] /\ UNCHANGED <<active, counter, pending>>` (50–58) | exact — the guard, the three-way inconclusiveness condition, the token reset to `N-1`/`0`/white, node 0 whitened, and the three unchanged variables. `lastNode hN` is the module's `N-1` (§3.4); `EXCEPT ![0] = v` is `Function.update … ⟨0, hN⟩ v` |
| PassToken | `PassToken (i : Node N) (s t : State N) := s.active i = false ∧ s.token.pos = i ∧ t.token = ⟨prevNode i, s.token.q + s.counter i, if s.color i = Color.black then Color.black else s.token.color⟩ ∧ t.color = Function.update s.color i Color.white ∧ s.active = t.active ∧ s.counter = t.counter ∧ s.pending = t.pending` | `PassToken(i) == /\ ~ active[i] /\ token.pos = i /\ token' = [pos \|-> token.pos - 1, q \|-> token.q + counter[i], color \|-> IF color[i] = "black" THEN "black" ELSE token.color] /\ color' = [ color EXCEPT ![i] = "white" ] /\ UNCHANGED <<active, counter, pending>>` (61–70) | exact — the passivity guard, the position match, the token's three updated fields including the colour rule, the node whitened, and the three unchanged variables. `prevNode i` is `pos - 1` |
| System | `System (hN : 0 < N) (s t : State N) := InitiateProbe hN s t ∨ ∃ i : Node N, i ≠ ⟨0, hN⟩ ∧ PassToken i s t` | `System == \/ InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)` (74–75) | exact — the same disjunction and the same restricted existential; `i ≠ ⟨0, hN⟩` is `i \in Node \ {0}` |
| SendMsg | `SendMsg (i : Node N) (s t : State N) := s.active i = true ∧ (∃ j : Node N, j ≠ i) ∧ t.counter = Function.update s.counter i (s.counter i + 1) ∧ t.pending = Function.update s.pending i (s.pending i + 1) ∧ s.active = t.active ∧ s.color = t.color ∧ s.token = t.token` | `SendMsg(i) == /\ active[i] /\ counter' = [counter EXCEPT ![i] = @ + 1] /\ \E j \in Node \ {i} : pending' = [pending EXCEPT ![j] = @ + 1] /\ UNCHANGED <<active, color, token>>` (79–88) | exact — the activity guard, the sender's count, a non-deterministically chosen receiver's pending count, and the three unchanged variables. The module's note that node `i` is *not* blackened on a send with `j > i` is honoured by not touching `color` |
| RecvMsg | `RecvMsg (i : Node N) (s t : State N) := s.pending i > 0 ∧ t.pending = Function.update s.pending i (s.pending i - 1) ∧ t.counter = Function.update s.counter i (s.counter i - 1) ∧ t.color = Function.update s.color i Color.black ∧ t.active = Function.update s.active i true ∧ s.token = t.token` | `RecvMsg(i) == /\ pending[i] > 0 /\ pending' = [pending EXCEPT ![i] = @ - 1] /\ counter' = [counter EXCEPT ![i] = @ - 1] /\ color' = [ color EXCEPT ![i] = "black" ] /\ active' = [ active EXCEPT ![i] = TRUE ] /\ UNCHANGED <<token>>` (90–99) | exact — the pending guard, pending and count down, Rule 3's blackening, activation, and the token unchanged |
| Deactivate | `Deactivate (i : Node N) (s t : State N) := s.active i = true ∧ t.active = Function.update s.active i false ∧ s.color = t.color ∧ s.counter = t.counter ∧ s.pending = t.pending ∧ s.token = t.token` | `Deactivate(i) == /\ active[i] /\ active' = [active EXCEPT ![i] = FALSE] /\ UNCHANGED <<color, counter, pending, token>>` (101–105) | exact — the activity guard, the node deactivated, and the four unchanged variables |
| Environment | `Environment (s t : State N) := ∃ i : Node N, SendMsg i s t ∨ RecvMsg i s t ∨ Deactivate i s t` | `Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)` (107) | exact — the same existential and three-way disjunction |
| Next | `Next (hN : 0 < N) (s t : State N) := System hN s t ∨ Environment s t` | `Next == System \/ Environment` (111) | exact |
| Step | `Step (hN : 0 < N) (s t : State N) := Next hN s t ∨ t = s` | `[Next]_vars` (114) | exact — the stuttering disjunct, `vars` being the whole `State` |
| Spec | `Reachable (hN : 0 < N) : State N → Prop` (constructors `init`, `step`) | `Spec == Init /\ [][Next]_vars /\ WF_vars(System)` (114) | idiomatic and **deliberately partial** — `Reachable` models `Init /\ [][Next]_vars` only, the invariance reading; the module's `WF_vars(System)` conjunct is the fairness hypothesis of the liveness theorem and is not carried (§"Three non-conflations", 1) |
| B | `B (s : State N) : ℤ := ∑ i : Node N, (s.pending i : ℤ)` | `B == Sum(pending, Node)` (145) | exact — the sum of pending over all nodes, coerced to `ℤ` so it can be compared with a counter sum; `Sum` is `FoldFunctionOnSet(+, 0, f, S)`, which is `Finset.sum` |
| Rng | `Rng (a b : ℕ) : Finset (Node N) := Finset.univ.filter fun i => a ≤ i.val ∧ i.val ≤ b` | `Rng(a,b) == { i \in Node: a <= i /\ i <= b }` (162) | exact — the node interval, as a `Finset`; the module's note that the definition exists to help Apalache construct a bounded set applies to the TLA+ encoding and is not needed on the Lean side |
| Inv | `Inv (s : State N) : Prop` — `P0`'s `B s = ∑ i, s.counter i`, then the four-way disjunction `P1`/`P2`/`P3`/`P4` | `Inv == /\ P0:: B = Sum(counter, Node) /\ \/ P1:: … \/ P2:: … \/ P3:: … \/ P4:: …` (168–183) | exact — clause for clause: `P1`'s "every node past the token is passive and the token's count is the sum over them", with the module's `IF token.pos = N-1 THEN token.q = 0 ELSE …` kept as the same conditional; `P2`'s prefix sum plus the token count positive; `P3`'s black node in the prefix; `P4`'s black token |
| Spec | `theorem inv (hN : 1 ≤ N) (s : State N) (hs : Reachable … s) : Inv s` | `THEOREM Invariance == Init /\ [][Next]_vars => []Inv` (`EWD998_proof.tla:176`) | exact — the module's invariance theorem, with the assumption `N \in Nat \ {0}` as `1 ≤ N` on the theorem |
| Termination | *not ported* | `Termination == /\ \A i \in Node : ~ active[i] /\ B = 0` (150–152) | not ported — a state predicate used by `TerminationDetection`, outside the ring layer's invariant |
| TerminationDetection | *not ported* | `TerminationDetection == terminationDetected => Termination` (155) | not ported — the module's "main safety property", grouped with the refinement theorem rather than with invariance (§"Three non-conflations", 3). **This is where `tasks/ewd998.json`'s `property` disagrees with what the seed states; the discrepancy is flagged, not resolved here.** |
| TypeOK | *the types of `State N`* | `THEOREM TypeCorrect == Init /\ [][Next]_vars => []TypeOK` (`EWD998_proof.tla:12`) | idiomatic — a separate theorem in the module, and here a fact about the types (§"Three non-conflations", 2) |
| System | *(also appears as the fairness target)* | `WF_vars(System)` (114) | not ported — a liveness hypothesis; the invariance theorem does not use it |

## 2. The two tiers

Tier 2 stands verbatim, as it does in the seed:

```lean
-- proofs/lean/ewd998/EWD998.lean
theorem inv (hN : 1 ≤ N) (s : State N) (hs : Reachable (Nat.lt_of_lt_of_le Nat.zero_lt_one hN) s) : Inv s
```

- **Tier 2 — the general theorem.** `inv`: every state reachable under `Init /\ [][Next]_vars` satisfies
  Safra's inductive invariant, at every `N ≥ 1`. This is the module's `Invariance` theorem, and it is not
  restricted to any instance, so it is strictly stronger than anything a bounded TLC run establishes.
- **Tier 1 — the corollary at `N₀ = 3`.** Not written; `n0` is settled, and it will
  be a separate seed closed by instantiating the tier-2 theorem, importing the promoted module
  (`EWD998Proved.lean`) rather than the seed.

## 3. Representation notes

### 3.1 `N ≠ 0` is threaded, not assumed

The module states `ASSUME NAssumption == N \in Nat \ {0}` once. In Lean the same fact appears as
`hN : 0 < N`, but threaded through `Init`, `InitiateProbe`, `System`, `Next`, `Step` and `Reachable`
rather than as a section variable, because node `0` — `InitiateProbe`'s subject and the distinguished node
of the invariant's prefix clauses — must exist for those declarations to be about anything. `Fin N`'s
inhabitant `⟨0, hN⟩` needs `hN` in scope, and making it a section variable would turn each definition into
one that is only meaningful under an unstated side condition. The theorem takes `1 ≤ N`, which is the same
statement in the form a caller writes.

### 3.2 Node numbers are `val`

`Node == 0 .. N-1` becomes `Fin N`, so the module's comparisons on node values (`a <= i`, `i <= b`,
`token.pos = 0`, `pos - 1`) become comparisons on `Fin.val`. The order is preserved, so `Rng` and the
prefix clauses mean the same intervals.

### 3.3 `Init`'s unconstrained conjuncts are omitted

`Init`'s first two conjuncts — `active \in [Node -> BOOLEAN]` and `color \in [Node -> Color]` — admit
*every* function of the right type, so they constrain nothing; they are the module's way of saying that a
node's initial activation and colour are arbitrary. A Lean port could write `∀ i, True`, which is a
tautology, or it can omit the conjuncts and let the functions be arbitrary by being unconstrained fields of
the initial state. The port omits them, and this note is why a reader comparing `Init` line by line will
find two conjuncts fewer than the module has.

### 3.4 `lastNode` and `prevNode`

The module writes `N-1` and `pos-1` as integer expressions, which TLA+ permits because `Node` is a
subrange of `Nat` and the arithmetic is total on the values it uses. Lean needs inhabitants of `Fin N`, so
the two appear as `lastNode hN` and `prevNode i`, each carrying its own bound proof. `lastNode` takes
`hN` because `N-1` is only a node when `N ≥ 1`; `prevNode` needs nothing beyond its argument's own bound.

### 3.5 The module's accounting rules are load-bearing

`Rule 0` appears twice in the ring layer — in `SendMsg` (`counter[i] + 1` with a receiver's `pending + 1`)
and in `RecvMsg` (both decremented) — and `Inv`'s `P0` is exactly the statement that they balance:
`B = Sum(counter, Node)`. A port that got either half subtly wrong would satisfy `P0` on the traces TLC
happens to explore or fail on all of them, so this is the place where the port's *faithfulness* is doing
more work than usual, and it is why the mutant targets a rule rather than a guard on a token action: §4
drops one half of `Rule 0` and the invariant goes false on the first receive.

### 3.6 The liveness hypothesis is absent by design

`Spec` asserts `WF_vars(System)`. The invariance theorem does not use it, so `Reachable` does not carry
it, and the port's `Spec` row in §1 is the closest correspondence rather than an exact one. If a later
rung ports `Live` (`EWD998_proof.tla:743`), it will need a separate model of fair executions rather than an
extension of this one.

## 4. The mutant

**`RecvMsg`'s Rule 0 counter decrement, dropped** — a single semantic weakening of one action, on both
sides: `specs/tla/ewd998/EWD998Mutant.tla` replaces the conjunct with `UNCHANGED counter`, and
`proofs/lean/ewd998/EWD998Mutant.lean` replaces the field update with `s.counter = t.counter`.

`P0` — `B = Sum(counter, Node)` — is a conjunct of `Inv` **outside** the four-way disjunction, so nothing
can rescue it: the first message received lowers `B` while the counter sum stays put. The candidates
rejected for this control each break a *disjunct* instead — dropping `PassToken`'s passivity guard breaks
`P1`, and dropping `RecvMsg`'s blackening breaks `P3` — and a mutant that might still satisfy the invariant
is worse than none, because it looks like a control and is not one.

**Verified:** TLC reports `Inv` violated at depth 3 (`negative_control.observed: violation`), and the Lean
mutant builds, so the closure loop must fail to close it.

**A modelling lesson worth keeping, because it is the same lesson as §3.5's faithfulness point:** removing a
guarded conjunct leaves its variable *unconstrained*. TLC reached `counter = null` and refused the run
before it could check anything, so a dropped guard needs `UNCHANGED counter` in its place — the mutant has
to be a weaker *action*, not a partial one. The Lean side happened to be right already (`s.counter =
t.counter`), which is a small independent check that the two sides describe the same mutation rather than
two mutations that look alike.

## 5. What this audit does not claim

- **No liveness.** The fairness hypothesis and the `Live` theorem are out of the port (§3.6).
- **No async layer.** `AsyncTerminationDetection` and the refinement theorem are out of the port; the
  port is the ring.
- **No resolution of the `property` mismatch.** The manifest names `TerminationDetection`; the seed states
  `Inv`. The audit records both facts and flags the disagreement rather than choosing.
- **No endpoint comparison yet.** The TLA+ side is imported and its published figures are in
  `docs/human-baseline.md`; the Route A calibration ran and set `n0 = 3` (§7).

## 6. Pending

- **Done:** `tasks/ewd998.json`'s `property` is now `Invariance` with the statement about `Inv` (the
  planner's ruling, Main's authorisation), `instances` lists `N = 3..6`, and `mutant` names the two mutant
  files.
- **Done:** the mutant, both sides, verified against TLC (§4).
- **Done:** per-`N` configs generated (`EWD998N3.cfg`..`EWD998N6.cfg`) and the calibration run through them.
  **`n₀` is 3**, and the basis matters more than the value:

  * **N=3** completes in 35.7 s with 1,520,618 distinct states, and has done so five times under the
    flag-resolved invocation — identical counts, which is how the `-cleanup` removal was verified.
  * **N=4** *completes* — but in **2 h 36 min**, 248,006,200 distinct states at depth 104, `EXIT=0`. That is
    outside Route A's 2 h cap, and §11 decision 3 defines `n₀` as *the largest N whose run completes **inside
    that cap***. So N=4 is a completion and not an `N₀`: possible, but never inside the budget.
  * N=5 was still running at 7.2 hours with 643,097,823 distinct states and a *growing* queue when it was
    stopped (49 GB of pool, no cap since it was invoked directly), so it cannot set `n₀` either way. It is
    evidence about the spec's size rather than about calibration.

  **The earlier `n₀ = 3` was right by accident and is right on the merits now.** It was first set from N=4
  failing at 75,753,775 states and 2,506.9 s with `Error: when reading the disk (StatePoolReader.run)` — but
  that failure was `run_tlc` passing `-cleanup`, not the tool: the same instance completes in 2 h 36 min
  without the flag. So the value survives, and what changed is the ground it stands on. The manifest holds
  it; this audit now states the basis.

- **The flag comparison, both arms.** The same N=4 instance was run three times *with* `-cleanup` and died
  each time — 201,981 / 43,634,504 / 75,753,775 distinct states, `StatePoolReader` or `StatePoolWriter` — and
  once *without* it, completing 248,006,200 states in 2 h 36 min. That pair is a death-versus-completion
  comparison rather than a bare `timeout`, and it is the finding in its strongest form.

- **The `timeout` row and the uncapped completion are one run's two faces.** The same instance takes
  2 h 36 min to finish and is cut off at 2 h, which is precisely what `n₀ = 3` means: the tool reaches those
  states and the cap is what stops the record from counting them. Reading the pair together states the
  definition rather than an accident.

- **The clean pass stops at N=4 deliberately.** N=5 and N=6 were flagged-only runs, both dying far short of
  completion (235,260 and 258,428 states). Their clean rows would restate that neither completes inside the
  cap, which §11 decision 3 already excludes and N=4's pair already establishes, at a cost of about four
  hours of host time. So the sweep's clean rows are N=3 and N=4 only, and that is a decision recorded here
  rather than a gap a reader has to interpret.

- **The `-cleanup` finding (fixed).** `run_tlc` passed `-cleanup` unconditionally, and it removed the state
  pool *a run was still using* — N=4 died at 75.7M states and N=5/N=6 at ~250k, while the same N=5 spec
  without the flag passed sixteen times its with-flag death point. Bakery (238.8M) and token-ring (289.4M)
  completed *with* the flag, so it is a two-factor interaction rather than a flag bug. The flag is no longer
  passed; the metadir is created per run and removed in a `finally`, so its lifetime is stated in our code
  rather than delegated.

- **Ordinary churn is not the failure.** An `inotifywait` watch on N=4's metadir recorded 29,794 `DELETE`
  events — TLC rotating its own pool files — and the run completed regardless. The watch's value is the
  distinction: rotation is harmless, `-cleanup`'s removal was not.

- **Fingerprint collision probability is a caveat on the 248M count.** TLC reported
  `calculated (optimistic): .033` against `based on the actual fingerprints: 7.0E-8` — the second is the
  figure that applies, and it is small, but a count of that size carries it and the audit should say so
  rather than leave it in the log.

- **The recorded evidence should be a row, not a log.** The N=4 completion above rests on a `/tmp` log,
  because the no-flag runs were invoked directly rather than through `harness.tlc_run`, which is why
  `results/tlc.jsonl` has no new EWD998 rows. When the sweep re-runs through the runner for the record,
  N=4 should reproduce and land properly; the same standard the error-tail fix set applies to our own
  calibration.
- **Filed, not yet done:** raising TLC's direct-memory ceiling from `run_tlc`'s command line. The comparison
  "the tool cannot do N=4" versus "this storage mode cannot" is not reachable through TLC's own flags —
  `-fp N` is the fingerprint size (all of 0, 1, 2 still start `MSBDiskFPSet`), and `-fpmem 0.7` left the JVM's
  64 MB direct-memory default unchanged — so it needs `-XX:MaxDirectMemorySize` or whatever the wrapper
  honours, confirmed by reading the header's `offheap memory` figure back.
- `TerminationDetection` remains the *task*'s property for the deferred refinement rung, deliberately not
  the pilot's (`property` above).
- `proofs/lean/ewd998/baseline/` and `seeds.json`, and the tier-1 seed.
- An enumerator, deferred as elsewhere.
