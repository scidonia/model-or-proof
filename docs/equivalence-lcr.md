# Equivalence audit: LCR, TLA+ ↔ Lean (Route B)

Protocol §4.1 requires the Lean port to be audited **statement by statement** against the reference
specification, so that Route B answers the same question Route A answered. This file is that audit, and it
is data: it is read by no code.

- **TLA+ reference** — `specs/tla/lcr/LCR.tla` (authored for this rung; `UniqueLeader`, safety)
- **Lean model** — `proofs/lean/lcr/LCR.lean` (module `LCR`), the tier-2 seed
- **Lean tier-1 seed** — `proofs/lean/lcr/LCRN0.lean` (module `LCRN0`): written — `unique_leader_n0` at
  `N₀ = 10`, the sweep's calibrated instance, importing `LCR` and becoming `LCRProved` once promotion
  re-points it (§2)
- **TLA+ mutant** — `specs/tla/lcr/LCRMutant.tla`
- **Lean mutant** — `proofs/lean/lcr/LCRMutant.lean` (module `LCRMutant`)
- **Toolchain** — `leanprover/lean4:v4.35.0-rc3`, the same pin as `proofs/lean/token-ring/` and
  `proofs/lean/bakery/`, whose resolved `lake-manifest.json` this package copies
- **Route A instance** — `tasks/lcr.json`'s `n0` is **10**: the sweep ran every instance through N = 10,
  all succeeding well inside the 2 h cap, so the tier-1 corollary is stated at that instance and the two
  rows are comparable by it
- **Enumerator** — deferred: no `scripts/equivalence_lcr.py` is written; the TLC sweep's logs will be the
  state-graph evidence (§7)

**What the reference spec is not.** Unlike Bakery and token-ring there is no imported artifact here: the
scout looking for a canonical provenance-able LCR specification failed on a persistent model-API 400, so
`specs/tla/lcr/LCR.tla` is authored by this project under the Bakery precedent. It is therefore not a
quotation of anybody's published module, and the claim it supports is narrower than EWD998's: this audit
maps our Lean port to *our* TLA+ reference, and no external calibration is claimed from it. If a canonical
spec surfaces later it takes EWD998's PROVENANCE treatment rather than silently replacing this one.

Each Lean artifact is the closure loop's **seed** (plan D5), and one seed carries exactly one statement
under test: `LCR.lean` holds the model and the general theorem, and `LCRMutant.lean` holds only the mutated
theorem. The model and the theorem statement are the human's; the proof is the loop's. This audit is
therefore about the *statements* — what is being claimed, and whether it is the same claim TLA+ makes — not
about the tactics that close them. Closure is asserted separately and structurally by the harness (zero
`sorry`/`Admitted`/`axiom` in the artifact, plan D6).

## 1. Line correspondence

Every operator of `LCR.tla`, against its Lean counterpart. Each operator's **bare name** is the first cell
of its row and its Lean counterpart the second, so "every operator has a Lean correspondence" is checkable
rather than aspirational. "Exact" means the two declarations constrain the same thing, conjunct for
conjunct; "idiomatic" means the representation of that notion differs in kind, and §3 says how.

| TLA+ operator | Lean (`LCR.`) | TLA+ source (line) | Kind and correspondence |
| --- | --- | --- | --- |
| ASSUME NAssumption | the hypothesis `hN : 2 ≤ N`, the first argument of `unique_leader` | `CONSTANT N`, `ASSUME NAssumption == N \in Nat /\ N >= 2` (21–22) | exact — `N ∈ Nat` is the type `ℕ`; `N >= 2` is carried as `hN`, and no declaration holds for smaller `N`. As in Bakery and unlike token-ring, `Init` names no distinguished process, so the assumption sits on the theorem rather than on `Reachable` (§3.4) |
| P | `abbrev Process (N : ℕ) := Fin N` | `P == 1 .. N` (24) | idiomatic — `Fin N` is the same number of processes in the same cyclic order; the module's `1 .. N` is `0 .. N-1` in Lean, and the identity of process `i` is `i` in both (§3.1) |
| succ | `def succ (i : Process N) : Process N := ⟨(i.val + 1) % N, Nat.mod_lt _ i.pos⟩` | `succ(i) == (i % N) + 1` (28) | exact — the same successor with the ring's wrap-around; the module's `%` and `+ 1` are `Nat` operations on `Fin.val`, and `i.pos` supplies the positivity `Nat.mod_lt` needs because a process exists |
| TypeOK | *the type `State N` itself*: `msg : Process N → Option (Process N)`, `sent : Process N → Bool`, `leader : Process N → Bool` | `TypeOK == /\ ident \in [P -> P] /\ \A i, j \in P : (ident[i] = ident[j]) => (i = j) /\ msg \in [P -> 0 .. N] /\ sent \in [P -> BOOLEAN] /\ leader \in [P -> BOOLEAN]` (33–38) | idiomatic — the slot bound `0 .. N` with `0` meaning empty is the type `Option (Process N)`, and the two flags are the type `Bool`, so no value of `State N` leaves `TypeOK`. The `ident` conjuncts are discharged by representation: `ident` is not a field, and its injectivity is the injectivity of `Fin N`'s value (§3.2) |
| Init | `Init (s : State N) := s.msg = fun _ => none ∧ s.sent = fun _ => false ∧ s.leader = fun _ => false` | `Init == /\ ident = [i \in P \|-> i] /\ msg = [i \in P \|-> 0] /\ sent = [i \in P \|-> FALSE] /\ leader = [i \in P \|-> FALSE]` (40–44) | exact — the three constant functions in the module's order; every slot empty, nothing initiated, no leader. The `ident` conjunct is the identity function by representation (§3.1) |
| Send | `Send (i : Process N) (s t : State N) := s.sent i = false ∧ s.msg (succ i) = none ∧ t.msg = Function.update s.msg (succ i) (some i) ∧ t.sent = Function.update s.sent i true ∧ t.leader = s.leader` | `Send(i) == /\ ~sent[i] /\ msg[succ(i)] = 0 /\ msg' = [msg EXCEPT ![succ(i)] = ident[i]] /\ sent' = [sent EXCEPT ![i] = TRUE] /\ UNCHANGED leader` (52–57) | exact — the five conjuncts in the module's order; `EXCEPT ![j] = v` is `Function.update … j (some v)`, `= 0` is `= none`, `UNCHANGED leader` is `t.leader = s.leader`. A disabled send is the module's `msg[succ(i)] = 0` conjunct, i.e. the ring's capacity made explicit |
| Receive | `Receive (i : Process N) (s t : State N) := ∃ m : Process N, s.msg i = some m ∧ ((m > i ∧ s.msg (succ i) = none ∧ t.msg = Function.update (Function.update s.msg i none) (succ i) (some m) ∧ t.sent = s.sent ∧ t.leader = s.leader) ∨ (m < i ∧ t.msg = Function.update s.msg i none ∧ t.sent = s.sent ∧ t.leader = s.leader) ∨ (m = i ∧ t.leader = Function.update s.leader i true ∧ t.msg = Function.update s.msg i none ∧ t.sent = s.sent))` | `Receive(i) == /\ msg[i] # 0 /\ \/ /\ msg[i] > ident[i] /\ msg[succ(i)] = 0 /\ msg' = [msg EXCEPT ![succ(i)] = msg[i], ![i] = 0] /\ UNCHANGED <<ident, sent, leader>> \/ /\ msg[i] < ident[i] /\ msg' = [msg EXCEPT ![i] = 0] /\ UNCHANGED <<ident, sent, leader>> \/ /\ msg[i] = ident[i] /\ leader' = [leader EXCEPT ![i] = TRUE] /\ msg' = [msg EXCEPT ![i] = 0] /\ UNCHANGED <<ident, sent>>` (64–80) | exact — the three cases as three disjuncts, in the module's order, each carrying its own `UNCHANGED`. `ident[i]` is `i` (§3.1); the nested `EXCEPT` in the forward case is the nested `Function.update` |
| Next | `Next (s t : State N) := ∃ i : Process N, Send i s t ∨ Receive i s t` | `Next == \/ \E i \in P : Send(i) \/ \E i \in P : Receive(i)` (82–84) | exact — the same existential over `P` and the same two-way disjunction |
| Spec | `Reachable : State N → Prop` (constructors `init`, `step`) and `Step (s t) := Next s t ∨ t = s` | `Spec == Init /\ [][Next]_vars` (90) | idiomatic — see §3.3: `Spec` is a predicate on *executions*; `Reachable` is the induced predicate on *states*, the standard reading of a safety property and the only one the two tiers need. `[Next]_vars` is `Step`, whose `t = s` disjunct is `UNCHANGED vars` with `vars` being the whole `State` |
| UniqueLeader | `UniqueLeader (s : State N) := ∀ i j : Process N, i ≠ j → ¬ (s.leader i = true ∧ s.leader j = true)` | `UniqueLeader == Cardinality({i \in P : leader[i]}) <= 1` (96–97) | exact — see §3.5: the cardinality bound and the pairwise negation are equivalent for a set of processes, and the pairwise form is what a proof reasons about |
| vars | *the whole `State N` structure* | `vars == <<ident, msg, sent, leader>>` (30) | exact modulo §3.1 — "the tuple of variables" is the structure itself, so `UNCHANGED vars` is `t = s`; `ident` is in the module's tuple and is represented by the identity function rather than a field |

## 2. The two tiers

Tier 2 stands verbatim, as it does in the seed:

```lean
-- proofs/lean/lcr/LCR.lean
theorem unique_leader (hN : 2 ≤ N) (s : State N) (hs : Reachable s) : UniqueLeader s
```

- **Tier 2 — the general theorem.** `unique_leader`: *every* state reachable under `Spec`, at every
  `N ≥ 2`, has at most one leader. This is the statement the module makes as `Spec => []UniqueLeader`
  under `ASSUME N >= 2`; it is not restricted to any instance, so it is strictly stronger than anything a
  bounded TLC run establishes.
- **Tier 1 — the corollary at `N₀`.** `LCRN0.lean`: `unique_leader_n0` states `UniqueLeader` at `N₀ = 10`
  and is closed by instantiating the tier-2 theorem, exactly as `TokenRingN0` and `BakeryN0` are — one
  statement under test, one `sorry`, and an `import` of the promoted module rather than of the seed (the
  promotion rule; `LCRProved.lean` is where the proof will live).

The claim the tier-1 cell supports is therefore deliberately narrow: "the corollary's proof is the
instantiation", so that Route B's cost on the general theorem is the honest number for the general claim
and the corollary is reported as a marginal cost (§7).

## 3. Representation notes

### 3.1 `ident` is not a state field

`LCR.tla` declares `ident` as a variable and *no action changes it*: every one carries `UNCHANGED ident`,
and `Init` pins it to `[i \in P |-> i]`. A variable that is constant along every execution is a
representation choice, not a state field, so `State N` omits it and `Send` loads `i` itself. This is the
same move as token-ring's `Init` naming `nodeZero` rather than storing a distinguished process: the
information is in the index. The audit records it because it is the one place the Lean `State` has fewer
fields than the module has variables, and a reader comparing `vars` to the structure would otherwise see a
gap.

### 3.2 `TypeOK` is carried by the type, including `ident`'s injectivity

Three of `TypeOK`'s five conjuncts are the types of `State N`'s fields. The remaining two are about
`ident`: membership in `P` and injectivity. Both are discharged by §3.1 — `i : Fin N` is in `1 .. N` by
construction, and distinct indices have distinct values, so the module's uniqueness assumption about
identities is a theorem of the representation rather than a state invariant. Nothing in `Reachable` needs
to carry it.

### 3.3 `Spec` becomes `Reachable`

`Spec` is a predicate on executions; `Reachable` is the induced predicate on states, which is the reading
`safety` takes. The `step` constructor quantifies over `Step` — `Next` or a stuttering step — so the
induction a tier-2 proof performs is exactly `[][Next]_vars`'s.

### 3.4 `ASSUME N >= 2` sits on the theorem

The module's assumption is a hypothesis of `unique_leader`, not a conjunct of `Init` and not a parameter of
`Reachable`. `Init` holds at every `N` (it names no distinguished process), so putting the assumption on
`Reachable` would narrow the state set for no reason; the theorem is where the module's `ASSUME` belongs.

### 3.5 The cardinality bound is a pairwise negation

`Cardinality({i \in P : leader[i]}) <= 1` says at most one process has `leader[i] = TRUE`. The Lean statement says
no two *distinct* processes are both leaders. For a finite set these are the same claim: a set of
cardinality ≤ 1 has no two distinct members, and a set with no two distinct members has cardinality ≤ 1.
The pairwise form is stated because that is the shape a proof unfolds, and it is `Mutex`-shaped for the
same reason — `MutualExclusion` is the same pairwise negation over `pc[i] = "crit"`.

## 4. The mutant

`LCRMutant.tla` and `LCRMutant.lean` drop the max-id election guard: the election is reachable with no
condition beyond the process not already being a leader, where `LCR` reaches it only when the identity in
its slot is its own (`Receive`'s third case, `m = i`). Two processes then both elect, so `UniqueLeader` is
false at `N ≥ 2` and both the TLA+ invariant check and the Lean closure must report a violation.

**The violation is unforced**, unlike Bakery's. There, the weakened guard needs two processes to be waiting
with distinct tickets at the same moment; here any two processes electing in any order suffice. That is
deliberate — the control's job is to check the rig refuses a false statement, not that it is sensitive to a
subtle one — and it means a `closed` outcome on this file is a rig failure rather than a hard-won result
(protocol §5).

## 5. What this audit does not claim

- **No external calibration.** The reference is authored here; nothing in it is quoted from a published
  artifact, so unlike EWD998 there is no published number to compare against.
- **No liveness.** `Spec` is asserted with no fairness, and the task's property is safety. "A leader is
  eventually elected" is a different property and is not stated, checked or claimed.
- **Not the maximum-identity rung.** `UniqueLeader` says at most one leader; it does not say the leader is
  the maximum identity. That is a later rung (the plan's LCR scoping), and this model's `Receive` forwards
  larger identities, which is what a proof of *that* property would need.

## 6. Bounded versus unbounded

The TLA+ module is finite-state by construction: a process's slot holds one identity or none (`msg \in
[P -> 0 .. N]`), so the state space is finite at every `N` and TLC can exhaust it. The Lean model has no
such bound to respect — `State N` is finite too, but for a different reason (three functions out of a
finite domain) — and the theorem is proved at every `N ≥ 2` rather than at the largest instance TLC
managed. The bounded run and the unbounded theorem are therefore not the same claim, which is the point of
running both: TLC's per-`N` rows show the message growth curve, and the theorem covers every `N`.

## 7. Pending

- **The calibration sweep** — run: N = 3..10, single-worker, 2 h cap each, per-`N` rows in
  `results/tlc.jsonl`. All eight succeed; distinct states are 39, 135, 459, 1539, 5103, 16767, 54675,
  177147 at 0.7-2.7 s. The curve is **geometric** (each `N` multiplying by ~3.3, ratios converging near
  3.24), not quadratic: the state space is the combination of per-process slot contents, whereas
  Q(N²) is what the algorithm *sends*. The plan's sentence asserting O(N²) growth should say what the
  curve shows instead.
- **An enumerator** — deferred, as it is for Bakery and token-ring.
