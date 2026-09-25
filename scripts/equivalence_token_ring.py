#!/usr/bin/env python3
"""Enumerate the token-ring transition relation exactly as `proofs/lean/token-ring/TokenRing.lean`
defines it, and print the state-graph metrics the equivalence audit compares against TLC.

This is the mechanical check behind `docs/equivalence-token-ring.md` §6: an independent
transcription of the Lean `Request`/`Enter`/`Release`/`Next` definitions (a model in the model
checker's sense, not a proof), enumerated exhaustively at the small instances TLC was run on, so
"the Lean relation is the spec's relation" is reproducible from the tree instead of asserted.

Pure Python 3, standard library only. No Lean, no TLC, no network: run it directly.

    python3 scripts/equivalence_token_ring.py            # metrics for N = 2, 3, 4 (positive and mutant)
    python3 scripts/equivalence_token_ring.py --check    # ... and compare with the committed TLC logs

The relation encoded is the Lean one, stated to match `TokenRing.lean` line for line:

    Init       : token = 0, every pc = idle
    Request(i) : pc[i] = idle  -> pc[i] = wait, token unchanged
    Enter(i)   : pc[i] = wait  -> pc[i] = crit, token unchanged     (the mutant drops the guard)
    Release(i) : pc[i] = crit  -> pc[i] = idle, token = (i + 1) % N
    Next       : exists i, Request(i) or Enter(i) or Release(i)
    Step       : Next, or an unchanged state (stuttering adds no state and no counted successor)

`Enter` carries `token = i` in `TokenRing.lean` and omits it in `TokenRingMutant.lean`; the only
difference between the two modes below is that conjunct.

Depth convention: this script reports BFS levels from `Init`, with `Init` at level 0. TLC's "depth
of the complete state graph search" counts the initial state as depth 1, so TLC's printed depth is
`levels + 1`. Both are printed, so a TLC comparison does not look like a disagreement.

`--check` compares the enumerated figures with the two committed TLC logs — the positive `N = 3`
graph (distinct states, states generated, depth, maximum outdegree) and the mutant's printed depth as
the length of its counterexample — and locks the figures audit §6 records for instances with no TLC
run (the positive reachable-state counts at `N = 2` and `N = 4`, the mutant's two-critical-node
counts at `N = 2, 3, 4`, and the BFS levels of the two states §5/§6 name by hand) against the audit's
own text. It exits non-zero on any mismatch.
"""

from __future__ import annotations

import sys
from collections import deque

IDLE, WAIT, CRIT = "idle", "wait", "crit"

# Figures the committed TLC logs print, for `--check`.
# positive, N = 3: results/logs/token-ring-20260925T153629-r1.log
# mutant,   N = 3: results/logs/token-ring-mutant-20260925T153632-r1.log
TLC_POSITIVE_N3 = {
    "distinct_states": 36,
    "states_generated": 73,
    "depth": 11,
    "max_outdegree": 3,
}
# The mutant's log is a search aborted at the violation ("10 states left on queue"), so only the
# depth of the behavior it printed is comparable with a completed enumeration.
TLC_MUTANT_N3 = {"depth": 5}
# Figures audit §6 records for instances with no committed TLC run (there is no log at N = 2 or
# N = 4), so `--check` locks them against the audit text rather than against a log: they are the
# enumeration's own numbers, and the lock is a regression guard on the transcription.
AUDIT_POSITIVE_STATES = {2: 12, 3: 36, 4: 96}
AUDIT_MUTANT_TWO_CRIT = {2: 2, 3: 21, 4: 132}
# Two states audit §5/§6 name by hand, as (token, pc) at N = 3, with their BFS levels. The first is
# where the mutant log's printed 5-state counterexample ends (its State 5); the second is the §5
# example of a reachable two-critical-node state.
MUTANT_WITNESSES = {
    (0, (CRIT, CRIT, IDLE)): 4,
    (1, (CRIT, WAIT, CRIT)): 8,
}

INSTANCES = (2, 3, 4)


def init(n: int) -> tuple:
    """`Init (hN : 2 ≤ N)`: the token at node 0, every node idle."""
    return (0, (IDLE,) * n)


def successors(n: int, state: tuple, guarded: bool = True):
    """The `Next` successors of `state`, as `(action, node, successor)` triples."""
    token, pc = state
    out = []
    for i in range(n):
        if pc[i] == IDLE:  # Request(i)
            nxt = list(pc)
            nxt[i] = WAIT
            out.append(("Request", i, (token, tuple(nxt))))
        if pc[i] == WAIT and (not guarded or token == i):  # Enter(i), guard `token = i`
            nxt = list(pc)
            nxt[i] = CRIT
            out.append(("Enter", i, (token, tuple(nxt))))
        if pc[i] == CRIT:  # Release(i)
            nxt = list(pc)
            nxt[i] = IDLE
            out.append(("Release", i, ((i + 1) % n, tuple(nxt))))
    return out


def explore(n: int, guarded: bool = True) -> dict:
    """Breadth-first closure of `Init` under `Next`, with the metrics TLC prints."""
    start = init(n)
    level = {start: 0}
    queue = deque([start])
    successors_total = 0  # TLC's "states generated" minus the initial state
    outdegrees = []
    while queue:
        state = queue.popleft()
        succ = successors(n, state, guarded)
        if len({s for _, _, s in succ}) != len(succ):
            raise AssertionError("two actions of one state share a successor; recount the edges")
        successors_total += len(succ)
        outdegrees.append(len(succ))
        for _, _, nxt in succ:
            if nxt not in level:
                level[nxt] = level[state] + 1
                queue.append(nxt)
    two_crit = [s for s in level if sum(p == CRIT for p in s[1]) >= 2]
    return {
        "level": level,  # the BFS map, for named-witness checks
        "states": len(level),
        "successors": successors_total,
        "states_generated": successors_total + 1,  # + the initial state
        "levels": max(level.values()),  # BFS levels from Init, Init at level 0
        "tlc_depth": max(level.values()) + 1,  # TLC counts the initial state as depth 1
        "max_outdegree": max(outdegrees),
        "min_outdegree": min(outdegrees),
        "mean_outdegree": round(successors_total / len(level), 2),
        "two_crit": len(two_crit),
        "two_crit_level": min((level[s] for s in two_crit), default=None),
    }


def report(n: int, guarded: bool) -> dict:
    m = explore(n, guarded)
    kind = "positive (guarded Enter)" if guarded else "mutant (Enter unguarded)"
    print(f"N = {n}  {kind}")
    print(f"  distinct reachable states            : {m['states']}")
    print(f"  successors of Next                   : {m['successors']}  "
          f"(TLC 'states generated' = {m['states_generated']})")
    print(f"  depth, BFS levels from Init (Init = 0): {m['levels']}")
    print(f"  depth, TLC convention (Init = 1)     : {m['tlc_depth']}")
    print(f"  outdegree min / mean / max           : {m['min_outdegree']} / "
          f"{m['mean_outdegree']} / {m['max_outdegree']}")
    if not guarded:
        print(f"  reachable states with two critical   : {m['two_crit']}  "
              f"(shortest one at BFS level {m['two_crit_level']})")
    print()
    return m


def check(positive: dict, mutant: dict) -> int:
    """Compare the enumeration with the committed TLC logs; return the number of mismatches."""
    bad = 0

    def expect(label, got, want):
        nonlocal bad
        if got != want:
            bad += 1
            print(f"MISMATCH {label}: enumerated {got}, TLC log {want}")

    expect("N=3 distinct states", positive[3]["states"], TLC_POSITIVE_N3["distinct_states"])
    expect("N=3 states generated", positive[3]["states_generated"],
           TLC_POSITIVE_N3["states_generated"])
    expect("N=3 depth, TLC convention", positive[3]["tlc_depth"], TLC_POSITIVE_N3["depth"])
    expect("N=3 maximum outdegree", positive[3]["max_outdegree"], TLC_POSITIVE_N3["max_outdegree"])
    expect("mutant N=3 counterexample length, TLC convention",
           mutant[3]["two_crit_level"] + 1, TLC_MUTANT_N3["depth"])
    for n, want in AUDIT_POSITIVE_STATES.items():
        expect(f"N={n} positive reachable states (audit figure)", positive[n]["states"], want)
    for n, want in AUDIT_MUTANT_TWO_CRIT.items():
        expect(f"N={n} mutant two-critical states (audit figure)", mutant[n]["two_crit"], want)
    for (state, want_level) in MUTANT_WITNESSES.items():
        got = mutant[3]["level"].get(state)
        expect(f"mutant N=3 witness token={state[0]} pc={state[1]} BFS level", got, want_level)
    if bad:
        print(f"{bad} mismatch(es) against the committed TLC logs")
        return 1
    print("all enumerated metrics match the committed TLC logs")
    return 0


def main(argv) -> int:
    positive = {n: report(n, True) for n in INSTANCES}
    mutant = {n: report(n, False) for n in INSTANCES}
    if "--check" in argv:
        return check(positive, mutant)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
