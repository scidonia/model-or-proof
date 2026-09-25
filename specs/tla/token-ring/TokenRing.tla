--------------------------- MODULE TokenRing ---------------------------
\* A token-passing ring: the N nodes pass one token, and only the token
\* holder may be in its critical section. The safety property Mutex is
\* what both sides of the experiment must establish: TLC by exhaustive
\* search over the bounded instance, the prover by a general theorem.
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N
ASSUME NAssumption == N \in Nat /\ N >= 2

Nodes == 0 .. (N - 1)

VARIABLES token, pc

vars == <<token, pc>>

TypeOK ==
    /\ token \in Nodes
    /\ pc \in [Nodes -> {"idle", "wait", "crit"}]

Init ==
    /\ token = 0
    /\ pc = [i \in Nodes |-> "idle"]

Request(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ UNCHANGED token

Enter(i) ==
    /\ pc[i] = "wait"
    /\ token = i
    /\ pc' = [pc EXCEPT ![i] = "crit"]
    /\ UNCHANGED token

Release(i) ==
    /\ pc[i] = "crit"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ token' = (i + 1) % N

Next ==
    \E i \in Nodes : Request(i) \/ Enter(i) \/ Release(i)

Mutex ==
    Cardinality({i \in Nodes : pc[i] = "crit"}) <= 1

Spec == Init /\ [][Next]_vars
=============================================================================
