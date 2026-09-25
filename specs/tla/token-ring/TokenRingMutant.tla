------------------------- MODULE TokenRingMutant ------------------------
\* Negative control: identical to TokenRing except that a node may enter
\* its critical section while holding no token. TLC must report a Mutex
\* violation; a measurement pipeline that reports success here is broken.
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N
ASSUME NAssumption == N \in Nat /\ N >= 2

Nodes == 0 .. (N - 1)

VARIABLES token, pc

vars == <<token, pc>>

Init ==
    /\ token = 0
    /\ pc = [i \in Nodes |-> "idle"]

Request(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ UNCHANGED token

Enter(i) ==
    /\ pc[i] = "wait"
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
