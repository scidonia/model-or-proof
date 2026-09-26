------------------------- MODULE BakeryMutant --------------------------
\* Negative control: identical to Bakery except that a process may enter
\* its critical section without holding a ticket of precedence — the
\* ticket/num half of Enter's guard is dropped, the flag half is kept.
\* Two processes waiting with distinct ticket values each satisfy the
\* weakened guard and enter together, so TLC must report a
\* MutualExclusion violation; a pipeline that reports success here is
\* broken.
EXTENDS Naturals

CONSTANT N
ASSUME NAssumption == N \in Nat /\ N >= 2

P == 1 .. N

VARIABLES num, flag, pc

vars == <<num, flag, pc>>

TypeOK ==
    /\ num \in [P -> 0 .. N]
    /\ flag \in [P -> BOOLEAN]
    /\ pc \in [P -> {"idle", "doorway", "wait", "crit"}]

Init ==
    /\ num = [i \in P |-> 0]
    /\ flag = [i \in P |-> FALSE]
    /\ pc = [i \in P |-> "idle"]

\* Unused by the weakened Enter below; kept so the mutant differs from
\* Bakery in exactly one guard.
LL(i, j) ==
    \/ num[i] < num[j]
    \/ /\ num[i] = num[j]
       /\ i <= j

SetFlag(i) ==
    /\ pc[i] = "idle"
    /\ flag' = [flag EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = "doorway"]
    /\ UNCHANGED num

ChooseTicket(i) ==
    /\ pc[i] = "doorway"
    /\ \E t \in 0 .. N :
         /\ \A j \in P \ {i} : t > num[j]
         /\ num' = [num EXCEPT ![i] = t]
    /\ flag' = [flag EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "wait"]

Enter(i) ==
    /\ pc[i] = "wait"
    /\ \A j \in P \ {i} : flag[j] = FALSE          \* MUTANT: ticket ordering dropped
    /\ pc' = [pc EXCEPT ![i] = "crit"]
    /\ UNCHANGED <<num, flag>>

Exit(i) ==
    /\ pc[i] = "crit"
    /\ num' = [num EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED flag

Next ==
    \E i \in P : SetFlag(i) \/ ChooseTicket(i) \/ Enter(i) \/ Exit(i)

MutualExclusion ==
    \A i, j \in P : (i # j) => ~(pc[i] = "crit" /\ pc[j] = "crit")

Spec == Init /\ [][Next]_vars
=============================================================================
