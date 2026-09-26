---------------------------- MODULE Bakery -----------------------------
\* Lamport's bakery algorithm for mutual exclusion, in its atomic-register
\* form: the shared registers flag and num are written by single atomic
\* steps, and the ticket domain is bounded by 0..N, so the model is
\* finite-state and TLC-checkable.
\*
\* This is a bounded derivation of the IJCAR 2010 artifact
\* specs/tla/ijcar2010/bakery/Bakery.tla, whose safe-register encoding
\* ("a write is an arbitrary sequence of type-correct values") is
\* infinite-state and, as that file's own comment notes, not model
\* checkable. That artifact and its TLAPS proof remain the provenance;
\* this file is the Route A reference semantics.
\*
\* Safety property MutualExclusion: no two distinct processes are
\* simultaneously in their critical section.
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

\* Lexicographic ticket order: i has precedence over j. Ties cannot occur
\* (a ticket is taken strictly greater than every ticket held), so the
\* tie-break is defensive; it matches the IJCAR LL.
LL(i, j) ==
    \/ num[i] < num[j]
    \/ /\ num[i] = num[j]
       /\ i <= j

\* Enter the doorway. The flag stays TRUE until the ticket is taken, which
\* is what makes a process in the doorway block the others.
SetFlag(i) ==
    /\ pc[i] = "idle"
    /\ flag' = [flag EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = "doorway"]
    /\ UNCHANGED num

\* Take a ticket strictly greater than every ticket currently held, then
\* leave the doorway. The 0..N bound is the bounded projection of the
\* unbounded tickets; a process seeing max(others) = N finds no fresh
\* ticket inside the bound and that step is disabled.
ChooseTicket(i) ==
    /\ pc[i] = "doorway"
    /\ \E t \in 0 .. N :
         /\ \A j \in P \ {i} : t > num[j]
         /\ num' = [num EXCEPT ![i] = t]
    /\ flag' = [flag EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "wait"]

\* Enter only when no process is in the doorway and no process holds a
\* ticket that takes precedence over i's.
Enter(i) ==
    /\ pc[i] = "wait"
    /\ \A j \in P \ {i} : flag[j] = FALSE /\ (num[j] = 0 \/ LL(i, j))
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
