------------------------- MODULE LCRMutant --------------------------
\* Negative control: identical to LCR except that the max-id election guard is
\* dropped. A process may elect itself at any time without checking that the
\* identity it received is its own coming back round the ring — so it never
\* checks that it is the maximum.
\*
\* Two processes each satisfy the weakened action, so at N >= 2 two leaders are
\* reachable and UniqueLeader is false. Unlike the bakery mutant, where the
\* weakened guard needs two processes to be waiting with distinct tickets at the
\* same moment, this violation is unforced: any two processes electing in any
\* order suffice, which is what makes this control a check on the rig rather
\* than on the model's subtlety.
\*
\* A pipeline that reports success here is broken, and its numbers are
\* discarded (protocol §5).
EXTENDS Naturals, FiniteSets

CONSTANT N
ASSUME NAssumption == N \in Nat /\ N >= 2

P == 1 .. N

succ(i) == (i % N) + 1

VARIABLES ident, msg, sent, leader

vars == <<ident, msg, sent, leader>>

TypeOK ==
    /\ ident \in [P -> P]
    /\ \A i, j \in P : (ident[i] = ident[j]) => (i = j)
    /\ msg \in [P -> 0 .. N]
    /\ sent \in [P -> BOOLEAN]
    /\ leader \in [P -> BOOLEAN]

Init ==
    /\ ident = [i \in P |-> i]
    /\ msg = [i \in P |-> 0]
    /\ sent = [i \in P |-> FALSE]
    /\ leader = [i \in P |-> FALSE]

Send(i) ==
    /\ ~sent[i]
    /\ msg[succ(i)] = 0
    /\ msg' = [msg EXCEPT ![succ(i)] = ident[i]]
    /\ sent' = [sent EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<ident, leader>>

\* The weakened action: election with no condition beyond not already being a
\* leader. In LCR this is reachable only when `msg[i] = ident[i]`; here it is
\* reachable whenever the process is not already a leader.
ElectSelf(i) ==
    /\ ~leader[i]
    /\ leader' = [leader EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<ident, msg, sent>>

Receive(i) ==
    /\ msg[i] # 0
    /\ \/ /\ msg[i] > ident[i]
          /\ msg[succ(i)] = 0
          /\ msg' = [msg EXCEPT ![succ(i)] = msg[i], ![i] = 0]
          /\ UNCHANGED <<ident, sent, leader>>
       \/ /\ msg[i] < ident[i]
          /\ msg' = [msg EXCEPT ![i] = 0]
          /\ UNCHANGED <<ident, sent, leader>>
       \/ /\ msg[i] = ident[i]
          /\ leader' = [leader EXCEPT ![i] = TRUE]
          /\ msg' = [msg EXCEPT ![i] = 0]
          /\ UNCHANGED <<ident, sent>>

Next ==
    \/ \E i \in P : Send(i)
    \/ \E i \in P : Receive(i)
    \/ \E i \in P : ElectSelf(i)

\* Same role as in LCR: the configs' `SPECIFICATION` line. No fairness.
Spec == Init /\ [][Next]_vars

UniqueLeader ==
    Cardinality({i \in P : leader[i]}) <= 1

=============================================================================
