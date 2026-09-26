---------------------------- MODULE LCR -----------------------------
\* LeLann–Chang–Roberts leader election on a unidirectional ring.
\*
\* N processes are arranged in a ring, each with a unique identity, and every
\* message travels one way: process i passes to succ(i). Each process initiates
\* once with its own identity. A process that receives a message m:
\*
\*   * forwards it when m > ident[i]  — a larger identity survives;
\*   * discards it when m < ident[i]  — a smaller one can never win;
\*   * elects itself when m = ident[i] — its own identity has gone all the way
\*     round, so it is the largest in the ring.
\*
\* The safety property is unique leadership: at most one process is ever a
\* leader. It is deliberately the shape of the token-ring / bakery
\* `MutualExclusion` — a cardinality bound over a per-process predicate — so the
\* oracle's theorem/definitions split, the seed-digest cell identity, and the
\* mutant mapping carry over without a second apparatus.
\*
\* This module is the Route A reference semantics. Liveness (a leader is
\* eventually elected) needs fairness and is not TLC-checked here: the task's
\* property is safety, per protocol §2.
EXTENDS Naturals, FiniteSets

CONSTANT N
ASSUME NAssumption == N \in Nat /\ N >= 2

P == 1 .. N

\* The ring is unidirectional: i's messages go to its successor, and N wraps
\* around to 1.
succ(i) == (i % N) + 1

\* `0` is the empty slot: identities are members of P, so 0 is not one of them.
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

\* A process initiates once, with its own identity, into its successor's slot.
\* The successor's slot may be occupied, in which case this step is disabled:
\* that is the ring's capacity assumption made explicit rather than left to the
\* reader.
Send(i) ==
    /\ ~sent[i]
    /\ msg[succ(i)] = 0
    /\ msg' = [msg EXCEPT ![succ(i)] = ident[i]]
    /\ sent' = [sent EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<ident, leader>>

\* Receive: the three cases of the algorithm, each as its own disjunct so a
\* violation can be attributed. `m > ident[i]` forwards, `m < ident[i]`
\* discards, and `m = ident[i]` is the election — the guard the mutant drops.
Receive(i) ==
    /\ msg[i] # 0
    /\ \/ \* forward a larger identity
          /\ msg[i] > ident[i]
          /\ msg[succ(i)] = 0
          /\ msg' = [msg EXCEPT ![succ(i)] = msg[i], ![i] = 0]
          /\ UNCHANGED <<ident, sent, leader>>
       \/ \* discard a smaller identity
          /\ msg[i] < ident[i]
          /\ msg' = [msg EXCEPT ![i] = 0]
          /\ UNCHANGED <<ident, sent, leader>>
       \/ \* our own identity has returned: elect, and stop the message
          /\ msg[i] = ident[i]
          /\ leader' = [leader EXCEPT ![i] = TRUE]
          /\ msg' = [msg EXCEPT ![i] = 0]
          /\ UNCHANGED <<ident, sent>>

Next ==
    \/ \E i \in P : Send(i)
    \/ \E i \in P : Receive(i)

\* The temporal specification exists for the configs' `SPECIFICATION` line and
\* for TLC's reachability run. No fairness is asserted: this task's property is
\* safety (protocol §2), and liveness ("a leader is eventually elected") is out
\* of scope — it would need a fairness assumption that the safety claim does not.
Spec == Init /\ [][Next]_vars

\* Unique leadership: at most one leader, ever. The ring can elect more than
\* once in a run only if the guard above is broken, which is what the mutant
\* demonstrates.
UniqueLeader ==
    Cardinality({i \in P : leader[i]}) <= 1

=============================================================================
