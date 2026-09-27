----------------------------- MODULE PaxosFinite -----------------------------
(***************************************************************************)
(* An executable, finite projection of the IJCAR 2010 Paxos specification. *)
(*                                                                         *)
(* The reference artifact is specs/tla/ijcar2010/paxos/Paxos.tla, imported *)
(* byte-for-byte (see specs/tla/ijcar2010/PROVENANCE.md) and never edited   *)
(* here. That file is TLAPS proof text: it EXTENDS TLAPS, it instantiates   *)
(* Consensus, `Ballots == Nat` is a definition rather than a cfg-bound      *)
(* constant, and `None == CHOOSE v : v \notin Values` is an unbounded       *)
(* choice evaluated by Init, which TLC cannot enumerate. A .cfg alone       *)
(* cannot make its state-generation rule finite.                           *)
(*                                                                         *)
(* This module therefore carries the *executable* part of the reference    *)
(* only - the constants' finite domains, Init, the four phases, Next, Spec *)
(* and the chosen/consistency predicates - with the three limitations      *)
(* resolved by:                                                            *)
(*   * N and B as cfg constants with Acceptors == 1..N, Ballots == 0..B;   *)
(*   * Values as the finite two-value domain;                              *)
(*   * None as the explicit sentinel "NoValue", outside Values.            *)
(* The TLAPS proof body (WontVoteIn, SafeAt, MsgInv, AccInv, Inv,          *)
(* Invariant, Consistent and the refinement definitions/lemmas) is not     *)
(* executable state-generation and is not reproduced; the audit            *)
(* docs/equivalence-paxos.md classifies it as outside the TLC predicate.   *)
(* Every operator that IS reproduced below is byte-identical to the        *)
(* reference, except the documented domain projection.                     *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS N, B

Acceptors == 1..N

Values == {"v0", "v1"}

Quorums == {Q \in SUBSET Acceptors : Cardinality(Q) > N \div 2}

ASSUME QuorumAssumption ==
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

Ballots == 0..B

VARIABLES msgs,    \* The set of messages that have been sent.
          maxBal,  \* maxBal[a] is the highest-number ballot acceptor a
                   \*   has participated in.
          maxVBal, \* maxVBal[a] is the highest ballot in which a has
          maxVal   \*   voted, and maxVal[a] is the value it voted for
                   \*   in that ballot.

vars == <<msgs, maxBal, maxVBal, maxVal>>

Send(m) == msgs' = msgs \cup {m}

\* "NoValue" stands for the reference's `None == CHOOSE v : v \notin Values`:
\* the same meaning (a value outside Values), chosen explicitly so TLC can
\* evaluate it. "NoValue" is in neither Values nor Acceptors.
None == "NoValue"

Init == /\ msgs = {}
        /\ maxVBal = [a \in Acceptors |-> -1]
        /\ maxBal  = [a \in Acceptors |-> -1]
        /\ maxVal  = [a \in Acceptors |-> None]

(***************************************************************************)
(* Phase 1a: A leader selects a ballot number b and sends a 1a message     *)
(* with ballot b to a majority of acceptors.  It can do this only if it    *)
(* has not already sent a 1a message for ballot b.                         *)
(***************************************************************************)
Phase1a(b) == /\ ~ \E m \in msgs : (m.type = "1a") /\ (m.bal = b)
              /\ Send([type |-> "1a", bal |-> b])
              /\ UNCHANGED <<maxVBal, maxBal, maxVal>>

(***************************************************************************)
(* Phase 1b: If an acceptor receives a 1a message with ballot b greater    *)
(* than that of any 1a message to which it has already responded, then it  *)
(* responds to the request with a promise not to accept any more proposals *)
(* for ballots numbered less than b and with the highest-numbered ballot   *)
(* (if any) for which it has voted for a value and the value it voted for  *)
(* in that ballot.  That promise is made in a 1b message.                  *)
(***************************************************************************)
Phase1b(a) ==
  \E m \in msgs :
     /\ m.type = "1a"
     /\ m.bal > maxBal[a]
     /\ Send([type |-> "1b", bal |-> m.bal, maxVBal |-> maxVBal[a],
               maxVal |-> maxVal[a], acc |-> a])
     /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
     /\ UNCHANGED <<maxVBal, maxVal>>

(***************************************************************************)
(* Phase 2a: If the leader receives a response to its 1b message (for      *)
(* ballot b) from a quorum of acceptors, then it sends a 2a message to all *)
(* acceptors for a proposal in ballot b with a value v, where v is the     *)
(* value of the highest-numbered proposal among the responses, or is any   *)
(* value if the responses reported no proposals.  The leader can send only *)
(* one 2a message for any ballot.                                          *)
(***************************************************************************)
Phase2a(b) ==
  /\ ~ \E m \in msgs : (m.type = "2a") /\ (m.bal = b)
  /\ \E v \in Values :
       /\ \E Q \in Quorums :
            \E S \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = b)} :
               /\ \A a \in Q : \E m \in S : m.acc = a
               /\ \/ \A m \in S : m.maxVBal = -1
                  \/ \E c \in 0..(b-1) :
                        /\ \A m \in S : m.maxVBal =< c
                        /\ \E m \in S : /\ m.maxVBal = c
                                        /\ m.maxVal = v
       /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

(***************************************************************************)
(* Phase 2b: If an acceptor receives a 2a message for a ballot numbered    *)
(* b, it votes for the message's value in ballot b unless it has already   *)
(* responded to a 1a request for a ballot number greater than or equal to  *)
(* b.                                                                      *)
(***************************************************************************)
Phase2b(a) ==
  \E m \in msgs :
    /\ m.type = "2a"
    /\ m.bal >= maxBal[a]
    /\ Send([type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a])
    /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ maxVal' = [maxVal EXCEPT ![a] = m.val]

Next == \/ \E b \in Ballots : Phase1a(b) \/ Phase2a(b)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
(***************************************************************************)
(* How a value is chosen:                                                  *)
(*                                                                         *)
(* This spec does not contain any actions in which a value is explicitly   *)
(* chosen (or a chosen value learned).  What it means for a value to be    *)
(* chosen is defined by the operator Chosen, where Chosen(v) means that v  *)
(* has been chosen.  From this definition, it is obvious how a process     *)
(* learns that a value has been chosen from messages of type "2b".         *)
(***************************************************************************)
VotedForIn(a, v, b) == \E m \in msgs : /\ m.type = "2b"
                                       /\ m.val  = v
                                       /\ m.bal  = b
                                       /\ m.acc  = a

ChosenIn(v, b) == \E Q \in Quorums :
                     \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in Ballots : ChosenIn(v, b)

(***************************************************************************)
(* The consistency condition that a consensus algorithm must satisfy is    *)
(* the invariance of the following state predicate Consistency.            *)
(***************************************************************************)
Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => (v1 = v2)
-----------------------------------------------------------------------------
(***************************************************************************)
(* Message universe and state typing, as in the reference's invariant      *)
(* section. TypeOK is available for the audit and is not the checked       *)
(* property of this task.                                                  *)
(***************************************************************************)
Messages ==      [type : {"1a"}, bal : Ballots]
            \cup [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
                    maxVal : Values \cup {None}, acc : Acceptors]
            \cup [type : {"2a"}, bal : Ballots, val : Values]
            \cup [type : {"2b"}, bal : Ballots, val : Values, acc : Acceptors]

TypeOK == /\ msgs \in SUBSET Messages
          /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
          /\ maxBal \in  [Acceptors -> Ballots \cup {-1}]
          /\ maxVal \in  [Acceptors -> Values \cup {None}]
          /\ \A a \in Acceptors : maxBal[a] >= maxVBal[a]

(***************************************************************************)
(* Diagnostic non-vacuity predicate (docs/protocol.md 4.10).               *)
(*                                                                         *)
(* NoChoice is TRUE of a state in which no value has been chosen. It is    *)
(* *not* part of Spec and not part of Consistency: it is a deliberately    *)
(* false invariant used only to obtain a TLC counterexample trace that     *)
(* proves a choice is actually reachable at a measured instance, so that   *)
(* Consistency cannot hold only because the finite projection prevents any *)
(* decision. Its rows and traces live under results/paxos-witness/ and are *)
(* kept out of the headline Route A rows.                                  *)
(***************************************************************************)
NoChoice == ~(\E v \in Values : Chosen(v))
=============================================================================
