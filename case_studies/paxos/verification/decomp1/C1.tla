-------------------------------- MODULE C1 -------------------------------
(***************************************************************************)
(* This is a specification of the Paxos algorithm without explicit leaders *)
(* or learners.  It refines the spec in Voting                             *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Value, Acceptor, Ballot \*, Quorum
Quorum == {i \in SUBSET(Acceptor) : Cardinality(i) * 2 > Cardinality(Acceptor)}

\*ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
\*                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

None == "None"

VARIABLE
    msgs2a,
    msgs2b

vars == <<msgs2a, msgs2b>>

TypeOK ==
    /\ msgs2a \in SUBSET (Ballot \X Value)
    /\ msgs2b \in SUBSET (Acceptor \X Ballot \X Value)


Init ==
    /\ msgs2a = {}
    /\ msgs2b = {}

Phase2a(b, v, a) ==
    /\ ~ \E m \in msgs2a : m[1] = b
    /\ msgs2a' = msgs2a \cup {<<b,v>>}
    /\ UNCHANGED <<msgs2b>>

Phase2b(a, b, v) ==
    /\ <<b,v>> \in msgs2a
    /\ msgs2b' = msgs2b \cup {<<a,b,v>>}
    /\ UNCHANGED<<msgs2a>>

Next ==
    \/ \E b \in Ballot : \E v \in Value : \E a \in Acceptor : Phase2a(b, v, a)
    \/ \E a \in Acceptor : \E b \in Ballot : \E v \in Value : Phase2b(a, b, v)

Spec == Init /\ [][Next]_vars

ChosenAt(b, v) == \E Q \in Quorum : \A a \in Q : <<a, b, v>> \in msgs2b

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

Safety == \A v,w \in chosen : v = w

============================================================================
