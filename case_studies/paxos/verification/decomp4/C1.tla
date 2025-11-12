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
    maxBal,
    msgs2b

vars == <<maxBal, msgs2b>>

TypeOK ==
    /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
    /\ msgs2b \in SUBSET (Acceptor \X Ballot \X Value)


Init ==
    /\ maxBal = [a \in Acceptor |-> -1]
    /\ msgs2b = {}

Phase1b(a, b) ==
    /\ b > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ UNCHANGED <<msgs2b>>

Phase2b(a, b, v) ==
    /\ b \geq maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ msgs2b' = msgs2b \cup {<<a,b,v>>}

Next ==
    \/ \E a \in Acceptor : \E b \in Ballot : Phase1b(a,b)
    \/ \E a \in Acceptor : \E b \in Ballot : \E v \in Value : Phase2b(a, b, v)

Spec == Init /\ [][Next]_vars

ChosenAt(b, v) == \E Q \in Quorum : \A a \in Q : <<a, b, v>> \in msgs2b

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

Safety == \A v,w \in chosen : v = w

============================================================================
