-------------------------------- MODULE T1 -------------------------------
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
    msgs1a

vars == <<maxBal, msgs1a>>

TypeOK ==
    /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
    /\ msgs1a \in SUBSET Ballot


Init ==
    /\ maxBal = [a \in Acceptor |-> -1]
    /\ msgs1a = {}

Phase1a(b) ==
    /\ msgs1a' = msgs1a \cup {b}
    /\ UNCHANGED <<maxBal>>

Phase1b(a, b) ==
    /\ b \in msgs1a
    /\ b > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ UNCHANGED <<msgs1a>>

Phase2b(a, b, v) ==
    /\ b \geq maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ UNCHANGED<<msgs1a>>

Next ==
    \/ \E b \in Ballot : Phase1a(b)
    \/ \E a \in Acceptor : \E b \in Ballot : Phase1b(a,b)
    \/ \E a \in Acceptor : \E b \in Ballot : \E v \in Value : Phase2b(a, b, v)

Spec == Init /\ [][Next]_vars

============================================================================
