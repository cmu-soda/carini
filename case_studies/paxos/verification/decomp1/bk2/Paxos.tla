-------------------------------- MODULE Paxos -------------------------------
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
    maxVBal, \* <<maxVBal[a], maxVal[a]>> is the vote with the largest
    maxVal,    \* ballot number cast by a; it equals <<-1, None>> if
               \* a has not cast any vote.
    msgs1a,
    msgs1b,
    msgs2a,
    msgs2b

vars == <<maxBal, maxVBal, maxVal, msgs1a, msgs1b, msgs2a, msgs2b>>

TypeOK ==
    /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
    /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
    /\ maxVal \in [Acceptor -> Value \cup {None}]
    /\ msgs1a \in SUBSET Ballot
    /\ msgs1b \in SUBSET (Acceptor \X Ballot \X (Ballot \cup {-1}) \X (Value \cup {None}))
    /\ msgs2a \in SUBSET (Ballot \X Value)
    /\ msgs2b \in SUBSET (Acceptor \X Ballot \X Value)


Init ==
    /\ maxBal = [a \in Acceptor |-> -1]
    /\ maxVBal = [a \in Acceptor |-> -1]
    /\ maxVal = [a \in Acceptor |-> None]
    /\ msgs1a = {}
    /\ msgs1b = {}
    /\ msgs2a = {}
    /\ msgs2b = {}

Phase1a(b) ==
    /\ msgs1a' = msgs1a \cup {b}
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, msgs1b, msgs2a, msgs2b>>

Phase1b(a, b) ==
    /\ b \in msgs1a
    /\ b > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ msgs1b' = msgs1b \cup {<<a,b,maxVBal[a],maxVal[a]>>}
    /\ UNCHANGED <<maxVBal, maxVal, msgs1a, msgs2a, msgs2b>>

Phase2a(b, v, a) ==
    /\ <<a,b,maxVBal[a],maxVal[a]>> \in msgs1b
    /\ ~ \E m \in msgs2a : m[1] = b
    /\ \E Q \in Quorum :
          LET Q1b == {m \in msgs1b : /\ m[1] \in Q
                                     /\ m[2] = b}
              Q1bv == {m \in Q1b : m[3] \geq 0}
          IN  /\ \A aa \in Q : \E m \in Q1b : m[1] = aa
              /\ \/ Q1bv = {}
                 \/ \E m \in Q1bv :
                      /\ m[4] = v
                      /\ \A mm \in Q1bv : m[3] \geq mm[3]
    /\ msgs2a' = msgs2a \cup {<<b,v>>}
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, msgs1a, msgs1b, msgs2b>>

Phase2b(a, b, v) ==
    /\ <<b,v>> \in msgs2a
    /\ b \geq maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = b]
    /\ maxVal' = [maxVal EXCEPT ![a] = v]
    /\ msgs2b' = msgs2b \cup {<<a,b,v>>}
    /\ UNCHANGED<<msgs1a, msgs1b, msgs2a>>

Next ==
    \/ \E b \in Ballot : Phase1a(b)
    \/ \E a \in Acceptor : \E b \in Ballot : Phase1b(a,b)
    \/ \E b \in Ballot : \E v \in Value : \E a \in Acceptor : Phase2a(b, v, a)
    \/ \E a \in Acceptor : \E b \in Ballot : \E v \in Value : Phase2b(a, b, v)

Spec == Init /\ [][Next]_vars

ChosenAt(b, v) == \E Q \in Quorum : \A a \in Q : <<a, b, v>> \in msgs2b

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

Safety == \A v,w \in chosen : v = w

============================================================================
