---- MODULE C1 ----
EXTENDS Naturals

CONSTANTS Round, Value, Quorum, Node

VARIABLES proposal, decision

vars == <<proposal, decision>>

None == 0

ASSUME None \in Round

Init ==
  /\ proposal = [r \in Round |-> [v \in Value |-> FALSE]]
  /\ decision = [r \in Round |-> [v \in Value |-> FALSE]]

propose(r, maxr, v) ==
  \E q \in Quorum :
  /\ r # None
  /\ \A V \in Value : ~proposal[r][V]
  /\ proposal' = [proposal EXCEPT![r][v] = TRUE]
  /\ UNCHANGED<<decision>>

cast_vote(n, v, r) ==
  /\ r # None
  /\ proposal[r][v]
  /\ UNCHANGED<<proposal, decision>>

decide(r, v) ==
  \E q \in Quorum :
  /\ r # None
  /\ decision' = [decision EXCEPT![r][v] = TRUE]
  /\ UNCHANGED<<proposal>>

Next ==
  \/ \E r \in Round, maxr \in Round, v \in Value : propose(r, maxr, v)
  \/ \E n \in Node, v \in Value, r \in Round : cast_vote(n, v, r)
  \/ \E r \in Round, v \in Value : decide(r, v)

Spec == Init /\ [][Next]_vars

Safety == \A R1,R2 \in Round, V1,V2 \in Value : decision[R1][V1] /\ decision[R2][V2] => V1 = V2

======
