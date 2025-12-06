---- MODULE C1 ----
EXTENDS Naturals

CONSTANTS Round, Value, Quorum, Node

VARIABLES vote, decision

vars == <<vote, decision>>

None == 0

ASSUME None \in Round

Init ==
  /\ vote = [n \in Node |-> [r \in Round |-> [v \in Value |-> FALSE]]]
  /\ decision = [r \in Round |-> [v \in Value |-> FALSE]]

propose(r, maxr, v) ==
  \E q \in Quorum :
  /\ r # None
  /\ (maxr = None) => \A N \in Node, MAXR \in Round, V \in Value : ~(N \in q /\ ~(r <= MAXR) /\ vote[N][MAXR][V])
  /\ (maxr # None) =>
       /\ \E N \in Node : N \in q /\ ~(r <= maxr) /\ vote[N][maxr][v]
       /\ \A N \in Node, MAXR \in Round, V \in Value : (N \in q /\ ~(r <= MAXR) /\ vote[N][MAXR][V]) => MAXR <= maxr
  /\ UNCHANGED<<vote, decision>>

cast_vote(n, v, r) ==
  /\ r # None
  /\ vote' = [vote EXCEPT![n][r][v] = TRUE]
  /\ UNCHANGED<<decision>>

decide(r, v) ==
  \E q \in Quorum :
  /\ r # None
  /\ \A N \in Node : N \in q => vote[N][r][v]
  /\ decision' = [decision EXCEPT![r][v] = TRUE]
  /\ UNCHANGED<<vote>>

Next ==
  \/ \E r \in Round, maxr \in Round, v \in Value : propose(r, maxr, v)
  \/ \E n \in Node, v \in Value, r \in Round : cast_vote(n, v, r)
  \/ \E r \in Round, v \in Value : decide(r, v)

Spec == Init /\ [][Next]_vars

Safety == \A R1,R2 \in Round, V1,V2 \in Value : decision[R1][V1] /\ decision[R2][V2] => V1 = V2

======
