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

propose(r, q, maxr, v) ==
  /\ r # None
  /\ r > maxr \* the proposed round must be larger than maxr, which is the largest proposed round thus far
  \* an odd way of restricting maxr of being the largest proposed (and voted for) round thus far
  /\ (maxr = None) => \A N \in Node, MAXR \in Round, V \in Value :
       \* if the maxr is None, then no one (in the quorum) could have voted for this round
       (r > MAXR) => ~(N \in q /\ vote[N][MAXR][V])
  /\ (maxr # None) =>
       \* if the maxr is larger than None, then:
       \* (1) there must be some node that voted for maxr
       /\ \E N \in Node : N \in q /\ ~(r <= maxr) /\ vote[N][maxr][v]
       \* (2) al votes (in the quorum) must be for maxr or earlier
       /\ \A N \in Node, MAXR \in Round, V \in Value : (N \in q /\ vote[N][MAXR][V] /\ r > MAXR) => MAXR <= maxr
  /\ UNCHANGED<<vote, decision>>

cast_vote(n, v, r) ==
  /\ r # None
  /\ vote' = [vote EXCEPT![n][r][v] = TRUE]
  /\ UNCHANGED<<decision>>

decide(r, v, q) ==
  /\ r # None
  /\ \A N \in Node : N \in q => vote[N][r][v]
  /\ decision' = [decision EXCEPT![r][v] = TRUE]
  /\ UNCHANGED<<vote>>

Next ==
  \/ \E r \in Round, q \in Quorum, maxr \in Round, v \in Value : propose(r, q, maxr, v)
  \/ \E n \in Node, v \in Value, r \in Round : cast_vote(n, v, r)
  \/ \E r \in Round, v \in Value, q \in Quorum : decide(r, v, q)

Spec == Init /\ [][Next]_vars

Safety == \A R1,R2 \in Round, V1,V2 \in Value : decision[R1][V1] /\ decision[R2][V2] => V1 = V2

======
