---- MODULE C1 ----
EXTENDS Naturals

CONSTANTS Round, Value, Quorum, Node

VARIABLES left_round, vote, decision

vars == <<left_round, vote, decision>>

None == 0

ASSUME None \in Round

Init ==
  /\ left_round = [n \in Node |-> [r \in Round |-> FALSE]]
  /\ vote = [n \in Node |-> [r \in Round |-> [v \in Value |-> FALSE]]]
  /\ decision = [r \in Round |-> [v \in Value |-> FALSE]]

join_round(n, r) ==
  /\ r # None
  /\ ~left_round[n][r]
  /\ left_round' = [N \in Node |-> [R \in Round |-> left_round[N][R] \/ (N=n /\ ~(r <= R))]]
  /\ UNCHANGED<<vote, decision>>

propose(r, q, maxr, v) ==
  /\ r # None
  /\ (maxr = None) => \A N \in Node, MAXR \in Round, V \in Value : ~(N \in q /\ ~(r <= MAXR) /\ vote[N][MAXR][V])
  /\ (maxr # None) =>
       /\ \E N \in Node : N \in q /\ ~(r <= maxr) /\ vote[N][maxr][v]
       /\ \A N \in Node, MAXR \in Round, V \in Value : (N \in q /\ ~(r <= MAXR) /\ vote[N][MAXR][V]) => MAXR <= maxr
  /\ UNCHANGED<<left_round, vote, decision>>

cast_vote(n, v, r) ==
  /\ r # None
  /\ ~left_round[n][r]
  /\ vote' = [vote EXCEPT![n][r][v] = TRUE]
  /\ UNCHANGED<<left_round, decision>>

decide(r, v, q) ==
  /\ r # None
  /\ \A N \in Node : N \in q => vote[N][r][v]
  /\ decision' = [decision EXCEPT![r][v] = TRUE]
  /\ UNCHANGED<<left_round, vote>>

Next ==
  \/ \E n \in Node, r \in Round : join_round(n, r)
  \/ \E r \in Round, q \in Quorum, maxr \in Round, v \in Value : propose(r, q, maxr, v)
  \/ \E n \in Node, v \in Value, r \in Round : cast_vote(n, v, r)
  \/ \E r \in Round, v \in Value, q \in Quorum : decide(r, v, q)

Spec == Init /\ [][Next]_vars

Safety == \A R1,R2 \in Round, V1,V2 \in Value : decision[R1][V1] /\ decision[R2][V2] => V1 = V2

======
