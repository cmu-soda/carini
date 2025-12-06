---- MODULE C1 ----
EXTENDS Naturals

CONSTANTS Round, Value, Quorum, Node

VARIABLES left_round, decision

vars == <<left_round, decision>>

None == 0

ASSUME None \in Round

Init ==
  /\ left_round = [n \in Node |-> [r \in Round |-> FALSE]]
  /\ decision = [r \in Round |-> [v \in Value |-> FALSE]]

join_round(n, r) ==
  /\ r # None
  /\ ~left_round[n][r]
  /\ left_round' = [N \in Node |-> [R \in Round |-> left_round[N][R] \/ (N=n /\ ~(r <= R))]]
  /\ UNCHANGED<<decision>>

cast_vote(n, v, r) ==
  /\ r # None
  /\ ~left_round[n][r]
  /\ UNCHANGED<<left_round, decision>>

decide(r, v, q) ==
  /\ r # None
  /\ decision' = [decision EXCEPT![r][v] = TRUE]
  /\ UNCHANGED<<left_round>>

Next ==
  \/ \E n \in Node, r \in Round : join_round(n, r)
  \/ \E n \in Node, v \in Value, r \in Round : cast_vote(n, v, r)
  \/ \E r \in Round, v \in Value, q \in Quorum : decide(r, v, q)

Spec == Init /\ [][Next]_vars

Safety == \A R1,R2 \in Round, V1,V2 \in Value : decision[R1][V1] /\ decision[R2][V2] => V1 = V2

======
