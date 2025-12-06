---- MODULE T1 ----
EXTENDS Naturals

CONSTANTS Round, Value, Quorum, Node

VARIABLES one_a, one_b, left_round, proposal

vars == <<one_a, one_b, left_round, proposal>>

None == 0

ASSUME None \in Round

Init ==
  /\ one_a = [r \in Round |-> FALSE]
  /\ one_b = [n \in Node |-> [r \in Round |-> FALSE]]
  /\ left_round = [n \in Node |-> [r \in Round |-> FALSE]]
  /\ proposal = [r \in Round |-> [v \in Value |-> FALSE]]

send_1a(r) ==
  /\ r # None
  /\ one_a' = [one_a EXCEPT![r] = TRUE]
  /\ UNCHANGED<<one_b, left_round, proposal>>

join_round(n, r) ==
  /\ r # None
  /\ one_a[r]
  /\ ~left_round[n][r]
  /\ one_b' = [one_b EXCEPT![n][r] = TRUE]
  /\ left_round' = [N \in Node |-> [R \in Round |-> left_round[N][R] \/ (N=n /\ ~(r <= R))]]
  /\ UNCHANGED<<one_a, proposal>>

propose(r, maxr, v) ==
  \E q \in Quorum :
  /\ r # None
  /\ \A V \in Value : ~proposal[r][V]
  /\ \A N \in Node : N \in q => one_b[N][r]
  /\ proposal' = [proposal EXCEPT![r][v] = TRUE]
  /\ UNCHANGED<<one_a, one_b, left_round>>

cast_vote(n, v, r) ==
  /\ r # None
  /\ ~left_round[n][r]
  /\ proposal[r][v]
  /\ UNCHANGED<<one_a, one_b, left_round, proposal>>

Next ==
  \/ \E r \in Round : send_1a(r)
  \/ \E n \in Node, r \in Round : join_round(n, r)
  \/ \E r \in Round, maxr \in Round, v \in Value : propose(r, maxr, v)
  \/ \E n \in Node, v \in Value, r \in Round : cast_vote(n, v, r)

Spec == Init /\ [][Next]_vars

======
