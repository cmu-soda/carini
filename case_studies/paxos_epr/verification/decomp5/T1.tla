---- MODULE T1 ----
EXTENDS Naturals

CONSTANTS Round, Value, Quorum, Node

VARIABLES one_a, one_b, left_round

vars == <<one_a, one_b, left_round>>

None == 0

ASSUME None \in Round

Init ==
  /\ one_a = [r \in Round |-> FALSE]
  /\ one_b = [n \in Node |-> [r \in Round |-> FALSE]]
  /\ left_round = [n \in Node |-> [r \in Round |-> FALSE]]

send_1a(r) ==
  /\ r # None
  /\ one_a' = [one_a EXCEPT![r] = TRUE]
  /\ UNCHANGED<<one_b, left_round>>

join_round(n, r) ==
  /\ r # None
  /\ one_a[r]
  /\ ~left_round[n][r]
  /\ one_b' = [one_b EXCEPT![n][r] = TRUE]
  /\ left_round' = [N \in Node |-> [R \in Round |-> left_round[N][R] \/ (N=n /\ ~(r <= R))]]
  /\ UNCHANGED<<one_a>>


propose(r, q, maxr, v) ==
  /\ \A N \in Node : N \in q => one_b[N][r]
  /\ UNCHANGED<<one_a, one_b, left_round>>

cast_vote(n, v, r) ==
  /\ r # None
  /\ ~left_round[n][r]
  /\ UNCHANGED<<one_a, one_b, left_round>>

Next ==
  \/ \E r \in Round : send_1a(r)
  \/ \E n \in Node, r \in Round : join_round(n, r)
  \/ \E r \in Round, q \in Quorum, maxr \in Round, v \in Value : propose(r, q, maxr, v)
  \/ \E n \in Node, v \in Value, r \in Round : cast_vote(n, v, r)

Spec == Init /\ [][Next]_vars

======
