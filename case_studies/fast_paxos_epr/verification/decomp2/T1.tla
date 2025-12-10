---- MODULE T1 ----
EXTENDS Naturals

CONSTANTS Node, Value, Quorum_c, Quorum_f, Round

VARIABLES one_a, one_b, left_round, proposal

vars == <<one_a, one_b, left_round, proposal>>

None == 0

ASSUME None \in Round
ASSUME \A Q1, Q2 \in Quorum_c : \E N \in Node : N \in Q1 /\ N \in Q2
ASSUME \A Q1 \in Quorum_c, Q2, Q3 \in Quorum_f : \E N \in Node : N \in Q1 /\ N \in Q2 /\ N \in Q3

Init ==
  /\ one_a = [R \in Round |-> FALSE]
  /\ one_b = [N \in Node |-> [R \in Round |-> FALSE]]
  /\ left_round = [N \in Node |-> [R \in Round |-> FALSE]]
  /\ proposal = [R \in Round |-> [V \in Value |-> FALSE]]

send_1a(r) ==
  /\ r # None
  /\ one_a' = [one_a EXCEPT![r] = TRUE]
  /\ UNCHANGED<<one_b, left_round, proposal>>

join_round(n, r) ==
  /\ r # None
  /\ one_a[r]
  /\ ~left_round[n][r]
  /\ one_b' = [one_b EXCEPT![n][r] = TRUE]
  /\ left_round' = [N \in Node |-> [R \in Round |-> left_round[N][R] \/ (N = n /\ R < r)]]
  /\ UNCHANGED<<one_a, proposal>>

propose_1(r, q, maxr, v, v2) ==
  /\ r # None
  /\ \A V \in Value : ~proposal[r][V]
  /\ \A N \in q : one_b[N][r]
  /\ maxr # None
  /\ proposal' = [proposal EXCEPT![r][v2] = TRUE]
  /\ UNCHANGED<<one_a, one_b, left_round>>

propose_2(r, q, maxr, v) ==
  /\ r # None
  /\ \A V \in Value : ~proposal[r][V]
  /\ \A N \in q : one_b[N][r]
  /\ maxr # None
  /\ proposal' = [proposal EXCEPT![r][v] = TRUE]
  /\ UNCHANGED<<one_a, one_b, left_round>>

propose_3(r, q, v) ==
  /\ r # None
  /\ \A V \in Value : ~proposal[r][V]
  /\ \A N \in q : one_b[N][r]
  /\ UNCHANGED<<one_a, one_b, left_round, proposal>>

propose_4(r, q, v) ==
  /\ r # None
  /\ \A V \in Value : ~proposal[r][V]
  /\ \A N \in q : one_b[N][r]
  /\ proposal' = [proposal EXCEPT![r][v] = TRUE]
  /\ UNCHANGED<<one_a, one_b, left_round>>

cast_vote_p(n, v, r) ==
  /\ r # None
  /\ ~left_round[n][r]
  /\ proposal[r][v]
  /\ UNCHANGED<<one_a, one_b, left_round, proposal>>

cast_vote_a(n, v, r) ==
  /\ r # None
  /\ ~left_round[n][r]
  /\ UNCHANGED<<one_a, one_b, left_round, proposal>>

Next ==
  \/ \E r \in Round : send_1a(r)
  \/ \E n \in Node, r \in Round : join_round(n, r)
  \/ \E r \in Round, q \in Quorum_c, maxr \in Round, v,v2 \in Value : propose_1(r, q, maxr, v, v2)
  \/ \E r \in Round, q \in Quorum_c, maxr \in Round, v \in Value : propose_2(r, q, maxr, v)
  \/ \E r \in Round, q \in Quorum_c, v \in Value : propose_3(r, q, v)
  \/ \E r \in Round, q \in Quorum_c, v \in Value : propose_4(r, q, v)
  \/ \E n \in Node, v \in Value, r \in Round : cast_vote_p(n, v, r)
  \/ \E n \in Node, v \in Value, r \in Round : cast_vote_a(n, v, r)

Spec == Init /\ [][Next]_vars

======
