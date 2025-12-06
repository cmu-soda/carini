---- MODULE T1 ----
EXTENDS Naturals

CONSTANTS Round, Value, Quorum, Node

VARIABLES one_a, one_b, proposal, vote

vars == <<one_a, one_b, proposal, vote>>

None == 0

ASSUME None \in Round

Init ==
  /\ one_a = [r \in Round |-> FALSE]
  /\ one_b = [n \in Node |-> [r \in Round |-> FALSE]]
  /\ proposal = [r \in Round |-> [v \in Value |-> FALSE]]
  /\ vote = [n \in Node |-> [r \in Round |-> [v \in Value |-> FALSE]]]

send_1a(r) ==
  /\ r # None
  /\ one_a' = [one_a EXCEPT![r] = TRUE]
  /\ UNCHANGED<<one_b, proposal, vote>>

join_round(n, r) ==
  /\ r # None
  /\ one_a[r]
  /\ one_b' = [one_b EXCEPT![n][r] = TRUE]
  /\ UNCHANGED<<one_a, proposal, vote>>

propose(r, q, maxr, v) ==
  /\ r # None
  /\ \A V \in Value : ~proposal[r][V]
  /\ \A N \in Node : N \in q => one_b[N][r]
  /\ (maxr = None) => \A N \in Node, MAXR \in Round, V \in Value : ~(N \in q /\ ~(r <= MAXR) /\ vote[N][MAXR][V])
  /\ (maxr # None) =>
       /\ \E N \in Node : N \in q /\ ~(r <= maxr) /\ vote[N][maxr][v]
       /\ \A N \in Node, MAXR \in Round, V \in Value : (N \in q /\ ~(r <= MAXR) /\ vote[N][MAXR][V]) => MAXR <= maxr
  /\ proposal' = [proposal EXCEPT![r][v] = TRUE]
  /\ UNCHANGED<<one_a, one_b, vote>>

cast_vote(n, v, r) ==
  /\ r # None
  /\ proposal[r][v]
  /\ vote' = [vote EXCEPT![n][r][v] = TRUE]
  /\ UNCHANGED<<one_a, one_b, proposal>>

decide(r, v, q) ==
  /\ r # None
  /\ \A N \in Node : N \in q => vote[N][r][v]
  /\ UNCHANGED<<one_a, one_b, proposal, vote>>

Next ==
  \/ \E r \in Round : send_1a(r)
  \/ \E n \in Node, r \in Round : join_round(n, r)
  \/ \E r \in Round, q \in Quorum, maxr \in Round, v \in Value : propose(r, q, maxr, v)
  \/ \E n \in Node, v \in Value, r \in Round : cast_vote(n, v, r)
  \/ \E r \in Round, v \in Value, q \in Quorum : decide(r, v, q)

Spec == Init /\ [][Next]_vars

======
