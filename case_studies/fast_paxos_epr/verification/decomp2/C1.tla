---- MODULE C1 ----
EXTENDS Naturals

CONSTANTS Node, Value, Quorum_c, Quorum_f, Round

VARIABLES vote, decision, any_msg, fast

vars == <<vote, decision, any_msg, fast>>

None == 0

ASSUME None \in Round
ASSUME \A Q1, Q2 \in Quorum_c : \E N \in Node : N \in Q1 /\ N \in Q2
ASSUME \A Q1 \in Quorum_c, Q2, Q3 \in Quorum_f : \E N \in Node : N \in Q1 /\ N \in Q2 /\ N \in Q3

Init ==
  /\ vote = [N \in Node |-> [R \in Round |-> [V \in Value |-> FALSE]]]
  /\ decision = [R \in Round |-> [V \in Value |-> FALSE]]
  /\ any_msg = [R \in Round |-> FALSE]
  /\ fast \in [Round -> BOOLEAN]

propose_1(r, q, maxr, v, v2) ==
  /\ r # None
  /\ ~any_msg[r]
  /\ maxr # None
  /\ \E N \in Node : N \in q /\ maxr < r /\ vote[N][maxr][v]
  /\ \A N \in Node, MAXR \in Round, V \in Value : (N \in q /\ MAXR < r /\ vote[N][MAXR][V]) => (MAXR <= maxr)
  /\ \E F \in Quorum_f : \A N \in Node : ~(N \in F /\ N \in q /\ ~vote[N][maxr][v2])
  /\ UNCHANGED<<vote, decision, any_msg, fast>>

propose_2(r, q, maxr, v) ==
  /\ r # None
  /\ ~any_msg[r]
  /\ maxr # None
  /\ \E N \in Node : N \in q /\ maxr < r /\ vote[N][maxr][v]
  /\ \A N \in Node, MAXR \in Round, V \in Value : (N \in q /\ MAXR < r /\ vote[N][MAXR][V]) => (MAXR <= maxr)
  /\ \A V2 \in Value, F \in Quorum_f : \E N \in Node : N \in F /\ N \in q /\ ~vote[N][maxr][V2]
  /\ UNCHANGED<<vote, decision, any_msg, fast>>

propose_3(r, q, v) ==
  /\ r # None
  /\ ~any_msg[r]
  /\ \A N \in Node, MAXR \in Round, V \in Value : ~(N \in q /\ MAXR < r /\ vote[N][MAXR][V])
  /\ fast[r]
  /\ any_msg' = [any_msg EXCEPT![r] = TRUE]
  /\ UNCHANGED<<vote, decision, fast>>

propose_4(r, q, v) ==
  /\ r # None
  /\ ~any_msg[r]
  /\ \A N \in Node, MAXR \in Round, V \in Value : ~(N \in q /\ MAXR < r /\ vote[N][MAXR][V])
  /\ ~fast[r]
  /\ UNCHANGED<<vote, decision, any_msg, fast>>

cast_vote_p(n, v, r) ==
  /\ r # None
  /\ \A V \in Value : ~vote[n][r][V]
  /\ vote' = [vote EXCEPT![n][r][v] = TRUE]
  /\ UNCHANGED<<decision, any_msg, fast>>

cast_vote_a(n, v, r) ==
  /\ r # None
  /\ \A V \in Value : ~vote[n][r][V]
  /\ any_msg[r]
  /\ vote' = [vote EXCEPT![n][r][v] = TRUE]
  /\ UNCHANGED<<decision, any_msg, fast>>

decide_c(r, v, q) ==
  /\ r # None
  /\ ~fast[r]
  /\ \A N \in q : vote[N][r][v]
  /\ decision' = [decision EXCEPT![r][v] = TRUE]
  /\ UNCHANGED<<vote, any_msg, fast>>

decide_f(r, v, q) ==
  /\ r # None
  /\ fast[r]
  /\ \A N \in q : vote[N][r][v]
  /\ decision' = [decision EXCEPT![r][v] = TRUE]
  /\ UNCHANGED<<vote, any_msg, fast>>

Next ==
  \/ \E r \in Round, q \in Quorum_c, maxr \in Round, v,v2 \in Value : propose_1(r, q, maxr, v, v2)
  \/ \E r \in Round, q \in Quorum_c, maxr \in Round, v \in Value : propose_2(r, q, maxr, v)
  \/ \E r \in Round, q \in Quorum_c, v \in Value : propose_3(r, q, v)
  \/ \E r \in Round, q \in Quorum_c, v \in Value : propose_4(r, q, v)
  \/ \E n \in Node, v \in Value, r \in Round : cast_vote_p(n, v, r)
  \/ \E n \in Node, v \in Value, r \in Round : cast_vote_a(n, v, r)
  \/ \E r \in Round, v \in Value, q \in Quorum_c : decide_c(r, v, q)
  \/ \E r \in Round, v \in Value, q \in Quorum_f : decide_f(r, v, q)

Spec == Init /\ [][Next]_vars

Safety == \A R1,R2 \in Round, V1,V2 \in Value : (decision[R1][V1] /\ decision[R2][V2]) => (V1 = V2)

======
