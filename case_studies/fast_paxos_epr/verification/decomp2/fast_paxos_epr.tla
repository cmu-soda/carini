---- MODULE fast_paxos_epr ----
EXTENDS Naturals

CONSTANTS Node, Value, Quorum_c, Quorum_f, Round

VARIABLES one_a, one_b, left_round, proposal, vote, decision, any_msg, fast

vars == <<one_a, one_b, left_round, proposal, vote, decision, any_msg, fast>>

None == 0

ASSUME None \in Round
ASSUME \A Q1, Q2 \in Quorum_c : \E N \in Node : N \in Q1 /\ N \in Q2
ASSUME \A Q1 \in Quorum_c, Q2, Q3 \in Quorum_f : \E N \in Node : N \in Q1 /\ N \in Q2 /\ N \in Q3

Init ==
  /\ one_a = [R \in Round |-> FALSE]
  /\ one_b = [N \in Node |-> [R \in Round |-> FALSE]]
  /\ left_round = [N \in Node |-> [R \in Round |-> FALSE]]
  /\ proposal = [R \in Round |-> [V \in Value |-> FALSE]]
  /\ vote = [N \in Node |-> [R \in Round |-> [V \in Value |-> FALSE]]]
  /\ decision = [R \in Round |-> [V \in Value |-> FALSE]]
  /\ any_msg = [R \in Round |-> FALSE]
  /\ fast \in [Round -> BOOLEAN]

send_1a(r) ==
  /\ r # None
  /\ one_a' = [one_a EXCEPT![r] = TRUE]
  /\ UNCHANGED<<one_b, left_round, proposal, vote, decision, any_msg, fast>>

join_round(n, r) ==
  /\ r # None
  /\ one_a[r]
  /\ ~left_round[n][r]
  /\ one_b' = [one_b EXCEPT![n][r] = TRUE]
  /\ left_round' = [N \in Node |-> [R \in Round |-> left_round[N][R] \/ (N = n /\ R < r)]]
  /\ UNCHANGED<<one_a, proposal, vote, decision, any_msg, fast>>

propose_1(r, q, maxr, v, v2) ==
  /\ r # None
  /\ \A V \in Value : ~proposal[r][V]
  /\ ~any_msg[r]
  /\ \A N \in q : one_b[N][r]
  /\ maxr # None
  /\ \E N \in Node : N \in q /\ maxr < r /\ vote[N][maxr][v]
  /\ \A N \in Node, MAXR \in Round, V \in Value : (N \in q /\ MAXR < r /\ vote[N][MAXR][V]) => (MAXR <= maxr)
  /\ \E F \in Quorum_f : \A N \in Node : ~(N \in F /\ N \in q /\ ~vote[N][maxr][v2])
  /\ proposal' = [proposal EXCEPT![r][v2] = TRUE]
  /\ UNCHANGED<<one_a, one_b, left_round, vote, decision, any_msg, fast>>

propose_2(r, q, maxr, v) ==
  /\ r # None
  /\ \A V \in Value : ~proposal[r][V]
  /\ ~any_msg[r]
  /\ \A N \in q : one_b[N][r]
  /\ maxr # None
  /\ \E N \in Node : N \in q /\ maxr < r /\ vote[N][maxr][v]
  /\ \A N \in Node, MAXR \in Round, V \in Value : (N \in q /\ MAXR < r /\ vote[N][MAXR][V]) => (MAXR <= maxr)
  /\ \A V2 \in Value, F \in Quorum_f : \E N \in Node : N \in F /\ N \in q /\ ~vote[N][maxr][V2]
  /\ proposal' = [proposal EXCEPT![r][v] = TRUE]
  /\ UNCHANGED<<one_a, one_b, left_round, vote, decision, any_msg, fast>>

propose_3(r, q, v) ==
  /\ r # None
  /\ \A V \in Value : ~proposal[r][V]
  /\ ~any_msg[r]
  /\ \A N \in q : one_b[N][r]
  /\ \A N \in Node, MAXR \in Round, V \in Value : ~(N \in q /\ MAXR < r /\ vote[N][MAXR][V])
  /\ fast[r]
  /\ any_msg' = [any_msg EXCEPT![r] = TRUE]
  /\ UNCHANGED<<one_a, one_b, left_round, proposal, vote, decision, fast>>

propose_4(r, q, v) ==
  /\ r # None
  /\ \A V \in Value : ~proposal[r][V]
  /\ ~any_msg[r]
  /\ \A N \in q : one_b[N][r]
  /\ \A N \in Node, MAXR \in Round, V \in Value : ~(N \in q /\ MAXR < r /\ vote[N][MAXR][V])
  /\ ~fast[r]
  /\ proposal' = [proposal EXCEPT![r][v] = TRUE]
  /\ UNCHANGED<<one_a, one_b, left_round, vote, decision, any_msg, fast>>

cast_vote_p(n, v, r) ==
  /\ r # None
  /\ ~left_round[n][r]
  /\ \A V \in Value : ~vote[n][r][V]
  /\ proposal[r][v]
  /\ vote' = [vote EXCEPT![n][r][v] = TRUE]
  /\ UNCHANGED<<one_a, one_b, left_round, proposal, decision, any_msg, fast>>

cast_vote_a(n, v, r) ==
  /\ r # None
  /\ ~left_round[n][r]
  /\ \A V \in Value : ~vote[n][r][V]
  /\ any_msg[r]
  /\ vote' = [vote EXCEPT![n][r][v] = TRUE]
  /\ UNCHANGED<<one_a, one_b, left_round, proposal, decision, any_msg, fast>>

decide_c(r, v, q) ==
  /\ r # None
  /\ ~fast[r]
  /\ \A N \in q : vote[N][r][v]
  /\ decision' = [decision EXCEPT![r][v] = TRUE]
  /\ UNCHANGED<<one_a, one_b, left_round, proposal, vote, any_msg, fast>>

decide_f(r, v, q) ==
  /\ r # None
  /\ fast[r]
  /\ \A N \in q : vote[N][r][v]
  /\ decision' = [decision EXCEPT![r][v] = TRUE]
  /\ UNCHANGED<<one_a, one_b, left_round, proposal, vote, any_msg, fast>>

Next ==
  \/ \E r \in Round : send_1a(r)
  \/ \E n \in Node, r \in Round : join_round(n, r)
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
