---- MODULE paxos_epr ----
EXTENDS Naturals

CONSTANTS Round, Value, Quorum, Node

VARIABLES one_a, one_b, left_round, proposal, vote, decision

vars == <<one_a, one_b, left_round, proposal, vote, decision>>

None == 0

ASSUME None \in Round

Init ==
  /\ one_a = [r \in Round |-> FALSE]
  /\ one_b = [n \in Node |-> [r \in Round |-> FALSE]]
  /\ left_round = [n \in Node |-> [r \in Round |-> FALSE]]
  /\ proposal = [r \in Round |-> [v \in Value |-> FALSE]]
  /\ vote = [n \in Node |-> [r \in Round |-> [v \in Value |-> FALSE]]]
  /\ decision = [r \in Round |-> [v \in Value |-> FALSE]]

send_1a(r) ==
  /\ r # None
  /\ one_a' = [one_a EXCEPT![r] = TRUE]
  /\ UNCHANGED<<one_b, left_round, proposal, vote, decision>>

join_round(n, r) ==
  /\ r # None
  /\ one_a[r]
  /\ ~left_round[n][r]
  /\ one_b' = [one_b EXCEPT![n][r] = TRUE]
  /\ left_round' = [N \in Node |-> [R \in Round |-> left_round[N][R] \/ (N=n /\ ~(r <= R))]]
  /\ UNCHANGED<<one_a, proposal, vote, decision>>

propose(r, maxr, v) ==
  \E q \in Quorum :
  /\ r # None
  /\ \A V \in Value : ~proposal[r][V]
  /\ \A N \in Node : N \in q => one_b[N][r]
  /\ (maxr = None) => \A N \in Node, MAXR \in Round, V \in Value : ~(N \in q /\ ~(r <= MAXR) /\ vote[N][MAXR][V])
  /\ (maxr # None) =>
       /\ \E N \in Node : N \in q /\ ~(r <= maxr) /\ vote[N][maxr][v]
       /\ \A N \in Node, MAXR \in Round, V \in Value : (N \in q /\ ~(r <= MAXR) /\ vote[N][MAXR][V]) => MAXR <= maxr
  /\ proposal' = [proposal EXCEPT![r][v] = TRUE]
  /\ UNCHANGED<<one_a, one_b, left_round, vote, decision>>

cast_vote(n, v, r) ==
  /\ r # None
  /\ ~left_round[n][r]
  /\ proposal[r][v]
  /\ vote' = [vote EXCEPT![n][r][v] = TRUE]
  /\ UNCHANGED<<one_a, one_b, left_round, proposal, decision>>

decide(r, v) ==
  \E q \in Quorum :
  /\ r # None
  /\ \A N \in Node : N \in q => vote[N][r][v]
  /\ decision' = [decision EXCEPT![r][v] = TRUE]
  /\ UNCHANGED<<one_a, one_b, left_round, proposal, vote>>

Next ==
  \/ \E r \in Round : send_1a(r)
  \/ \E n \in Node, r \in Round : join_round(n, r)
  \/ \E r \in Round, maxr \in Round, v \in Value : propose(r, maxr, v)
  \/ \E n \in Node, v \in Value, r \in Round : cast_vote(n, v, r)
  \/ \E r \in Round, v \in Value : decide(r, v)

Spec == Init /\ [][Next]_vars

Safety == \A R1,R2 \in Round, V1,V2 \in Value : decision[R1][V1] /\ decision[R2][V2] => V1 = V2

======
