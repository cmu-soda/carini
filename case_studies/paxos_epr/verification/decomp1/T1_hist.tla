--------------------------- MODULE T1_hist ---------------------------
EXTENDS Naturals

CONSTANTS Round, Value, Quorum, Node

VARIABLES proposal, one_b, one_a, left_round, Fluent1_10

vars == <<proposal, one_b, one_a, left_round, Fluent1_10>>

CandSep ==
\A var0 \in Round : ~(Fluent1_10[var0])

None == 0

Init ==
/\ one_a = [r \in Round |-> FALSE]
/\ one_b = [n \in Node |-> [r \in Round |-> FALSE]]
/\ left_round = [n \in Node |-> [r \in Round |-> FALSE]]
/\ proposal = [r \in Round |-> [v \in Value |-> FALSE]]
/\ Fluent1_10 = [ x0 \in Round |-> FALSE]

send_1a(r) ==
/\ r /= None
/\ one_a' = [one_a EXCEPT![r] = TRUE]
/\ UNCHANGED <<one_b,left_round,proposal>>
/\ UNCHANGED<<Fluent1_10>>

join_round(n,r) ==
/\ r /= None
/\ one_a[r]
/\ ~(left_round[n][r])
/\ one_b' = [one_b EXCEPT![n][r] = TRUE]
/\ left_round' = [N \in Node |-> [R \in Round |-> (left_round[N][R] \/ (N = n /\ ~(r <= R)))]]
/\ UNCHANGED <<one_a,proposal>>
/\ UNCHANGED<<Fluent1_10>>

propose(r,q,maxr,v) ==
/\ r /= None
/\ (\A V \in Value : ~(proposal[r][V]))
/\ (\A N \in Node : ((N \in q) => one_b[N][r]))
/\ proposal' = [proposal EXCEPT![r][v] = TRUE]
/\ UNCHANGED <<one_a,one_b,left_round>>
/\ UNCHANGED<<Fluent1_10>>

cast_vote(n,v,r) ==
/\ r /= None
/\ ~(left_round[n][r])
/\ proposal[r][v]
/\ UNCHANGED <<one_a,one_b,left_round,proposal>>
/\ Fluent1_10' = [Fluent1_10 EXCEPT ![r] = TRUE]
/\ UNCHANGED<<>>

Next ==
\/ (\E r \in Round : send_1a(r))
\/ (\E n \in Node, r \in Round : join_round(n,r))
\/ (\E r \in Round, q \in Quorum, maxr \in Round, v \in Value : propose(r,q,maxr,v))
\/ (\E n \in Node, v \in Value, r \in Round : cast_vote(n,v,r))

Spec == (Init /\ [][Next]_vars)
=============================================================================
