--------------------------- MODULE T1_hist ---------------------------
EXTENDS Naturals

CONSTANTS Round, Value, Quorum, Node

VARIABLES Fluent11_49, one_b, one_a, left_round, Fluent12_49

vars == <<Fluent11_49, one_b, one_a, left_round, Fluent12_49>>

CandSep ==
\A var0 \in Node : \E var1 \in Value : \E var2 \in Round : (Fluent12_49[var2][var1][var0]) => (~(Fluent11_49[var2][var1]))

None == 0

Init ==
/\ one_a = [r \in Round |-> FALSE]
/\ one_b = [n \in Node |-> [r \in Round |-> FALSE]]
/\ left_round = [n \in Node |-> [r \in Round |-> FALSE]]
/\ Fluent11_49 = [ x0 \in Round |-> [ x1 \in Value |-> FALSE]]
/\ Fluent12_49 = [ x0 \in Round |-> [ x1 \in Value |-> [ x2 \in Node |-> FALSE]]]

send_1a(r) ==
/\ r /= None
/\ one_a' = [one_a EXCEPT![r] = TRUE]
/\ UNCHANGED <<one_b,left_round>>
/\ UNCHANGED<<Fluent11_49, Fluent12_49>>

join_round(n,r) ==
/\ r /= None
/\ one_a[r]
/\ ~(left_round[n][r])
/\ one_b' = [one_b EXCEPT![n][r] = TRUE]
/\ left_round' = [N \in Node |-> [R \in Round |-> (left_round[N][R] \/ (N = n /\ ~(r <= R)))]]
/\ UNCHANGED <<one_a>>
/\ UNCHANGED<<Fluent11_49, Fluent12_49>>

propose(r,q,maxr,v) ==
/\ (\A N \in Node : ((N \in q) => one_b[N][r]))
/\ UNCHANGED <<one_a,one_b,left_round>>
/\ Fluent11_49' = [[Fluent11_49 EXCEPT ![r] = [x0 \in Value |-> TRUE]] EXCEPT ![maxr][v] = TRUE]
/\ Fluent12_49' = [Fluent12_49 EXCEPT ![r][v] = [x0 \in Node |-> TRUE]]
/\ UNCHANGED<<>>

cast_vote(n,v,r) ==
/\ r /= None
/\ ~(left_round[n][r])
/\ UNCHANGED <<one_a,one_b,left_round>>
/\ Fluent12_49' = [x0 \in Round |-> [x1 \in Value |-> [x2 \in Node |-> Fluent12_49[r][v][n]]]]
/\ UNCHANGED<<Fluent11_49>>

Next ==
\/ (\E r \in Round : send_1a(r))
\/ (\E n \in Node, r \in Round : join_round(n,r))
\/ (\E r \in Round, q \in Quorum, maxr \in Round, v \in Value : propose(r,q,maxr,v))
\/ (\E n \in Node, v \in Value, r \in Round : cast_vote(n,v,r))

Spec == (Init /\ [][Next]_vars)
=============================================================================
