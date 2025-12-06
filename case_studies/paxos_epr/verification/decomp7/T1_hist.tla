--------------------------- MODULE T1_hist ---------------------------
EXTENDS Naturals

CONSTANTS Round, Value, Quorum, Node

VARIABLES proposal, one_b, one_a, Fluent28_28, Fluent29_28

vars == <<proposal, one_b, one_a, Fluent28_28, Fluent29_28>>

CandSep ==
\A var0 \in Quorum : \E var1 \in Node : \E var2 \in Value : (Fluent29_28[var2][var0]) => (~(Fluent28_28[var1]))

None == 0

Init ==
/\ one_a = [r \in Round |-> FALSE]
/\ one_b = [n \in Node |-> [r \in Round |-> FALSE]]
/\ proposal = [r \in Round |-> [v \in Value |-> FALSE]]
/\ Fluent28_28 = [ x0 \in Node |-> FALSE]
/\ Fluent29_28 = [ x0 \in Value |-> [ x1 \in Quorum |-> FALSE]]

send_1a(r) ==
/\ r /= None
/\ one_a' = [one_a EXCEPT![r] = TRUE]
/\ UNCHANGED <<one_b,proposal>>
/\ UNCHANGED<<Fluent28_28, Fluent29_28>>

join_round(n,r) ==
/\ r /= None
/\ one_a[r]
/\ one_b' = [one_b EXCEPT![n][r] = TRUE]
/\ UNCHANGED <<one_a,proposal>>
/\ Fluent28_28' = [Fluent28_28 EXCEPT ![n] = TRUE]
/\ UNCHANGED<<Fluent29_28>>

propose(r,q,maxr,v) ==
/\ r /= None
/\ (\A V \in Value : ~(proposal[r][V]))
/\ (\A N \in Node : ((N \in q) => one_b[N][r]))
/\ proposal' = [proposal EXCEPT![r][v] = TRUE]
/\ UNCHANGED <<one_a,one_b>>
/\ Fluent29_28' = [Fluent29_28 EXCEPT ![v][q] = TRUE]
/\ UNCHANGED<<Fluent28_28>>

cast_vote(n,v,r) ==
/\ r /= None
/\ proposal[r][v]
/\ UNCHANGED <<one_a,one_b,proposal>>
/\ UNCHANGED<<Fluent28_28, Fluent29_28>>

Next ==
\/ (\E r \in Round : send_1a(r))
\/ (\E n \in Node, r \in Round : join_round(n,r))
\/ (\E r \in Round, q \in Quorum, maxr \in Round, v \in Value : propose(r,q,maxr,v))
\/ (\E n \in Node, v \in Value, r \in Round : cast_vote(n,v,r))

Spec == (Init /\ [][Next]_vars)
=============================================================================
