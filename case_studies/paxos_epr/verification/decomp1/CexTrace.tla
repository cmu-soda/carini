--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS Quorum, n1, n2, n3, Node, NUM2, NUM0, NUM1, _n2n3_, _n1n2n3_, Value, Round, _n1n3_, v1, _n1n2_, v2

VARIABLES proposal, err, one_b, one_a, left_round, cexTraceIdx

vars == <<proposal, err, one_b, one_a, left_round, cexTraceIdx>>

NoErr == err = FALSE

None == 0

Init ==
/\ one_a = [r \in Round |-> FALSE]
/\ one_b = [n \in Node |-> [r \in Round |-> FALSE]]
/\ left_round = [n \in Node |-> [r \in Round |-> FALSE]]
/\ proposal = [r \in Round |-> [v \in Value |-> FALSE]]
/\ cexTraceIdx = 0
/\ err = FALSE

send_1a(r) ==
/\ r /= None
/\ one_a' = [one_a EXCEPT![r] = TRUE]
/\ UNCHANGED <<one_b,left_round,proposal>>
/\ cexTraceIdx' = cexTraceIdx

join_round(n,r) ==
/\ r /= None
/\ one_a[r]
/\ ~(left_round[n][r])
/\ one_b' = [one_b EXCEPT![n][r] = TRUE]
/\ left_round' = [N \in Node |-> [R \in Round |-> (left_round[N][R] \/ (N = n /\ ~(r <= R)))]]
/\ UNCHANGED <<one_a,proposal>>
/\ cexTraceIdx' = cexTraceIdx

propose(r,q,maxr,v) ==
/\ r /= None
/\ (\A V \in Value : ~(proposal[r][V]))
/\ (\A N \in Node : ((N \in q) => one_b[N][r]))
/\ proposal' = [proposal EXCEPT![r][v] = TRUE]
/\ UNCHANGED <<one_a,one_b,left_round>>
/\ cexTraceIdx' = cexTraceIdx + 1

cast_vote(n,v,r) ==
/\ r /= None
/\ ~(left_round[n][r])
/\ proposal[r][v]
/\ UNCHANGED <<one_a,one_b,left_round,proposal>>
/\ cexTraceIdx' = cexTraceIdx + 1

Next ==
\/ (\E r \in Round : send_1a(r))
\/ (\E n \in Node, r \in Round : join_round(n,r))
\/ (\E r \in Round, q \in Quorum, maxr \in Round, v \in Value : propose(r,q,maxr,v))
\/ (\E n \in Node, v \in Value, r \in Round : cast_vote(n,v,r))

Spec == (Init /\ [][Next]_vars)

TraceConstraint ==
/\ cexTraceIdx = 0 => cast_vote(n2,v2,1) /\ err' = TRUE
/\ cexTraceIdx >= 1 => FALSE

InternalAction == UNCHANGED<<cexTraceIdx,err>>

TraceConstraintSpec == Init /\ [][Next /\ (TraceConstraint \/ InternalAction)]_vars
=============================================================================
