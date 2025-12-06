--------------------------- MODULE T1_hist ---------------------------
EXTENDS Naturals

CONSTANTS Round, Value, Quorum, Node

VARIABLES proposal, Fluent29_0, one_b, one_a, vote

vars == <<proposal, Fluent29_0, one_b, one_a, vote>>

CandSep ==
\A var0 \in Quorum : ~(Fluent29_0[var0])

None == 0

Init ==
/\ one_a = [r \in Round |-> FALSE]
/\ one_b = [n \in Node |-> [r \in Round |-> FALSE]]
/\ proposal = [r \in Round |-> [v \in Value |-> FALSE]]
/\ vote = [n \in Node |-> [r \in Round |-> [v \in Value |-> FALSE]]]
/\ Fluent29_0 = [ x0 \in Quorum |-> FALSE]

send_1a(r) ==
/\ r /= None
/\ one_a' = [one_a EXCEPT![r] = TRUE]
/\ UNCHANGED <<one_b,proposal,vote>>
/\ UNCHANGED<<Fluent29_0>>

join_round(n,r) ==
/\ r /= None
/\ one_a[r]
/\ one_b' = [one_b EXCEPT![n][r] = TRUE]
/\ UNCHANGED <<one_a,proposal,vote>>
/\ UNCHANGED<<Fluent29_0>>

propose(r,q,maxr,v) ==
/\ r /= None
/\ (\A V \in Value : ~(proposal[r][V]))
/\ (\A N \in Node : ((N \in q) => one_b[N][r]))
/\ (maxr = None => (\A N \in Node, MAXR \in Round, V \in Value : ~((((N \in q) /\ ~(r <= MAXR)) /\ vote[N][MAXR][V]))))
/\ (maxr /= None => ((\E N \in Node : (((N \in q) /\ ~(r <= maxr)) /\ vote[N][maxr][v])) /\ (\A N \in Node, MAXR \in Round, V \in Value : ((((N \in q) /\ ~(r <= MAXR)) /\ vote[N][MAXR][V]) => MAXR <= maxr))))
/\ proposal' = [proposal EXCEPT![r][v] = TRUE]
/\ UNCHANGED <<one_a,one_b,vote>>
/\ UNCHANGED<<Fluent29_0>>

cast_vote(n,v,r) ==
/\ r /= None
/\ proposal[r][v]
/\ vote' = [vote EXCEPT![n][r][v] = TRUE]
/\ UNCHANGED <<one_a,one_b,proposal>>
/\ Fluent29_0' = [x0 \in Quorum |-> TRUE]
/\ UNCHANGED<<>>

decide(r,v,q) ==
/\ r /= None
/\ (\A N \in Node : ((N \in q) => vote[N][r][v]))
/\ UNCHANGED <<one_a,one_b,proposal,vote>>
/\ UNCHANGED<<Fluent29_0>>

Next ==
\/ (\E r \in Round : send_1a(r))
\/ (\E n \in Node, r \in Round : join_round(n,r))
\/ (\E r \in Round, q \in Quorum, maxr \in Round, v \in Value : propose(r,q,maxr,v))
\/ (\E n \in Node, v \in Value, r \in Round : cast_vote(n,v,r))
\/ (\E r \in Round, v \in Value, q \in Quorum : decide(r,v,q))

Spec == (Init /\ [][Next]_vars)
=============================================================================
