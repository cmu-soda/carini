--------------------------- MODULE T1_hist ---------------------------
EXTENDS Naturals

CONSTANTS Round, Value, Quorum, Node

VARIABLES Fluent22_62, one_b, one_a, Fluent20_62, Fluent21_62, left_round, vote

vars == <<Fluent22_62, one_b, one_a, Fluent20_62, Fluent21_62, left_round, vote>>

CandSep ==
\A var0 \in Round : \A var1 \in Value : (Fluent22_62[var1][var0]) => ((Fluent21_62[var1][var0]) => (Fluent20_62[var1][var0]))

None == 0

Init ==
/\ one_a = [r \in Round |-> FALSE]
/\ one_b = [n \in Node |-> [r \in Round |-> FALSE]]
/\ left_round = [n \in Node |-> [r \in Round |-> FALSE]]
/\ vote = [n \in Node |-> [r \in Round |-> [v \in Value |-> FALSE]]]
/\ Fluent22_62 = [ x0 \in Value |-> [ x1 \in Round |-> FALSE]]
/\ Fluent20_62 = [ x0 \in Value |-> [ x1 \in Round |-> FALSE]]
/\ Fluent21_62 = [ x0 \in Value |-> [ x1 \in Round |-> FALSE]]

send_1a(r) ==
/\ r /= None
/\ one_a' = [one_a EXCEPT![r] = TRUE]
/\ UNCHANGED <<one_b,left_round,vote>>
/\ UNCHANGED<<Fluent22_62, Fluent20_62, Fluent21_62>>

join_round(n,r) ==
/\ r /= None
/\ one_a[r]
/\ ~(left_round[n][r])
/\ one_b' = [one_b EXCEPT![n][r] = TRUE]
/\ left_round' = [N \in Node |-> [R \in Round |-> (left_round[N][R] \/ (N = n /\ ~(r <= R)))]]
/\ UNCHANGED <<one_a,vote>>
/\ UNCHANGED<<Fluent22_62, Fluent20_62, Fluent21_62>>

propose(r,q,maxr,v) ==
/\ r /= None
/\ (\A N \in Node : ((N \in q) => one_b[N][r]))
/\ (maxr = None => (\A N \in Node, MAXR \in Round, V \in Value : ~((((N \in q) /\ ~(r <= MAXR)) /\ vote[N][MAXR][V]))))
/\ (maxr /= None => ((\E N \in Node : (((N \in q) /\ ~(r <= maxr)) /\ vote[N][maxr][v])) /\ (\A N \in Node, MAXR \in Round, V \in Value : ((((N \in q) /\ ~(r <= MAXR)) /\ vote[N][MAXR][V]) => MAXR <= maxr))))
/\ UNCHANGED <<one_a,one_b,left_round,vote>>
/\ Fluent22_62' = [Fluent22_62 EXCEPT ![v][r] = TRUE]
/\ Fluent20_62' = [[x0 \in Value |-> [x1 \in Round |-> FALSE]] EXCEPT ![v][r] = TRUE]
/\ UNCHANGED<<Fluent21_62>>

cast_vote(n,v,r) ==
/\ r /= None
/\ ~(left_round[n][r])
/\ vote' = [vote EXCEPT![n][r][v] = TRUE]
/\ UNCHANGED <<one_a,one_b,left_round>>
/\ Fluent21_62' = [Fluent21_62 EXCEPT ![v][r] = TRUE]
/\ UNCHANGED<<Fluent22_62, Fluent20_62>>

decide(r,v,q) ==
/\ r /= None
/\ (\A N \in Node : ((N \in q) => vote[N][r][v]))
/\ UNCHANGED <<one_a,one_b,left_round,vote>>
/\ UNCHANGED<<Fluent22_62, Fluent20_62, Fluent21_62>>

Next ==
\/ (\E r \in Round : send_1a(r))
\/ (\E n \in Node, r \in Round : join_round(n,r))
\/ (\E r \in Round, q \in Quorum, maxr \in Round, v \in Value : propose(r,q,maxr,v))
\/ (\E n \in Node, v \in Value, r \in Round : cast_vote(n,v,r))
\/ (\E r \in Round, v \in Value, q \in Quorum : decide(r,v,q))

Spec == (Init /\ [][Next]_vars)
=============================================================================
