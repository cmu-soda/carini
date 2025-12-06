--------------------------- MODULE C1_hist ---------------------------
EXTENDS Naturals

CONSTANTS Round, Value, Quorum, Node

VARIABLES decision, Fluent10_50, Fluent9_50, left_round, Fluent8_50, vote

vars == <<decision, Fluent10_50, Fluent9_50, left_round, Fluent8_50, vote>>

CandSep ==
\A var0 \in Round : (Fluent9_50[var0]) => ((Fluent8_50[var0]) => (Fluent10_50[var0]))

None == 0

Init ==
/\ left_round = [n \in Node |-> [r \in Round |-> FALSE]]
/\ vote = [n \in Node |-> [r \in Round |-> [v \in Value |-> FALSE]]]
/\ decision = [r \in Round |-> [v \in Value |-> FALSE]]
/\ Fluent10_50 = [ x0 \in Round |-> FALSE]
/\ Fluent9_50 = [ x0 \in Round |-> FALSE]
/\ Fluent8_50 = [ x0 \in Round |-> FALSE]

join_round(n,r) ==
/\ r /= None
/\ ~(left_round[n][r])
/\ left_round' = [N \in Node |-> [R \in Round |-> (left_round[N][R] \/ (N = n /\ ~(r <= R)))]]
/\ UNCHANGED <<vote,decision>>
/\ Fluent10_50' = [Fluent10_50 EXCEPT ![r] = Fluent9_50[r]]
/\ Fluent9_50' = [Fluent9_50 EXCEPT ![r] = TRUE]
/\ UNCHANGED<<Fluent8_50>>
/\ CandSep'

propose(r,q,maxr,v) ==
/\ r /= None
/\ (maxr = None => (\A N \in Node, MAXR \in Round, V \in Value : ~((((N \in q) /\ ~(r <= MAXR)) /\ vote[N][MAXR][V]))))
/\ (maxr /= None => ((\E N \in Node : (((N \in q) /\ ~(r <= maxr)) /\ vote[N][maxr][v])) /\ (\A N \in Node, MAXR \in Round, V \in Value : ((((N \in q) /\ ~(r <= MAXR)) /\ vote[N][MAXR][V]) => MAXR <= maxr))))
/\ UNCHANGED <<left_round,vote,decision>>
/\ Fluent8_50' = [Fluent8_50 EXCEPT ![r] = TRUE]
/\ UNCHANGED<<Fluent10_50, Fluent9_50>>
/\ CandSep'

cast_vote(n,v,r) ==
/\ r /= None
/\ ~(left_round[n][r])
/\ vote' = [vote EXCEPT![n][r][v] = TRUE]
/\ UNCHANGED <<left_round,decision>>
/\ UNCHANGED<<Fluent10_50, Fluent9_50, Fluent8_50>>
/\ CandSep'

decide(r,v,q) ==
/\ r /= None
/\ (\A N \in Node : ((N \in q) => vote[N][r][v]))
/\ decision' = [decision EXCEPT![r][v] = TRUE]
/\ UNCHANGED <<left_round,vote>>
/\ UNCHANGED<<Fluent10_50, Fluent9_50, Fluent8_50>>
/\ CandSep'

Next ==
\/ (\E n \in Node, r \in Round : join_round(n,r))
\/ (\E r \in Round, q \in Quorum, maxr \in Round, v \in Value : propose(r,q,maxr,v))
\/ (\E n \in Node, v \in Value, r \in Round : cast_vote(n,v,r))
\/ (\E r \in Round, v \in Value, q \in Quorum : decide(r,v,q))

Spec == (Init /\ [][Next]_vars)

Safety == (\A R1,R2 \in Round, V1,V2 \in Value : ((decision[R1][V1] /\ decision[R2][V2]) => V1 = V2))
=============================================================================
