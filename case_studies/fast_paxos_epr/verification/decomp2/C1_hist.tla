--------------------------- MODULE C1_hist ---------------------------
EXTENDS Naturals

CONSTANTS Round, Value, Node, Quorum_c, Quorum_f

VARIABLES fast, decision, Fluent5_45, Fluent4_45, vote

vars == <<fast, decision, Fluent5_45, Fluent4_45, vote>>

CandSep ==
\A var0 \in Quorum_c : \E var1 \in Value : (Fluent4_45[var0]) => (Fluent5_45[var1])

None == 0

Init ==
/\ vote = [N \in Node |-> [R \in Round |-> [V \in Value |-> FALSE]]]
/\ decision = [R \in Round |-> [V \in Value |-> FALSE]]
/\ (fast \in [Round -> BOOLEAN])
/\ Fluent5_45 = [ x0 \in Value |-> FALSE]
/\ Fluent4_45 = [ x0 \in Quorum_c |-> FALSE]

propose_1(r,q,maxr,v,v2) ==
/\ r /= None
/\ maxr /= None
/\ (\E N \in Node : (((N \in q) /\ maxr < r) /\ vote[N][maxr][v]))
/\ (\A N \in Node, MAXR \in Round, V \in Value : ((((N \in q) /\ MAXR < r) /\ vote[N][MAXR][V]) => MAXR <= maxr))
/\ (\E F \in Quorum_f : (\A N \in Node : ~((((N \in F) /\ (N \in q)) /\ ~(vote[N][maxr][v2])))))
/\ UNCHANGED <<vote,decision,fast>>
/\ Fluent5_45' = [Fluent5_45 EXCEPT ![v2] = TRUE]
/\ UNCHANGED<<Fluent4_45>>
/\ CandSep'

propose_2(r,q,maxr,v) ==
/\ r /= None
/\ maxr /= None
/\ (\E N \in Node : (((N \in q) /\ maxr < r) /\ vote[N][maxr][v]))
/\ (\A N \in Node, MAXR \in Round, V \in Value : ((((N \in q) /\ MAXR < r) /\ vote[N][MAXR][V]) => MAXR <= maxr))
/\ (\A V2 \in Value, F \in Quorum_f : (\E N \in Node : (((N \in F) /\ (N \in q)) /\ ~(vote[N][maxr][V2]))))
/\ UNCHANGED <<vote,decision,fast>>
/\ Fluent5_45' = [Fluent5_45 EXCEPT ![v] = TRUE]
/\ UNCHANGED<<Fluent4_45>>
/\ CandSep'

propose_3(r,q,v) ==
/\ r /= None
/\ (\A N \in Node, MAXR \in Round, V \in Value : ~((((N \in q) /\ MAXR < r) /\ vote[N][MAXR][V])))
/\ UNCHANGED <<vote,decision,fast>>
/\ Fluent5_45' = [Fluent5_45 EXCEPT ![v] = TRUE]
/\ UNCHANGED<<Fluent4_45>>
/\ CandSep'

propose_4(r,q,v) ==
/\ r /= None
/\ (\A N \in Node, MAXR \in Round, V \in Value : ~((((N \in q) /\ MAXR < r) /\ vote[N][MAXR][V])))
/\ UNCHANGED <<vote,decision,fast>>
/\ Fluent5_45' = [Fluent5_45 EXCEPT ![v] = TRUE]
/\ UNCHANGED<<Fluent4_45>>
/\ CandSep'

cast_vote(n,v,r) ==
/\ r /= None
/\ (\A V \in Value : ~(vote[n][r][V]))
/\ vote' = [vote EXCEPT![n][r][v] = TRUE]
/\ UNCHANGED <<decision,fast>>
/\ Fluent4_45' = [x0 \in Quorum_c |-> TRUE]
/\ UNCHANGED<<Fluent5_45>>
/\ CandSep'

decide_c(r,v,q) ==
/\ r /= None
/\ ~(fast[r])
/\ (\A N \in q : vote[N][r][v])
/\ decision' = [decision EXCEPT![r][v] = TRUE]
/\ UNCHANGED <<vote,fast>>
/\ UNCHANGED<<Fluent5_45, Fluent4_45>>
/\ CandSep'

decide_f(r,v,q) ==
/\ r /= None
/\ fast[r]
/\ (\A N \in q : vote[N][r][v])
/\ decision' = [decision EXCEPT![r][v] = TRUE]
/\ UNCHANGED <<vote,fast>>
/\ UNCHANGED<<Fluent5_45, Fluent4_45>>
/\ CandSep'

Next ==
\/ (\E r \in Round, q \in Quorum_c, maxr \in Round, v,v2 \in Value : propose_1(r,q,maxr,v,v2))
\/ (\E r \in Round, q \in Quorum_c, maxr \in Round, v \in Value : propose_2(r,q,maxr,v))
\/ (\E r \in Round, q \in Quorum_c, v \in Value : propose_3(r,q,v))
\/ (\E r \in Round, q \in Quorum_c, v \in Value : propose_4(r,q,v))
\/ (\E n \in Node, v \in Value, r \in Round : cast_vote(n,v,r))
\/ (\E r \in Round, v \in Value, q \in Quorum_c : decide_c(r,v,q))
\/ (\E r \in Round, v \in Value, q \in Quorum_f : decide_f(r,v,q))

Spec == (Init /\ [][Next]_vars)

Safety == (\A R1,R2 \in Round, V1,V2 \in Value : ((decision[R1][V1] /\ decision[R2][V2]) => V1 = V2))
=============================================================================
