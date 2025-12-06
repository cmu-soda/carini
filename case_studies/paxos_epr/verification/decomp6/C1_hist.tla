--------------------------- MODULE C1_hist ---------------------------
EXTENDS Naturals

CONSTANTS Round, Value, Quorum, Node

VARIABLES decision, Fluent13_25, left_round, Fluent14_25

vars == <<decision, Fluent13_25, left_round, Fluent14_25>>

CandSep ==
\A var0 \in Node : (Fluent14_25[var0]) => (Fluent13_25[var0])

None == 0

Init ==
/\ left_round = [n \in Node |-> [r \in Round |-> FALSE]]
/\ decision = [r \in Round |-> [v \in Value |-> FALSE]]
/\ Fluent13_25 = [ x0 \in Node |-> FALSE]
/\ Fluent14_25 = [ x0 \in Node |-> FALSE]

join_round(n,r) ==
/\ r /= None
/\ ~(left_round[n][r])
/\ left_round' = [N \in Node |-> [R \in Round |-> (left_round[N][R] \/ (N = n /\ ~(r <= R)))]]
/\ UNCHANGED <<decision>>
/\ Fluent13_25' = [[x0 \in Node |-> TRUE] EXCEPT ![n] = Fluent13_25[n]]
/\ UNCHANGED<<Fluent14_25>>
/\ CandSep'

cast_vote(n,v,r) ==
/\ r /= None
/\ ~(left_round[n][r])
/\ UNCHANGED <<left_round,decision>>
/\ Fluent14_25' = [Fluent14_25 EXCEPT ![n] = TRUE]
/\ UNCHANGED<<Fluent13_25>>
/\ CandSep'

decide(r,v,q) ==
/\ r /= None
/\ decision' = [decision EXCEPT![r][v] = TRUE]
/\ UNCHANGED <<left_round>>
/\ UNCHANGED<<Fluent13_25, Fluent14_25>>
/\ CandSep'

Next ==
\/ (\E n \in Node, r \in Round : join_round(n,r))
\/ (\E n \in Node, v \in Value, r \in Round : cast_vote(n,v,r))
\/ (\E r \in Round, v \in Value, q \in Quorum : decide(r,v,q))

Spec == (Init /\ [][Next]_vars)

Safety == (\A R1,R2 \in Round, V1,V2 \in Value : ((decision[R1][V1] /\ decision[R2][V2]) => V1 = V2))
=============================================================================
