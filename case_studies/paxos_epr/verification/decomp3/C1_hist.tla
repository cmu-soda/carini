--------------------------- MODULE C1_hist ---------------------------
EXTENDS Naturals

CONSTANTS Round, Value, Quorum, Node

VARIABLES proposal, decision, Fluent4_22, Fluent5_22

vars == <<proposal, decision, Fluent4_22, Fluent5_22>>

CandSep ==
\A var0 \in Node : (Fluent4_22[var0]) => (Fluent5_22[var0])

None == 0

Init ==
/\ proposal = [r \in Round |-> [v \in Value |-> FALSE]]
/\ decision = [r \in Round |-> [v \in Value |-> FALSE]]
/\ Fluent4_22 = [ x0 \in Node |-> FALSE]
/\ Fluent5_22 = [ x0 \in Node |-> FALSE]

propose(r,q,maxr,v) ==
/\ r /= None
/\ (\A V \in Value : ~(proposal[r][V]))
/\ proposal' = [proposal EXCEPT![r][v] = TRUE]
/\ UNCHANGED <<decision>>
/\ UNCHANGED<<Fluent4_22, Fluent5_22>>
/\ CandSep'

cast_vote(n,v,r) ==
/\ r /= None
/\ proposal[r][v]
/\ UNCHANGED <<proposal,decision>>
/\ Fluent5_22' = [x0 \in Node |-> TRUE]
/\ UNCHANGED<<Fluent4_22>>
/\ CandSep'

decide(r,v,q) ==
/\ r /= None
/\ decision' = [decision EXCEPT![r][v] = TRUE]
/\ UNCHANGED <<proposal>>
/\ Fluent4_22' = [x0 \in Node |-> TRUE]
/\ UNCHANGED<<Fluent5_22>>
/\ CandSep'

Next ==
\/ (\E r \in Round, q \in Quorum, maxr \in Round, v \in Value : propose(r,q,maxr,v))
\/ (\E n \in Node, v \in Value, r \in Round : cast_vote(n,v,r))
\/ (\E r \in Round, v \in Value, q \in Quorum : decide(r,v,q))

Spec == (Init /\ [][Next]_vars)

Safety == (\A R1,R2 \in Round, V1,V2 \in Value : ((decision[R1][V1] /\ decision[R2][V2]) => V1 = V2))
=============================================================================
