--------------------------- MODULE C1_hist ---------------------------
EXTENDS Naturals

CONSTANTS Round, Value, Quorum, Node

VARIABLES proposal, decision, Fluent7_3, Fluent8_3

vars == <<proposal, decision, Fluent7_3, Fluent8_3>>

CandSep ==
\A var0 \in Round : (Fluent8_3[var0]) => (Fluent7_3[var0])

None == 0

Init ==
/\ proposal = [r \in Round |-> [v \in Value |-> FALSE]]
/\ decision = [r \in Round |-> [v \in Value |-> FALSE]]
/\ Fluent7_3 = [ x0 \in Round |-> FALSE]
/\ Fluent8_3 = [ x0 \in Round |-> FALSE]

propose(r,maxr,v) ==
/\ (\E q \in Quorum : (r /= None /\ (\A V \in Value : ~(proposal[r][V])) /\ proposal' = [proposal EXCEPT![r][v] = TRUE] /\ UNCHANGED <<decision>>))
/\ UNCHANGED<<Fluent7_3, Fluent8_3>>
/\ CandSep'

cast_vote(n,v,r) ==
/\ r /= None
/\ proposal[r][v]
/\ UNCHANGED <<proposal,decision>>
/\ Fluent7_3' = [Fluent7_3 EXCEPT ![r] = TRUE]
/\ UNCHANGED<<Fluent8_3>>
/\ CandSep'

decide(r,v) ==
/\ (\E q \in Quorum : (r /= None /\ decision' = [decision EXCEPT![r][v] = TRUE] /\ UNCHANGED <<proposal>>))
/\ Fluent8_3' = [Fluent8_3 EXCEPT ![r] = TRUE]
/\ UNCHANGED<<Fluent7_3>>
/\ CandSep'

Next ==
\/ (\E r \in Round, maxr \in Round, v \in Value : propose(r,maxr,v))
\/ (\E n \in Node, v \in Value, r \in Round : cast_vote(n,v,r))
\/ (\E r \in Round, v \in Value : decide(r,v))

Spec == (Init /\ [][Next]_vars)

Safety == (\A R1,R2 \in Round, V1,V2 \in Value : ((decision[R1][V1] /\ decision[R2][V2]) => V1 = V2))
=============================================================================
