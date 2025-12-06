--------------------------- MODULE C1_hist ---------------------------
EXTENDS Naturals

CONSTANTS Round, Value, Quorum, Node

VARIABLES proposal, decision, vote

vars == <<proposal, decision, vote>>

CandSep ==
TRUE

None == 0

Init ==
/\ proposal = [r \in Round |-> [v \in Value |-> FALSE]]
/\ vote = [n \in Node |-> [r \in Round |-> [v \in Value |-> FALSE]]]
/\ decision = [r \in Round |-> [v \in Value |-> FALSE]]

propose(r,q,maxr,v) ==
/\ r /= None
/\ (\A V \in Value : ~(proposal[r][V]))
/\ (maxr = None => (\A N \in Node, MAXR \in Round, V \in Value : ~((((N \in q) /\ ~(r <= MAXR)) /\ vote[N][MAXR][V]))))
/\ (maxr /= None => ((\E N \in Node : (((N \in q) /\ ~(r <= maxr)) /\ vote[N][maxr][v])) /\ (\A N \in Node, MAXR \in Round, V \in Value : ((((N \in q) /\ ~(r <= MAXR)) /\ vote[N][MAXR][V]) => MAXR <= maxr))))
/\ proposal' = [proposal EXCEPT![r][v] = TRUE]
/\ UNCHANGED <<vote,decision>>
/\ UNCHANGED<<>>
/\ CandSep'

cast_vote(n,v,r) ==
/\ r /= None
/\ proposal[r][v]
/\ vote' = [vote EXCEPT![n][r][v] = TRUE]
/\ UNCHANGED <<proposal,decision>>
/\ UNCHANGED<<>>
/\ CandSep'

decide(r,v,q) ==
/\ r /= None
/\ (\A N \in Node : ((N \in q) => vote[N][r][v]))
/\ decision' = [decision EXCEPT![r][v] = TRUE]
/\ UNCHANGED <<proposal,vote>>
/\ UNCHANGED<<>>
/\ CandSep'

Next ==
\/ (\E r \in Round, q \in Quorum, maxr \in Round, v \in Value : propose(r,q,maxr,v))
\/ (\E n \in Node, v \in Value, r \in Round : cast_vote(n,v,r))
\/ (\E r \in Round, v \in Value, q \in Quorum : decide(r,v,q))

Spec == (Init /\ [][Next]_vars)

Safety == (\A R1,R2 \in Round, V1,V2 \in Value : ((decision[R1][V1] /\ decision[R2][V2]) => V1 = V2))
=============================================================================
