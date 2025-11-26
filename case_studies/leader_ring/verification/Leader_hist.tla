--------------------------- MODULE Leader_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Id

VARIABLES elected, Fluent3_3, Fluent2_3

vars == <<elected, Fluent3_3, Fluent2_3>>

CandSep ==
/\ \A var0 \in Id : (Fluent2_3[var0]) => (Fluent3_3[var0])

id == @@(@@(:>(0,5),:>(1,3)),:>(2,8))

TypeOK ==
/\ \subseteq(elected,Node)

Init ==
/\ elected = {}
/\ Fluent3_3 = [ x0 \in Id |-> FALSE]
/\ Fluent2_3 = [ x0 \in Id |-> FALSE]

Send(i,m) ==
/\ m = id[i]
/\ UNCHANGED elected
/\ Fluent3_3' = [Fluent3_3 EXCEPT ![m] = TRUE]
/\ UNCHANGED<<Fluent2_3>>
/\ CandSep'

Delete(i,m) ==
/\ m <= id[i]
/\ IF m = id[i] THEN elected' = (elected \cup {i}) ELSE UNCHANGED elected
/\ Fluent2_3' = [Fluent2_3 EXCEPT ![m] = TRUE]
/\ UNCHANGED<<Fluent3_3>>
/\ CandSep'

Propagate(i,m) ==
/\ m > id[i]
/\ UNCHANGED elected
/\ UNCHANGED<<Fluent3_3, Fluent2_3>>
/\ CandSep'

Next ==
\E i \in Node, m \in Id :
\/ Send(i,m)
\/ Delete(i,m)
\/ Propagate(i,m)

Spec == (Init /\ [][Next]_elected)

AtMostOneLeader == Cardinality(elected) <= 1
=============================================================================
