--------------------------- MODULE Ring_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Id

VARIABLES Fluent7_1, Fluent6_1, inbox

vars == <<Fluent7_1, Fluent6_1, inbox>>

CandSep ==
\A var0 \in Id : \E var1 \in Node : (Fluent7_1[var0]) => (Fluent6_1[var0][var1])

N == Cardinality(Node)

id == @@(@@(:>(0,5),:>(1,3)),:>(2,8))

succ(n) == %((n + 1),N)

TypeOK ==
/\ (inbox \in [Node -> SUBSET(Id)])

Init ==
/\ inbox = [i \in Node |-> {}]
/\ Fluent7_1 = [ x0 \in Id |-> FALSE]
/\ Fluent6_1 = [ x0 \in Id |-> [ x1 \in Node |-> FALSE]]

Send(i,m) ==
/\ inbox' = [inbox EXCEPT![succ(i)] = (@ \cup {m})]
/\ Fluent7_1' = [Fluent7_1 EXCEPT ![m] = TRUE]
/\ Fluent6_1' = [Fluent6_1 EXCEPT ![m][i] = TRUE]
/\ UNCHANGED<<>>

Delete(i,m) ==
/\ (m \in inbox[i])
/\ inbox' = [inbox EXCEPT![i] = (@ \ {m})]
/\ Fluent6_1' = [Fluent6_1 EXCEPT ![m][i] = FALSE]
/\ UNCHANGED<<Fluent7_1>>

Propagate(i,m) ==
/\ (m \in inbox[i])
/\ inbox' = [inbox EXCEPT![i] = (@ \ {m}), ![succ(i)] = (@ \cup {m})]
/\ Fluent6_1' = [Fluent6_1 EXCEPT ![m][i] = TRUE]
/\ UNCHANGED<<Fluent7_1>>

Next ==
\E i \in Node, m \in Id :
\/ Send(i,m)
\/ Delete(i,m)
\/ Propagate(i,m)

Spec == (Init /\ [][Next]_inbox)
=============================================================================
