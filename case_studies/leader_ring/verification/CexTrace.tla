--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NUM8, Node, NUM2, NUM3, NUM5, Id, NUM0, NUM1

VARIABLES Fluent7_1, Fluent6_1, inbox, cexTraceIdx

vars == <<Fluent7_1, Fluent6_1, inbox, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ Fluent7_1 = (3 :> FALSE @@ 5 :> FALSE @@ 8 :> FALSE)
  /\ inbox = (0 :> {} @@ 1 :> {} @@ 2 :> {})
  /\ Fluent6_1 = ( 3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    5 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    8 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )

/\ cexTraceIdx = 1 =>
  /\ Fluent7_1 = (3 :> TRUE @@ 5 :> FALSE @@ 8 :> FALSE)
  /\ inbox = (0 :> {} @@ 1 :> {3} @@ 2 :> {})
  /\ Fluent6_1 = ( 3 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    5 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    8 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )

/\ cexTraceIdx = 2 =>
  /\ Fluent7_1 = (3 :> TRUE @@ 5 :> FALSE @@ 8 :> FALSE)
  /\ inbox = (0 :> {} @@ 1 :> {3} @@ 2 :> {3})
  /\ Fluent6_1 = ( 3 :> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    5 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    8 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )

/\ cexTraceIdx = 3 =>
  /\ Fluent7_1 = (3 :> TRUE @@ 5 :> FALSE @@ 8 :> FALSE)
  /\ inbox = (0 :> {} @@ 1 :> {} @@ 2 :> {3})
  /\ Fluent6_1 = ( 3 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    5 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    8 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )

/\ cexTraceIdx = 4 =>
  /\ Fluent7_1 = (3 :> TRUE @@ 5 :> FALSE @@ 8 :> FALSE)
  /\ inbox = (0 :> {3} @@ 1 :> {} @@ 2 :> {3})
  /\ Fluent6_1 = ( 3 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> TRUE) @@
    5 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    8 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )

/\ cexTraceIdx = 5 =>
  /\ Fluent7_1 = (3 :> TRUE @@ 5 :> FALSE @@ 8 :> FALSE)
  /\ inbox = (0 :> {} @@ 1 :> {} @@ 2 :> {3})
  /\ Fluent6_1 = ( 3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE) @@
    5 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    8 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )

/\ cexTraceIdx = 6 =>
  /\ Fluent7_1 = (3 :> TRUE @@ 5 :> FALSE @@ 8 :> FALSE)
  /\ inbox = (0 :> {} @@ 1 :> {} @@ 2 :> {})
  /\ Fluent6_1 = ( 3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    5 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    8 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )


CandSep == (\A var0 \in Id : (\E var1 \in Node : (Fluent7_1[var0] => Fluent6_1[var0][var1])))

N == Cardinality(Node)

id == @@(@@(:>(0,5),:>(1,3)),:>(2,8))

succ(n) == %((n + 1),N)

TypeOK ==
/\ (inbox \in [Node -> SUBSET(Id)])

Init ==
/\ inbox = [i \in Node |-> {}]
/\ Fluent7_1 = [x0 \in Id |-> FALSE]
/\ Fluent6_1 = [x0 \in Id |-> [x1 \in Node |-> FALSE]]
/\ cexTraceIdx = 0
/\ TraceConstraint

Send(i,m) ==
/\ inbox' = [inbox EXCEPT![succ(i)] = (@ \cup {m})]
/\ Fluent7_1' = [Fluent7_1 EXCEPT![m] = TRUE]
/\ Fluent6_1' = [Fluent6_1 EXCEPT![m][i] = TRUE]
/\ UNCHANGED <<>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Delete(i,m) ==
/\ (m \in inbox[i])
/\ inbox' = [inbox EXCEPT![i] = (@ \ {m})]
/\ Fluent6_1' = [Fluent6_1 EXCEPT![m][i] = FALSE]
/\ UNCHANGED <<Fluent7_1>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Propagate(i,m) ==
/\ (m \in inbox[i])
/\ inbox' = [inbox EXCEPT![i] = (@ \ {m}), ![succ(i)] = (@ \cup {m})]
/\ Fluent6_1' = [Fluent6_1 EXCEPT![m][i] = TRUE]
/\ UNCHANGED <<Fluent7_1>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\E i \in Node, m \in Id :
\/ Send(i,m)
\/ Delete(i,m)
\/ Propagate(i,m)

Spec == (Init /\ [][Next]_inbox)
=============================================================================
