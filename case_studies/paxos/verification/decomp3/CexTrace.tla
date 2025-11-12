--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS a1, a2, a3, Acceptor, NUM2, Value, v1, v2, Ballot, NUM0, NUM1

VARIABLES msgs1a, maxBal, Fluent4_14, Fluent3_14, Fluent2_14, cexTraceIdx

vars == <<msgs1a, maxBal, Fluent4_14, Fluent3_14, Fluent2_14, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ msgs1a = {}
  /\ Fluent4_14 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent3_14 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent2_14 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ maxBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 1 =>
  /\ msgs1a = {0}
  /\ Fluent4_14 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent3_14 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent2_14 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ maxBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 2 =>
  /\ msgs1a = {0, 2}
  /\ Fluent4_14 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent3_14 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent2_14 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ maxBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 3 =>
  /\ msgs1a = {0, 2}
  /\ Fluent4_14 = ( a1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent3_14 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent2_14 = ( a1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ maxBal = (a1 :> 0 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 4 =>
  /\ msgs1a = {0, 2}
  /\ Fluent4_14 = ( a1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent3_14 = ( a1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent2_14 = ( a1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ maxBal = (a1 :> 0 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 5 =>
  /\ msgs1a = {0, 2}
  /\ Fluent4_14 = ( a1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> TRUE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent3_14 = ( a1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent2_14 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ maxBal = (a1 :> 2 @@ a2 :> -1 @@ a3 :> -1)


CandSep == (\A var0 \in Acceptor : (\A var1 \in Ballot : (Fluent4_14[var0][var1] => (Fluent3_14[var0][var1] => Fluent2_14[var0][var1]))))

Quorum == { i \in SUBSET(Acceptor) : (Cardinality(i) * 2) > Cardinality(Acceptor) }

None == "None"

TypeOK ==
/\ (maxBal \in [Acceptor -> (Ballot \cup {-.(1)})])
/\ (msgs1a \in SUBSET(Ballot))

Init ==
/\ maxBal = [a \in Acceptor |-> -.(1)]
/\ msgs1a = {}
/\ Fluent3_14 = [x0 \in Acceptor |-> [x1 \in Ballot |-> FALSE]]
/\ Fluent4_14 = [x0 \in Acceptor |-> [x1 \in Ballot |-> FALSE]]
/\ Fluent2_14 = [x0 \in Acceptor |-> [x1 \in Ballot |-> FALSE]]
/\ cexTraceIdx = 0
/\ TraceConstraint

Phase1a(b) ==
/\ msgs1a' = (msgs1a \cup {b})
/\ UNCHANGED <<maxBal>>
/\ UNCHANGED <<Fluent3_14,Fluent4_14,Fluent2_14>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Phase1b(a,b) ==
/\ (b \in msgs1a)
/\ b > maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ UNCHANGED <<msgs1a>>
/\ Fluent4_14' = [Fluent4_14 EXCEPT![a][b] = TRUE]
/\ Fluent2_14' = [[Fluent2_14 EXCEPT![a] = [x0 \in Ballot |-> FALSE]] EXCEPT![a][b] = TRUE]
/\ UNCHANGED <<Fluent3_14>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Phase2b(a,b,v) ==
/\ b >= maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ UNCHANGED <<msgs1a>>
/\ Fluent3_14' = [Fluent3_14 EXCEPT![a][b] = TRUE]
/\ UNCHANGED <<Fluent4_14,Fluent2_14>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\/ (\E b \in Ballot : Phase1a(b))
\/ (\E a \in Acceptor : (\E b \in Ballot : Phase1b(a,b)))
\/ (\E a \in Acceptor : (\E b \in Ballot : (\E v \in Value : Phase2b(a,b,v))))

Spec == (Init /\ [][Next]_vars)
=============================================================================
