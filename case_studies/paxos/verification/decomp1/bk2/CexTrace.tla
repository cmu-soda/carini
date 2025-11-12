--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS a1, a2, a3, Acceptor, NUM2, Value, v1, v2, Ballot, NUM0, NUM1

VARIABLES maxVal, msgs1b, msgs1a, maxBal, maxVBal, Fluent44_1, cexTraceIdx, Fluent43_1

vars == <<maxVal, msgs1b, msgs1a, maxBal, maxVBal, Fluent44_1, cexTraceIdx, Fluent43_1>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ msgs1a = {}
  /\ msgs1b = {}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ Fluent43_1 = ( v1 :>
        ( v1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          v2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    v2 :>
        ( v1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          v2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ Fluent44_1 = ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    a2 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    a3 :> (v1 :> FALSE @@ v2 :> FALSE) )
  /\ maxBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 1 =>
  /\ msgs1a = {1}
  /\ msgs1b = {}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ Fluent43_1 = ( v1 :>
        ( v1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          v2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    v2 :>
        ( v1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          v2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ Fluent44_1 = ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    a2 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    a3 :> (v1 :> FALSE @@ v2 :> FALSE) )
  /\ maxBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 2 =>
  /\ msgs1a = {0, 1}
  /\ msgs1b = {}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ Fluent43_1 = ( v1 :>
        ( v1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          v2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    v2 :>
        ( v1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          v2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ Fluent44_1 = ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    a2 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    a3 :> (v1 :> FALSE @@ v2 :> FALSE) )
  /\ maxBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 3 =>
  /\ msgs1a = {0, 1}
  /\ msgs1b = {<<a1, 0, -1, "None">>}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ Fluent43_1 = ( v1 :>
        ( v1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          v2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    v2 :>
        ( v1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          v2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ Fluent44_1 = ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    a2 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    a3 :> (v1 :> FALSE @@ v2 :> FALSE) )
  /\ maxBal = (a1 :> 0 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 4 =>
  /\ msgs1a = {0, 1}
  /\ msgs1b = {<<a1, 0, -1, "None">>, <<a2, 0, -1, "None">>}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ Fluent43_1 = ( v1 :>
        ( v1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          v2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    v2 :>
        ( v1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          v2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ Fluent44_1 = ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    a2 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    a3 :> (v1 :> FALSE @@ v2 :> FALSE) )
  /\ maxBal = (a1 :> 0 @@ a2 :> 0 @@ a3 :> -1)

/\ cexTraceIdx = 5 =>
  /\ msgs1a = {0, 1}
  /\ msgs1b = {<<a1, 0, -1, "None">>, <<a2, 0, -1, "None">>}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ Fluent43_1 = ( v1 :>
        (v1 :> (v1 :> TRUE @@ v2 :> TRUE) @@ v2 :> (v1 :> TRUE @@ v2 :> TRUE)) @@
    v2 :>
        ( v1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          v2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ Fluent44_1 = ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    a2 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    a3 :> (v1 :> FALSE @@ v2 :> FALSE) )
  /\ maxBal = (a1 :> 0 @@ a2 :> 0 @@ a3 :> -1)

/\ cexTraceIdx = 6 =>
  /\ msgs1a = {0, 1}
  /\ msgs1b = {<<a1, 0, -1, "None">>, <<a2, 0, -1, "None">>}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ Fluent43_1 = ( v1 :>
        (v1 :> (v1 :> TRUE @@ v2 :> TRUE) @@ v2 :> (v1 :> TRUE @@ v2 :> TRUE)) @@
    v2 :> (v1 :> (v1 :> TRUE @@ v2 :> TRUE) @@ v2 :> (v1 :> TRUE @@ v2 :> TRUE)) )
  /\ Fluent44_1 = ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    a2 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    a3 :> (v1 :> FALSE @@ v2 :> FALSE) )
  /\ maxBal = (a1 :> 0 @@ a2 :> 0 @@ a3 :> -1)

/\ cexTraceIdx = 7 =>
  /\ msgs1a = {0, 1}
  /\ msgs1b = {<<a1, 0, -1, "None">>, <<a2, 0, -1, "None">>}
  /\ maxVBal = (a1 :> 1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> v2 @@ a2 :> "None" @@ a3 :> "None")
  /\ Fluent43_1 = ( v1 :>
        (v1 :> (v1 :> TRUE @@ v2 :> TRUE) @@ v2 :> (v1 :> TRUE @@ v2 :> TRUE)) @@
    v2 :> (v1 :> (v1 :> TRUE @@ v2 :> TRUE) @@ v2 :> (v1 :> TRUE @@ v2 :> TRUE)) )
  /\ Fluent44_1 = ( a1 :> (v1 :> FALSE @@ v2 :> TRUE) @@
    a2 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    a3 :> (v1 :> FALSE @@ v2 :> FALSE) )
  /\ maxBal = (a1 :> 1 @@ a2 :> 0 @@ a3 :> -1)

/\ cexTraceIdx = 8 =>
  /\ msgs1a = {0, 1}
  /\ msgs1b = {<<a1, 0, -1, "None">>, <<a2, 0, -1, "None">>}
  /\ maxVBal = (a1 :> 1 @@ a2 :> 0 @@ a3 :> -1)
  /\ maxVal = (a1 :> v2 @@ a2 :> v1 @@ a3 :> "None")
  /\ Fluent43_1 = ( v1 :>
        (v1 :> (v1 :> TRUE @@ v2 :> TRUE) @@ v2 :> (v1 :> TRUE @@ v2 :> TRUE)) @@
    v2 :> (v1 :> (v1 :> TRUE @@ v2 :> TRUE) @@ v2 :> (v1 :> TRUE @@ v2 :> TRUE)) )
  /\ Fluent44_1 = ( a1 :> (v1 :> FALSE @@ v2 :> TRUE) @@
    a2 :> (v1 :> TRUE @@ v2 :> FALSE) @@
    a3 :> (v1 :> FALSE @@ v2 :> FALSE) )
  /\ maxBal = (a1 :> 1 @@ a2 :> 0 @@ a3 :> -1)


CandSep == (\A var0 \in Value : (\E var1 \in Value : (\A var2 \in Acceptor : (Fluent44_1[var2][var1] => ~(Fluent43_1[var1][var1][var0])))))

Quorum == { i \in SUBSET(Acceptor) : (Cardinality(i) * 2) > Cardinality(Acceptor) }

None == "None"

TypeOK ==
/\ (maxBal \in [Acceptor -> (Ballot \cup {-.(1)})])
/\ (maxVBal \in [Acceptor -> (Ballot \cup {-.(1)})])
/\ (maxVal \in [Acceptor -> (Value \cup {None})])
/\ (msgs1a \in SUBSET(Ballot))
/\ (msgs1b \in SUBSET((Acceptor \X Ballot \X (Ballot \cup {-.(1)}) \X (Value \cup {None}))))

Init ==
/\ maxBal = [a \in Acceptor |-> -.(1)]
/\ maxVBal = [a \in Acceptor |-> -.(1)]
/\ maxVal = [a \in Acceptor |-> None]
/\ msgs1a = {}
/\ msgs1b = {}
/\ Fluent44_1 = [x0 \in Acceptor |-> [x1 \in Value |-> FALSE]]
/\ Fluent43_1 = [x0 \in Value |-> [x1 \in Value |-> [x2 \in Value |-> FALSE]]]
/\ cexTraceIdx = 0
/\ TraceConstraint

Phase1a(b) ==
/\ msgs1a' = (msgs1a \cup {b})
/\ UNCHANGED <<maxBal,maxVBal,maxVal,msgs1b>>
/\ UNCHANGED <<Fluent44_1,Fluent43_1>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Phase1b(a,b) ==
/\ (b \in msgs1a)
/\ b > maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ msgs1b' = (msgs1b \cup {<<a,b,maxVBal[a],maxVal[a]>>})
/\ UNCHANGED <<maxVBal,maxVal,msgs1a>>
/\ UNCHANGED <<Fluent44_1,Fluent43_1>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Phase2a(b,v,a) ==
/\ (<<a,b,maxVBal[a],maxVal[a]>> \in msgs1b)
/\ (\E Q \in Quorum : LET Q1b == { m \in msgs1b : ((m[1] \in Q) /\ m[2] = b) }
    Q1bv == { m \in Q1b : m[3] >= 0 } IN
  /\ (\A aa \in Q : (\E m \in Q1b : m[1] = aa))
  /\ (Q1bv = {} \/ (\E m \in Q1bv : (m[4] = v /\ (\A mm \in Q1bv : m[3] >= mm[3])))))
/\ UNCHANGED <<maxBal,maxVBal,maxVal,msgs1a,msgs1b>>
/\ Fluent43_1' = [Fluent43_1 EXCEPT![v] = [x0 \in Value |-> [x1 \in Value |-> TRUE]]]
/\ UNCHANGED <<Fluent44_1>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Phase2b(a,b,v) ==
/\ b >= maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ maxVBal' = [maxVBal EXCEPT![a] = b]
/\ maxVal' = [maxVal EXCEPT![a] = v]
/\ UNCHANGED <<msgs1a,msgs1b>>
/\ Fluent44_1' = [[Fluent44_1 EXCEPT![a] = [x0 \in Value |-> FALSE]] EXCEPT![a][v] = TRUE]
/\ UNCHANGED <<Fluent43_1>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\/ (\E b \in Ballot : Phase1a(b))
\/ (\E a \in Acceptor : (\E b \in Ballot : Phase1b(a,b)))
\/ (\E b \in Ballot : (\E v \in Value : (\E a \in Acceptor : Phase2a(b,v,a))))
\/ (\E a \in Acceptor : (\E b \in Ballot : (\E v \in Value : Phase2b(a,b,v))))

Spec == (Init /\ [][Next]_vars)
=============================================================================
