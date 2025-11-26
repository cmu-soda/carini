--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS a1, a2, a3, Acceptor, NUM2, Value, v1, v2, Ballot, NUM0, NUM1

VARIABLES maxVal, msgs1b, msgs1a, maxBal, Fluent6_7, Fluent5_7, maxVBal, cexTraceIdx

vars == <<maxVal, msgs1b, msgs1a, maxBal, Fluent6_7, Fluent5_7, maxVBal, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ Fluent6_7 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ msgs1a = {}
  /\ msgs1b = {}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ maxBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ Fluent5_7 = (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE)

/\ cexTraceIdx = 1 =>
  /\ Fluent6_7 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ msgs1a = {0}
  /\ msgs1b = {}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ maxBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ Fluent5_7 = (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE)

/\ cexTraceIdx = 2 =>
  /\ Fluent6_7 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ msgs1a = {0, 1}
  /\ msgs1b = {}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ maxBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ Fluent5_7 = (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE)

/\ cexTraceIdx = 3 =>
  /\ Fluent6_7 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ msgs1a = {0, 1}
  /\ msgs1b = {<<a1, 0, -1, "None">>}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ maxBal = (a1 :> 0 @@ a2 :> -1 @@ a3 :> -1)
  /\ Fluent5_7 = (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE)

/\ cexTraceIdx = 4 =>
  /\ Fluent6_7 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ msgs1a = {0, 1}
  /\ msgs1b = {<<a1, 0, -1, "None">>, <<a1, 1, -1, "None">>}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ maxBal = (a1 :> 1 @@ a2 :> -1 @@ a3 :> -1)
  /\ Fluent5_7 = (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE)

/\ cexTraceIdx = 5 =>
  /\ Fluent6_7 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ msgs1a = {0, 1}
  /\ msgs1b = {<<a1, 0, -1, "None">>, <<a1, 1, -1, "None">>, <<a2, 0, -1, "None">>}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ maxBal = (a1 :> 1 @@ a2 :> 0 @@ a3 :> -1)
  /\ Fluent5_7 = (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE)

/\ cexTraceIdx = 6 =>
  /\ Fluent6_7 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ msgs1a = {0, 1}
  /\ msgs1b = { <<a1, 0, -1, "None">>,
    <<a1, 1, -1, "None">>,
    <<a2, 0, -1, "None">>,
    <<a2, 1, -1, "None">> }
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ maxBal = (a1 :> 1 @@ a2 :> 1 @@ a3 :> -1)
  /\ Fluent5_7 = (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE)

/\ cexTraceIdx = 7 =>
  /\ Fluent6_7 = ( a1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ msgs1a = {0, 1}
  /\ msgs1b = { <<a1, 0, -1, "None">>,
    <<a1, 1, -1, "None">>,
    <<a2, 0, -1, "None">>,
    <<a2, 1, -1, "None">> }
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ maxBal = (a1 :> 1 @@ a2 :> 1 @@ a3 :> -1)
  /\ Fluent5_7 = (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE)

/\ cexTraceIdx = 8 =>
  /\ Fluent6_7 = ( a1 :> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ msgs1a = {0, 1}
  /\ msgs1b = { <<a1, 0, -1, "None">>,
    <<a1, 1, -1, "None">>,
    <<a2, 0, -1, "None">>,
    <<a2, 1, -1, "None">> }
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ maxBal = (a1 :> 1 @@ a2 :> 1 @@ a3 :> -1)
  /\ Fluent5_7 = (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE)

/\ cexTraceIdx = 9 =>
  /\ Fluent6_7 = ( a1 :> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ msgs1a = {0, 1}
  /\ msgs1b = { <<a1, 0, -1, "None">>,
    <<a1, 1, -1, "None">>,
    <<a2, 0, -1, "None">>,
    <<a2, 1, -1, "None">> }
  /\ maxVBal = (a1 :> 1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> v1 @@ a2 :> "None" @@ a3 :> "None")
  /\ maxBal = (a1 :> 1 @@ a2 :> 1 @@ a3 :> -1)
  /\ Fluent5_7 = (a1 :> TRUE @@ a2 :> FALSE @@ a3 :> FALSE)


CandSep == (\A var0 \in Acceptor : (\E var1 \in Ballot : (Fluent5_7[var0] => ~(Fluent6_7[var0][var1]))))

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
/\ Fluent6_7 = [x0 \in Acceptor |-> [x1 \in Ballot |-> FALSE]]
/\ Fluent5_7 = [x0 \in Acceptor |-> FALSE]
/\ cexTraceIdx = 0
/\ TraceConstraint

Phase1a(b) ==
/\ msgs1a' = (msgs1a \cup {b})
/\ UNCHANGED <<maxBal,maxVBal,maxVal,msgs1b>>
/\ UNCHANGED <<Fluent6_7,Fluent5_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Phase1b(a,b) ==
/\ (b \in msgs1a)
/\ b > maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ msgs1b' = (msgs1b \cup {<<a,b,maxVBal[a],maxVal[a]>>})
/\ UNCHANGED <<maxVBal,maxVal,msgs1a>>
/\ UNCHANGED <<Fluent6_7,Fluent5_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Phase2a(b,v,a) ==
/\ (<<a,b,maxVBal[a],maxVal[a]>> \in msgs1b)
/\ (\E Q \in Quorum : LET Q1b == { m \in msgs1b : ((m[1] \in Q) /\ m[2] = b) }
    Q1bv == { m \in Q1b : m[3] >= 0 } IN
  /\ (\A aa \in Q : (\E m \in Q1b : m[1] = aa))
  /\ (Q1bv = {} \/ (\E m \in Q1bv : (m[4] = v /\ (\A mm \in Q1bv : m[3] >= mm[3])))))
/\ UNCHANGED <<maxBal,maxVBal,maxVal,msgs1a,msgs1b>>
/\ Fluent6_7' = [[Fluent6_7 EXCEPT![a] = [x0 \in Ballot |-> TRUE]] EXCEPT![a][b] = Fluent6_7[a][b]]
/\ UNCHANGED <<Fluent5_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Phase2b(a,b,v) ==
/\ b >= maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ maxVBal' = [maxVBal EXCEPT![a] = b]
/\ maxVal' = [maxVal EXCEPT![a] = v]
/\ UNCHANGED <<msgs1a,msgs1b>>
/\ Fluent5_7' = [Fluent5_7 EXCEPT![a] = TRUE]
/\ UNCHANGED <<Fluent6_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\/ (\E b \in Ballot : Phase1a(b))
\/ (\E a \in Acceptor : (\E b \in Ballot : Phase1b(a,b)))
\/ (\E b \in Ballot : (\E v \in Value : (\E a \in Acceptor : Phase2a(b,v,a))))
\/ (\E a \in Acceptor : (\E b \in Ballot : (\E v \in Value : Phase2b(a,b,v))))

Spec == (Init /\ [][Next]_vars)
=============================================================================
