--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Acceptor, Quorum, NUM2, Ballot, NUM0, NUM1, a1, a2, a3, _a1a2_, _a1a2a3_, _a1a3_, _a2a3_, Value, v1, v2

VARIABLES maxVal, msgs1b, msgs1a, maxBal, Fluent6_29, maxVBal, Fluent4_29, Fluent5_29, cexTraceIdx

vars == <<maxVal, msgs1b, msgs1a, maxBal, Fluent6_29, maxVBal, Fluent4_29, Fluent5_29, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ msgs1a = {}
  /\ msgs1b = {}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ Fluent6_29 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent5_29 = ( 0 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) )
  /\ Fluent4_29 = ( 0 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) )
  /\ maxBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 1 =>
  /\ msgs1a = {1}
  /\ msgs1b = {}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ Fluent6_29 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent5_29 = ( 0 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) )
  /\ Fluent4_29 = ( 0 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) )
  /\ maxBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 2 =>
  /\ msgs1a = {1, 2}
  /\ msgs1b = {}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ Fluent6_29 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent5_29 = ( 0 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) )
  /\ Fluent4_29 = ( 0 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) )
  /\ maxBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 3 =>
  /\ msgs1a = {1, 2}
  /\ msgs1b = {<<a1, 1, -1, "None">>}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ Fluent6_29 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent5_29 = ( 0 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) )
  /\ Fluent4_29 = ( 0 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) )
  /\ maxBal = (a1 :> 1 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 4 =>
  /\ msgs1a = {1, 2}
  /\ msgs1b = {<<a1, 1, -1, "None">>, <<a1, 2, -1, "None">>}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ Fluent6_29 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent5_29 = ( 0 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) )
  /\ Fluent4_29 = ( 0 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) )
  /\ maxBal = (a1 :> 2 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 5 =>
  /\ msgs1a = {1, 2}
  /\ msgs1b = {<<a1, 1, -1, "None">>, <<a1, 2, -1, "None">>, <<a2, 1, -1, "None">>}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ Fluent6_29 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent5_29 = ( 0 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) )
  /\ Fluent4_29 = ( 0 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) )
  /\ maxBal = (a1 :> 2 @@ a2 :> 1 @@ a3 :> -1)

/\ cexTraceIdx = 6 =>
  /\ msgs1a = {1, 2}
  /\ msgs1b = { <<a1, 1, -1, "None">>,
    <<a1, 2, -1, "None">>,
    <<a2, 1, -1, "None">>,
    <<a2, 2, -1, "None">> }
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ Fluent6_29 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent5_29 = ( 0 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) )
  /\ Fluent4_29 = ( 0 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) )
  /\ maxBal = (a1 :> 2 @@ a2 :> 2 @@ a3 :> -1)

/\ cexTraceIdx = 7 =>
  /\ msgs1a = {1, 2}
  /\ msgs1b = { <<a1, 1, -1, "None">>,
    <<a1, 2, -1, "None">>,
    <<a2, 1, -1, "None">>,
    <<a2, 2, -1, "None">> }
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ Fluent6_29 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE)
  /\ Fluent5_29 = ( 0 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) )
  /\ Fluent4_29 = ( 0 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    2 :> (a1 :> TRUE @@ a2 :> FALSE @@ a3 :> FALSE) )
  /\ maxBal = (a1 :> 2 @@ a2 :> 2 @@ a3 :> -1)

/\ cexTraceIdx = 8 =>
  /\ msgs1a = {1, 2}
  /\ msgs1b = { <<a1, 1, -1, "None">>,
    <<a1, 2, -1, "None">>,
    <<a2, 1, -1, "None">>,
    <<a2, 2, -1, "None">> }
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ Fluent6_29 = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ Fluent5_29 = ( 0 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) )
  /\ Fluent4_29 = ( 0 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    1 :> (a1 :> TRUE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    2 :> (a1 :> TRUE @@ a2 :> FALSE @@ a3 :> FALSE) )
  /\ maxBal = (a1 :> 2 @@ a2 :> 2 @@ a3 :> -1)

/\ cexTraceIdx = 9 =>
  /\ msgs1a = {1, 2}
  /\ msgs1b = { <<a1, 1, -1, "None">>,
    <<a1, 2, -1, "None">>,
    <<a2, 1, -1, "None">>,
    <<a2, 2, -1, "None">> }
  /\ maxVBal = (a1 :> 2 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> v1 @@ a2 :> "None" @@ a3 :> "None")
  /\ Fluent6_29 = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ Fluent5_29 = ( 0 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    2 :> (a1 :> TRUE @@ a2 :> FALSE @@ a3 :> FALSE) )
  /\ Fluent4_29 = ( 0 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    1 :> (a1 :> TRUE @@ a2 :> FALSE @@ a3 :> FALSE) @@
    2 :> (a1 :> TRUE @@ a2 :> FALSE @@ a3 :> FALSE) )
  /\ maxBal = (a1 :> 2 @@ a2 :> 2 @@ a3 :> -1)


CandSep == (\A var0 \in Acceptor : (\A var1 \in Ballot : (Fluent5_29[var1][var0] => (Fluent4_29[var1][var0] => Fluent6_29[var1]))))

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
/\ Fluent6_29 = [x0 \in Ballot |-> FALSE]
/\ Fluent4_29 = [x0 \in Ballot |-> [x1 \in Acceptor |-> FALSE]]
/\ Fluent5_29 = [x0 \in Ballot |-> [x1 \in Acceptor |-> FALSE]]
/\ cexTraceIdx = 0
/\ TraceConstraint

Phase1a(b) ==
/\ msgs1a' = (msgs1a \cup {b})
/\ UNCHANGED <<maxBal,maxVBal,maxVal,msgs1b>>
/\ UNCHANGED <<Fluent6_29,Fluent4_29,Fluent5_29>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Phase1b(a,b) ==
/\ (b \in msgs1a)
/\ b > maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ msgs1b' = (msgs1b \cup {<<a,b,maxVBal[a],maxVal[a]>>})
/\ UNCHANGED <<maxVBal,maxVal,msgs1a>>
/\ UNCHANGED <<Fluent6_29,Fluent4_29,Fluent5_29>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Phase2a(b,v,a,Q) ==
/\ (<<a,b,maxVBal[a],maxVal[a]>> \in msgs1b)
/\ LET Q1b == { m \in msgs1b : ((m[1] \in Q) /\ m[2] = b) }
    Q1bv == { m \in Q1b : m[3] >= 0 } IN
  /\ (\A aa \in Q : (\E m \in Q1b : m[1] = aa))
  /\ (Q1bv = {} \/ (\E m \in Q1bv : (m[4] = v /\ (\A mm \in Q1bv : m[3] >= mm[3]))))
/\ UNCHANGED <<maxBal,maxVBal,maxVal,msgs1a,msgs1b>>
/\ Fluent6_29' = [[x0 \in Ballot |-> FALSE] EXCEPT![b] = TRUE]
/\ Fluent4_29' = [Fluent4_29 EXCEPT![b][a] = TRUE]
/\ UNCHANGED <<Fluent5_29>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Phase2b(a,b,v) ==
/\ b >= maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ maxVBal' = [maxVBal EXCEPT![a] = b]
/\ maxVal' = [maxVal EXCEPT![a] = v]
/\ UNCHANGED <<msgs1a,msgs1b>>
/\ Fluent5_29' = [Fluent5_29 EXCEPT![b][a] = TRUE]
/\ UNCHANGED <<Fluent6_29,Fluent4_29>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\/ (\E b \in Ballot : Phase1a(b))
\/ (\E a \in Acceptor : (\E b \in Ballot : Phase1b(a,b)))
\/ (\E b \in Ballot : (\E v \in Value : (\E a \in Acceptor : (\E Q \in Quorum : Phase2a(b,v,a,Q)))))
\/ (\E a \in Acceptor : (\E b \in Ballot : (\E v \in Value : Phase2b(a,b,v))))

Spec == (Init /\ [][Next]_vars)
=============================================================================
