--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS a1, a2, a3, Acceptor, NUM2, Value, v1, v2, Ballot, NUM0, NUM1

VARIABLES Fluent11_19, maxVal, msgs2a, Fluent12_19, msgs1b, msgs1a, maxVBal, cexTraceIdx

vars == <<Fluent11_19, maxVal, msgs2a, Fluent12_19, msgs1b, msgs1a, maxVBal, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ Fluent12_19 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent11_19 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ msgs1a = {}
  /\ msgs1b = {}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ msgs2a = {}

/\ cexTraceIdx = 1 =>
  /\ Fluent12_19 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent11_19 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ msgs1a = {0}
  /\ msgs1b = {}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ msgs2a = {}

/\ cexTraceIdx = 2 =>
  /\ Fluent12_19 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent11_19 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ msgs1a = {0, 1}
  /\ msgs1b = {}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ msgs2a = {}

/\ cexTraceIdx = 3 =>
  /\ Fluent12_19 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent11_19 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ msgs1a = {0, 1, 2}
  /\ msgs1b = {}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ msgs2a = {}

/\ cexTraceIdx = 4 =>
  /\ Fluent12_19 = ( a1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent11_19 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ msgs1a = {0, 1, 2}
  /\ msgs1b = {<<a1, 0, -1, "None">>}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ msgs2a = {}

/\ cexTraceIdx = 5 =>
  /\ Fluent12_19 = ( a1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent11_19 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ msgs1a = {0, 1, 2}
  /\ msgs1b = {<<a1, 0, -1, "None">>, <<a1, 1, -1, "None">>}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ msgs2a = {}

/\ cexTraceIdx = 6 =>
  /\ Fluent12_19 = ( a1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    a2 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent11_19 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ msgs1a = {0, 1, 2}
  /\ msgs1b = {<<a1, 0, -1, "None">>, <<a1, 1, -1, "None">>, <<a2, 0, -1, "None">>}
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ msgs2a = {}

/\ cexTraceIdx = 7 =>
  /\ Fluent12_19 = ( a1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent11_19 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ msgs1a = {0, 1, 2}
  /\ msgs1b = { <<a1, 0, -1, "None">>,
    <<a1, 1, -1, "None">>,
    <<a2, 0, -1, "None">>,
    <<a2, 1, -1, "None">> }
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ msgs2a = {}

/\ cexTraceIdx = 8 =>
  /\ Fluent12_19 = ( a1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent11_19 = ( a1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ msgs1a = {0, 1, 2}
  /\ msgs1b = { <<a1, 0, -1, "None">>,
    <<a1, 1, -1, "None">>,
    <<a2, 0, -1, "None">>,
    <<a2, 1, -1, "None">> }
  /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> "None" @@ a2 :> "None" @@ a3 :> "None")
  /\ msgs2a = {<<0, v1>>}

/\ cexTraceIdx = 9 =>
  /\ Fluent12_19 = ( a1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent11_19 = ( a1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    a3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ msgs1a = {0, 1, 2}
  /\ msgs1b = { <<a1, 0, -1, "None">>,
    <<a1, 1, -1, "None">>,
    <<a2, 0, -1, "None">>,
    <<a2, 1, -1, "None">> }
  /\ maxVBal = (a1 :> 0 @@ a2 :> -1 @@ a3 :> -1)
  /\ maxVal = (a1 :> v1 @@ a2 :> "None" @@ a3 :> "None")
  /\ msgs2a = {<<0, v1>>}


CandSep == (\A var0 \in Acceptor : (\E var1 \in Acceptor : (\A var2 \in Ballot : (Fluent11_19[var0][var2] => Fluent12_19[var1][var2]))))

Quorum == { i \in SUBSET(Acceptor) : (Cardinality(i) * 2) > Cardinality(Acceptor) }

None == "None"

TypeOK ==
/\ (maxVBal \in [Acceptor -> (Ballot \cup {-.(1)})])
/\ (maxVal \in [Acceptor -> (Value \cup {None})])
/\ (msgs1a \in SUBSET(Ballot))
/\ (msgs1b \in SUBSET((Acceptor \X Ballot \X (Ballot \cup {-.(1)}) \X (Value \cup {None}))))
/\ (msgs2a \in SUBSET((Ballot \X Value)))

Init ==
/\ maxVBal = [a \in Acceptor |-> -.(1)]
/\ maxVal = [a \in Acceptor |-> None]
/\ msgs1a = {}
/\ msgs1b = {}
/\ msgs2a = {}
/\ Fluent11_19 = [x0 \in Acceptor |-> [x1 \in Ballot |-> FALSE]]
/\ Fluent12_19 = [x0 \in Acceptor |-> [x1 \in Ballot |-> FALSE]]
/\ cexTraceIdx = 0
/\ TraceConstraint

Phase1a(b) ==
/\ msgs1a' = (msgs1a \cup {b})
/\ UNCHANGED <<maxVBal,maxVal,msgs1b,msgs2a>>
/\ UNCHANGED <<Fluent11_19,Fluent12_19>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Phase1b(a,b) ==
/\ (b \in msgs1a)
/\ msgs1b' = (msgs1b \cup {<<a,b,maxVBal[a],maxVal[a]>>})
/\ UNCHANGED <<maxVBal,maxVal,msgs1a,msgs2a>>
/\ Fluent12_19' = [[Fluent12_19 EXCEPT![a] = [x0 \in Ballot |-> FALSE]] EXCEPT![a][b] = TRUE]
/\ UNCHANGED <<Fluent11_19>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Phase2a(b,v,a) ==
/\ (<<a,b,maxVBal[a],maxVal[a]>> \in msgs1b)
/\ ~((\E m \in msgs2a : m[1] = b))
/\ (\E Q \in Quorum : LET Q1b == { m \in msgs1b : ((m[1] \in Q) /\ m[2] = b) }
    Q1bv == { m \in Q1b : m[3] >= 0 } IN
  /\ (\A aa \in Q : (\E m \in Q1b : m[1] = aa))
  /\ (Q1bv = {} \/ (\E m \in Q1bv : (m[4] = v /\ (\A mm \in Q1bv : m[3] >= mm[3])))))
/\ msgs2a' = (msgs2a \cup {<<b,v>>})
/\ UNCHANGED <<maxVBal,maxVal,msgs1a,msgs1b>>
/\ UNCHANGED <<Fluent11_19,Fluent12_19>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Phase2b(a,b,v) ==
/\ (<<b,v>> \in msgs2a)
/\ maxVBal' = [maxVBal EXCEPT![a] = b]
/\ maxVal' = [maxVal EXCEPT![a] = v]
/\ UNCHANGED <<msgs1a,msgs1b,msgs2a>>
/\ Fluent11_19' = [Fluent11_19 EXCEPT![a][b] = TRUE]
/\ UNCHANGED <<Fluent12_19>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\/ (\E b \in Ballot : Phase1a(b))
\/ (\E a \in Acceptor : (\E b \in Ballot : Phase1b(a,b)))
\/ (\E b \in Ballot : (\E v \in Value : (\E a \in Acceptor : Phase2a(b,v,a))))
\/ (\E a \in Acceptor : (\E b \in Ballot : (\E v \in Value : Phase2b(a,b,v))))

Spec == (Init /\ [][Next]_vars)
=============================================================================
