--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS a1, a2, a3, Acceptor, NUM2, Value, v1, v2, Ballot, NUM0, NUM1

VARIABLES msgs2a, msgs1a, maxBal, Fluent23_12, Fluent22_12, cexTraceIdx

vars == <<msgs2a, msgs1a, maxBal, Fluent23_12, Fluent22_12, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ msgs1a = {}
  /\ Fluent23_12 = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )
  /\ Fluent22_12 = ( 0 :>
        ( v1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
          v2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) ) @@
    1 :>
        ( v1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
          v2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) ) @@
    2 :>
        ( v1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
          v2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) ) )
  /\ msgs2a = {}
  /\ maxBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 1 =>
  /\ msgs1a = {0}
  /\ Fluent23_12 = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )
  /\ Fluent22_12 = ( 0 :>
        ( v1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
          v2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) ) @@
    1 :>
        ( v1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
          v2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) ) @@
    2 :>
        ( v1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
          v2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) ) )
  /\ msgs2a = {}
  /\ maxBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 2 =>
  /\ msgs1a = {0, 1}
  /\ Fluent23_12 = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )
  /\ Fluent22_12 = ( 0 :>
        ( v1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
          v2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) ) @@
    1 :>
        ( v1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
          v2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) ) @@
    2 :>
        ( v1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
          v2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) ) )
  /\ msgs2a = {}
  /\ maxBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 3 =>
  /\ msgs1a = {0, 1}
  /\ Fluent23_12 = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )
  /\ Fluent22_12 = ( 0 :>
        ( v1 :> (a1 :> TRUE @@ a2 :> TRUE @@ a3 :> TRUE) @@
          v2 :> (a1 :> TRUE @@ a2 :> TRUE @@ a3 :> TRUE) ) @@
    1 :>
        ( v1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
          v2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) ) @@
    2 :>
        ( v1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
          v2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) ) )
  /\ msgs2a = {}
  /\ maxBal = (a1 :> 0 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 4 =>
  /\ msgs1a = {0, 1}
  /\ Fluent23_12 = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )
  /\ Fluent22_12 = ( 0 :>
        ( v1 :> (a1 :> TRUE @@ a2 :> TRUE @@ a3 :> TRUE) @@
          v2 :> (a1 :> TRUE @@ a2 :> TRUE @@ a3 :> TRUE) ) @@
    1 :>
        ( v1 :> (a1 :> TRUE @@ a2 :> TRUE @@ a3 :> TRUE) @@
          v2 :> (a1 :> TRUE @@ a2 :> TRUE @@ a3 :> TRUE) ) @@
    2 :>
        ( v1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
          v2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) ) )
  /\ msgs2a = {}
  /\ maxBal = (a1 :> 1 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 5 =>
  /\ msgs1a = {0, 1}
  /\ Fluent23_12 = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )
  /\ Fluent22_12 = ( 0 :>
        ( v1 :> (a1 :> TRUE @@ a2 :> FALSE @@ a3 :> TRUE) @@
          v2 :> (a1 :> TRUE @@ a2 :> TRUE @@ a3 :> TRUE) ) @@
    1 :>
        ( v1 :> (a1 :> TRUE @@ a2 :> TRUE @@ a3 :> TRUE) @@
          v2 :> (a1 :> TRUE @@ a2 :> TRUE @@ a3 :> TRUE) ) @@
    2 :>
        ( v1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
          v2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) ) )
  /\ msgs2a = {<<0, v1>>}
  /\ maxBal = (a1 :> 1 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 6 =>
  /\ msgs1a = {0, 1}
  /\ Fluent23_12 = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )
  /\ Fluent22_12 = ( 0 :>
        ( v1 :> (a1 :> TRUE @@ a2 :> FALSE @@ a3 :> TRUE) @@
          v2 :> (a1 :> TRUE @@ a2 :> TRUE @@ a3 :> TRUE) ) @@
    1 :>
        ( v1 :> (a1 :> TRUE @@ a2 :> TRUE @@ a3 :> TRUE) @@
          v2 :> (a1 :> FALSE @@ a2 :> TRUE @@ a3 :> TRUE) ) @@
    2 :>
        ( v1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
          v2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) ) )
  /\ msgs2a = {<<0, v1>>, <<1, v2>>}
  /\ maxBal = (a1 :> 1 @@ a2 :> -1 @@ a3 :> -1)

/\ cexTraceIdx = 7 =>
  /\ msgs1a = {0, 1}
  /\ Fluent23_12 = ( 0 :> (v1 :> TRUE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )
  /\ Fluent22_12 = ( 0 :>
        ( v1 :> (a1 :> TRUE @@ a2 :> TRUE @@ a3 :> TRUE) @@
          v2 :> (a1 :> TRUE @@ a2 :> TRUE @@ a3 :> TRUE) ) @@
    1 :>
        ( v1 :> (a1 :> TRUE @@ a2 :> TRUE @@ a3 :> TRUE) @@
          v2 :> (a1 :> FALSE @@ a2 :> TRUE @@ a3 :> TRUE) ) @@
    2 :>
        ( v1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
          v2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) ) )
  /\ msgs2a = {<<0, v1>>, <<1, v2>>}
  /\ maxBal = (a1 :> 1 @@ a2 :> 0 @@ a3 :> -1)

/\ cexTraceIdx = 8 =>
  /\ msgs1a = {0, 1}
  /\ Fluent23_12 = ( 0 :> (v1 :> TRUE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> TRUE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )
  /\ Fluent22_12 = ( 0 :>
        ( v1 :> (a1 :> TRUE @@ a2 :> TRUE @@ a3 :> TRUE) @@
          v2 :> (a1 :> TRUE @@ a2 :> TRUE @@ a3 :> TRUE) ) @@
    1 :>
        ( v1 :> (a1 :> TRUE @@ a2 :> TRUE @@ a3 :> TRUE) @@
          v2 :> (a1 :> TRUE @@ a2 :> TRUE @@ a3 :> TRUE) ) @@
    2 :>
        ( v1 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) @@
          v2 :> (a1 :> FALSE @@ a2 :> FALSE @@ a3 :> FALSE) ) )
  /\ msgs2a = {<<0, v1>>, <<1, v2>>}
  /\ maxBal = (a1 :> 1 @@ a2 :> 0 @@ a3 :> -1)


CandSep ==
\E var0 \in Value :
\A var1 \in Ballot :
\E var2 \in Acceptor :
(Fluent23_12[var1][var0] => ~(Fluent22_12[var1][var0][var2]))

Quorum == { i \in SUBSET(Acceptor) : (Cardinality(i) * 2) > Cardinality(Acceptor) }

None == "None"

TypeOK ==
/\ (maxBal \in [Acceptor -> (Ballot \cup {-.(1)})])
/\ (msgs1a \in SUBSET(Ballot))
/\ (msgs2a \in SUBSET((Ballot \X Value)))

Init ==
/\ maxBal = [a \in Acceptor |-> -.(1)]
/\ msgs1a = {}
/\ msgs2a = {}
/\ Fluent23_12 = [x0 \in Ballot |-> [x1 \in Value |-> FALSE]]
/\ Fluent22_12 = [x0 \in Ballot |-> [x1 \in Value |-> [x2 \in Acceptor |-> FALSE]]]
/\ cexTraceIdx = 0
/\ TraceConstraint

Phase1a(b) ==
/\ msgs1a' = (msgs1a \cup {b})
/\ UNCHANGED <<maxBal,msgs2a>>
/\ UNCHANGED <<Fluent23_12,Fluent22_12>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Phase1b(a,b) ==
/\ (b \in msgs1a)
/\ b > maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ UNCHANGED <<msgs1a,msgs2a>>
/\ Fluent22_12' = [Fluent22_12 EXCEPT![b] = [x0 \in Value |-> [x1 \in Acceptor |-> TRUE]]]
/\ UNCHANGED <<Fluent23_12>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Phase2a(b,v,a) ==
/\ ~((\E m \in msgs2a : m[1] = b))
/\ msgs2a' = (msgs2a \cup {<<b,v>>})
/\ UNCHANGED <<maxBal,msgs1a>>
/\ Fluent22_12' = [Fluent22_12 EXCEPT![b][v][a] = FALSE]
/\ UNCHANGED <<Fluent23_12>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Phase2b(a,b,v) ==
/\ (<<b,v>> \in msgs2a)
/\ b >= maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ UNCHANGED <<msgs1a,msgs2a>>
/\ Fluent23_12' = [Fluent23_12 EXCEPT![b][v] = TRUE]
/\ Fluent22_12' = [Fluent22_12 EXCEPT![b][v][a] = TRUE]
/\ UNCHANGED <<>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\/ (\E b \in Ballot : Phase1a(b))
\/ (\E a \in Acceptor : (\E b \in Ballot : Phase1b(a,b)))
\/ (\E b \in Ballot : (\E v \in Value : (\E a \in Acceptor : Phase2a(b,v,a))))
\/ (\E a \in Acceptor : (\E b \in Ballot : (\E v \in Value : Phase2b(a,b,v))))

Spec == (Init /\ [][Next]_vars)
=============================================================================
