--------------------------- MODULE T1_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS Acceptor, Value, Ballot

VARIABLES maxVal, Fluent7_2, msgs1b, Fluent6_2, msgs1a, maxBal, Fluent13_14, maxVBal, Fluent14_14, Fluent15_14

vars == <<maxVal, Fluent7_2, msgs1b, Fluent6_2, msgs1a, maxBal, Fluent13_14, maxVBal, Fluent14_14, Fluent15_14>>

CandSep ==
/\ \A var0 \in Ballot : \A var1 \in Ballot : (Fluent6_2[var1]) => ((Fluent7_2[var0]) => (var0 <= var1))
/\ \A var0 \in Value : \E var1 \in Acceptor : (Fluent15_14[var0]) => ((Fluent13_14[var1]) => (Fluent14_14[var0]))

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
/\ Fluent13_14 = [ x0 \in Acceptor |-> FALSE]
/\ Fluent7_2 = [ x0 \in Ballot |-> FALSE]
/\ Fluent6_2 = [ x0 \in Ballot |-> FALSE]
/\ Fluent14_14 = [ x0 \in Value |-> FALSE]
/\ Fluent15_14 = [ x0 \in Value |-> FALSE]

Phase1a(b) ==
/\ msgs1a' = (msgs1a \cup {b})
/\ UNCHANGED <<maxBal,maxVBal,maxVal,msgs1b>>
/\ UNCHANGED<<Fluent13_14, Fluent7_2, Fluent6_2, Fluent14_14, Fluent15_14>>

Phase1b(a,b) ==
/\ (b \in msgs1a)
/\ b > maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ msgs1b' = (msgs1b \cup {<<a,b,maxVBal[a],maxVal[a]>>})
/\ UNCHANGED <<maxVBal,maxVal,msgs1a>>
/\ UNCHANGED<<Fluent13_14, Fluent7_2, Fluent6_2, Fluent14_14, Fluent15_14>>

Phase2a(b,v,a) ==
/\ (<<a,b,maxVBal[a],maxVal[a]>> \in msgs1b)
/\ (\E Q \in Quorum : LET Q1b == { m \in msgs1b : ((m[1] \in Q) /\ m[2] = b) }
    Q1bv == { m \in Q1b : m[3] >= 0 } IN
  /\ (\A aa \in Q : (\E m \in Q1b : m[1] = aa))
  /\ (Q1bv = {} \/ (\E m \in Q1bv : (m[4] = v /\ (\A mm \in Q1bv : m[3] >= mm[3])))))
/\ UNCHANGED <<maxBal,maxVBal,maxVal,msgs1a,msgs1b>>
/\ Fluent7_2' = [Fluent7_2 EXCEPT ![b] = TRUE]
/\ Fluent6_2' = [x0 \in Ballot |-> FALSE]
/\ Fluent15_14' = [Fluent15_14 EXCEPT ![v] = TRUE]
/\ UNCHANGED<<Fluent13_14, Fluent14_14>>

Phase2b(a,b,v) ==
/\ b >= maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ maxVBal' = [maxVBal EXCEPT![a] = b]
/\ maxVal' = [maxVal EXCEPT![a] = v]
/\ UNCHANGED <<msgs1a,msgs1b>>
/\ Fluent13_14' = [Fluent13_14 EXCEPT ![a] = TRUE]
/\ Fluent6_2' = [Fluent6_2 EXCEPT ![b] = TRUE]
/\ Fluent14_14' = [Fluent14_14 EXCEPT ![v] = TRUE]
/\ Fluent15_14' = [x0 \in Value |-> FALSE]
/\ UNCHANGED<<Fluent7_2>>

Next ==
\/ (\E b \in Ballot : Phase1a(b))
\/ (\E a \in Acceptor : (\E b \in Ballot : Phase1b(a,b)))
\/ (\E b \in Ballot : (\E v \in Value : (\E a \in Acceptor : Phase2a(b,v,a))))
\/ (\E a \in Acceptor : (\E b \in Ballot : (\E v \in Value : Phase2b(a,b,v))))

Spec == (Init /\ [][Next]_vars)
=============================================================================
