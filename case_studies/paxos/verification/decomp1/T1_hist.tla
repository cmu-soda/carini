--------------------------- MODULE T1_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS Acceptor, Value, Ballot

VARIABLES maxVal, msgs1b, msgs1a, maxBal, Fluent6_7, Fluent5_7, maxVBal

vars == <<maxVal, msgs1b, msgs1a, maxBal, Fluent6_7, Fluent5_7, maxVBal>>

CandSep ==
\A var0 \in Acceptor : \E var1 \in Ballot : (Fluent5_7[var0]) => (~(Fluent6_7[var0][var1]))

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
/\ Fluent6_7 = [ x0 \in Acceptor |-> [ x1 \in Ballot |-> FALSE]]
/\ Fluent5_7 = [ x0 \in Acceptor |-> FALSE]

Phase1a(b) ==
/\ msgs1a' = (msgs1a \cup {b})
/\ UNCHANGED <<maxBal,maxVBal,maxVal,msgs1b>>
/\ UNCHANGED<<Fluent6_7, Fluent5_7>>

Phase1b(a,b) ==
/\ (b \in msgs1a)
/\ b > maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ msgs1b' = (msgs1b \cup {<<a,b,maxVBal[a],maxVal[a]>>})
/\ UNCHANGED <<maxVBal,maxVal,msgs1a>>
/\ UNCHANGED<<Fluent6_7, Fluent5_7>>

Phase2a(b,v,a) ==
/\ (<<a,b,maxVBal[a],maxVal[a]>> \in msgs1b)
/\ (\E Q \in Quorum : LET Q1b == { m \in msgs1b : ((m[1] \in Q) /\ m[2] = b) }
    Q1bv == { m \in Q1b : m[3] >= 0 } IN
  /\ (\A aa \in Q : (\E m \in Q1b : m[1] = aa))
  /\ (Q1bv = {} \/ (\E m \in Q1bv : (m[4] = v /\ (\A mm \in Q1bv : m[3] >= mm[3])))))
/\ UNCHANGED <<maxBal,maxVBal,maxVal,msgs1a,msgs1b>>
/\ Fluent6_7' = [[Fluent6_7 EXCEPT ![a] = [x0 \in Ballot |-> TRUE]] EXCEPT ![a][b] = Fluent6_7[a][b]]
/\ UNCHANGED<<Fluent5_7>>

Phase2b(a,b,v) ==
/\ b >= maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ maxVBal' = [maxVBal EXCEPT![a] = b]
/\ maxVal' = [maxVal EXCEPT![a] = v]
/\ UNCHANGED <<msgs1a,msgs1b>>
/\ Fluent5_7' = [Fluent5_7 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent6_7>>

Next ==
\/ (\E b \in Ballot : Phase1a(b))
\/ (\E a \in Acceptor : (\E b \in Ballot : Phase1b(a,b)))
\/ (\E b \in Ballot : (\E v \in Value : (\E a \in Acceptor : Phase2a(b,v,a))))
\/ (\E a \in Acceptor : (\E b \in Ballot : (\E v \in Value : Phase2b(a,b,v))))

Spec == (Init /\ [][Next]_vars)
=============================================================================
