--------------------------- MODULE T1_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS Acceptor, Value, Ballot

VARIABLES Fluent21_18, maxVal, msgs2a, Fluent20_18, msgs1b, msgs1a, maxVBal, Fluent19_18

vars == <<Fluent21_18, maxVal, msgs2a, Fluent20_18, msgs1b, msgs1a, maxVBal, Fluent19_18>>

CandSep ==
\A var0 \in Acceptor : (Fluent21_18[var0]) => ((Fluent19_18[var0]) => (Fluent20_18[var0]))

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
/\ Fluent21_18 = [ x0 \in Acceptor |-> FALSE]
/\ Fluent20_18 = [ x0 \in Acceptor |-> FALSE]
/\ Fluent19_18 = [ x0 \in Acceptor |-> FALSE]

Phase1a(b) ==
/\ msgs1a' = (msgs1a \cup {b})
/\ UNCHANGED <<maxVBal,maxVal,msgs1b,msgs2a>>
/\ UNCHANGED<<Fluent21_18, Fluent20_18, Fluent19_18>>

Phase1b(a,b) ==
/\ (b \in msgs1a)
/\ msgs1b' = (msgs1b \cup {<<a,b,maxVBal[a],maxVal[a]>>})
/\ UNCHANGED <<maxVBal,maxVal,msgs1a,msgs2a>>
/\ Fluent20_18' = [Fluent20_18 EXCEPT ![a] = Fluent21_18[a]]
/\ UNCHANGED<<Fluent21_18, Fluent19_18>>

Phase2a(b,v,a) ==
/\ (<<a,b,maxVBal[a],maxVal[a]>> \in msgs1b)
/\ ~((\E m \in msgs2a : m[1] = b))
/\ (\E Q \in Quorum : LET Q1b == { m \in msgs1b : ((m[1] \in Q) /\ m[2] = b) }
    Q1bv == { m \in Q1b : m[3] >= 0 } IN
  /\ (\A aa \in Q : (\E m \in Q1b : m[1] = aa))
  /\ (Q1bv = {} \/ (\E m \in Q1bv : (m[4] = v /\ (\A mm \in Q1bv : m[3] >= mm[3])))))
/\ msgs2a' = (msgs2a \cup {<<b,v>>})
/\ UNCHANGED <<maxVBal,maxVal,msgs1a,msgs1b>>
/\ UNCHANGED<<Fluent21_18, Fluent20_18, Fluent19_18>>

Phase2b(a,b,v) ==
/\ (<<b,v>> \in msgs2a)
/\ maxVBal' = [maxVBal EXCEPT![a] = b]
/\ maxVal' = [maxVal EXCEPT![a] = v]
/\ UNCHANGED <<msgs1a,msgs1b,msgs2a>>
/\ Fluent21_18' = [Fluent21_18 EXCEPT ![a] = TRUE]
/\ Fluent19_18' = [x0 \in Acceptor |-> Fluent20_18[a]]
/\ UNCHANGED<<Fluent20_18>>

Next ==
\/ (\E b \in Ballot : Phase1a(b))
\/ (\E a \in Acceptor : (\E b \in Ballot : Phase1b(a,b)))
\/ (\E b \in Ballot : (\E v \in Value : (\E a \in Acceptor : Phase2a(b,v,a))))
\/ (\E a \in Acceptor : (\E b \in Ballot : (\E v \in Value : Phase2b(a,b,v))))

Spec == (Init /\ [][Next]_vars)
=============================================================================
