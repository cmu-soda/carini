--------------------------- MODULE C1_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS Acceptor, Value, Ballot

VARIABLES Fluent5_5, Fluent4_5, msgs2b, maxBal, Fluent8_6, Fluent7_6

vars == <<Fluent5_5, Fluent4_5, msgs2b, maxBal, Fluent8_6, Fluent7_6>>

CandSep ==
/\ \A var0 \in Ballot : \E var1 \in Acceptor : \A var2 \in Value : (Fluent4_5[var2][var1]) => (Fluent5_5[var1][var2][var0])
/\ \A var0 \in Ballot : (Fluent8_6[var0]) => (Fluent7_6[var0])

Quorum == { i \in SUBSET(Acceptor) : (Cardinality(i) * 2) > Cardinality(Acceptor) }

None == "None"

TypeOK ==
/\ (maxBal \in [Acceptor -> (Ballot \cup {-.(1)})])
/\ (msgs2b \in SUBSET((Acceptor \X Ballot \X Value)))

Init ==
/\ maxBal = [a \in Acceptor |-> -.(1)]
/\ msgs2b = {}
/\ Fluent8_6 = [ x0 \in Ballot |-> FALSE]
/\ Fluent7_6 = [ x0 \in Ballot |-> FALSE]
/\ Fluent5_5 = [ x0 \in Acceptor |-> [ x1 \in Value |-> [ x2 \in Ballot |-> FALSE]]]
/\ Fluent4_5 = [ x0 \in Value |-> [ x1 \in Acceptor |-> FALSE]]

Phase1b(a,b) ==
/\ b > maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ UNCHANGED <<msgs2b>>
/\ Fluent7_6' = [Fluent7_6 EXCEPT ![b] = TRUE]
/\ Fluent5_5' = [Fluent5_5 EXCEPT ![a] = [x0 \in Value |-> [x1 \in Ballot |-> TRUE]]]
/\ Fluent4_5' = [x0 \in Value |-> [x1 \in Acceptor |-> TRUE]]
/\ UNCHANGED<<Fluent8_6>>
/\ CandSep'

Phase2b(a,b,v) ==
/\ b >= maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ msgs2b' = (msgs2b \cup {<<a,b,v>>})
/\ Fluent8_6' = [Fluent8_6 EXCEPT ![b] = TRUE]
/\ Fluent5_5' = [Fluent5_5 EXCEPT ![a][v][b] = FALSE]
/\ Fluent4_5' = [[Fluent4_5 EXCEPT ![v] = [x0 \in Acceptor |-> FALSE]] EXCEPT ![v][a] = TRUE]
/\ UNCHANGED<<Fluent7_6>>
/\ CandSep'

Next ==
\/ (\E a \in Acceptor : (\E b \in Ballot : Phase1b(a,b)))
\/ (\E a \in Acceptor : (\E b \in Ballot : (\E v \in Value : Phase2b(a,b,v))))

Spec == (Init /\ [][Next]_vars)

ChosenAt(b,v) ==
\E Q \in Quorum :
\A a \in Q :
(<<a,b,v>> \in msgs2b)

chosen == { v \in Value : (\E b \in Ballot : ChosenAt(b,v)) }

Safety == (\A v,w \in chosen : v = w)
=============================================================================
