--------------------------- MODULE C1_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS Acceptor, Value, Ballot

VARIABLES Fluent13_3, Fluent7_3, Fluent3_7, Fluent11_8, Fluent6_3, Fluent10_8, msgs2b, maxBal, Fluent12_8, Fluent4_7

vars == <<Fluent13_3, Fluent7_3, Fluent3_7, Fluent11_8, Fluent6_3, Fluent10_8, msgs2b, maxBal, Fluent12_8, Fluent4_7>>

CandSep ==
/\ \A var0 \in Ballot : (Fluent6_3[var0]) => (Fluent7_3[var0])
/\ \A var0 \in Acceptor : (Fluent3_7[var0]) => (Fluent4_7[var0])
/\ \A var0 \in Ballot : (Fluent12_8[var0]) => ((Fluent11_8[var0]) => (Fluent10_8[var0]))
/\ \A var0 \in Ballot : \E var1 \in Value : ~(Fluent13_3[var1][var0])

Quorum == { i \in SUBSET(Acceptor) : (Cardinality(i) * 2) > Cardinality(Acceptor) }

None == "None"

TypeOK ==
/\ (maxBal \in [Acceptor -> (Ballot \cup {-.(1)})])
/\ (msgs2b \in SUBSET((Acceptor \X Ballot \X Value)))

Init ==
/\ maxBal = [a \in Acceptor |-> -.(1)]
/\ msgs2b = {}
/\ Fluent13_3 = [ x0 \in Value |-> [ x1 \in Ballot |-> FALSE]]
/\ Fluent7_3 = [ x0 \in Ballot |-> FALSE]
/\ Fluent3_7 = [ x0 \in Acceptor |-> FALSE]
/\ Fluent11_8 = [ x0 \in Ballot |-> FALSE]
/\ Fluent6_3 = [ x0 \in Ballot |-> FALSE]
/\ Fluent10_8 = [ x0 \in Ballot |-> FALSE]
/\ Fluent12_8 = [ x0 \in Ballot |-> FALSE]
/\ Fluent4_7 = [ x0 \in Acceptor |-> FALSE]

Phase1b(a,b) ==
/\ b > maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ UNCHANGED <<msgs2b>>
/\ Fluent7_3' = [Fluent7_3 EXCEPT ![b] = TRUE]
/\ Fluent11_8' = [Fluent11_8 EXCEPT ![b] = TRUE]
/\ Fluent10_8' = [Fluent10_8 EXCEPT ![b] = Fluent11_8[b]]
/\ Fluent4_7' = [[x0 \in Acceptor |-> TRUE] EXCEPT ![a] = Fluent4_7[a]]
/\ UNCHANGED<<Fluent13_3, Fluent3_7, Fluent6_3, Fluent12_8>>
/\ CandSep'

Phase2b(a,b,v) ==
/\ b >= maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ msgs2b' = (msgs2b \cup {<<a,b,v>>})
/\ Fluent13_3' = [Fluent13_3 EXCEPT ![v][b] = TRUE]
/\ Fluent3_7' = [Fluent3_7 EXCEPT ![a] = TRUE]
/\ Fluent6_3' = [Fluent6_3 EXCEPT ![b] = TRUE]
/\ Fluent12_8' = [Fluent12_8 EXCEPT ![b] = TRUE]
/\ UNCHANGED<<Fluent7_3, Fluent11_8, Fluent10_8, Fluent4_7>>
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
