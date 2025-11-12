--------------------------- MODULE C1_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS Acceptor, Value, Ballot

VARIABLES msgs2a, Fluent7_2, Fluent6_2, msgs2b, Fluent13_14, Fluent14_14, Fluent15_14

vars == <<msgs2a, Fluent7_2, Fluent6_2, msgs2b, Fluent13_14, Fluent14_14, Fluent15_14>>

CandSep ==
/\ \A var0 \in Ballot : \A var1 \in Ballot : (Fluent6_2[var1]) => ((Fluent7_2[var0]) => (var0 <= var1))
/\ \A var0 \in Value : \E var1 \in Acceptor : (Fluent15_14[var0]) => ((Fluent13_14[var1]) => (Fluent14_14[var0]))

Quorum == { i \in SUBSET(Acceptor) : (Cardinality(i) * 2) > Cardinality(Acceptor) }

None == "None"

TypeOK ==
/\ (msgs2a \in SUBSET((Ballot \X Value)))
/\ (msgs2b \in SUBSET((Acceptor \X Ballot \X Value)))

Init ==
/\ msgs2a = {}
/\ msgs2b = {}
/\ Fluent13_14 = [ x0 \in Acceptor |-> FALSE]
/\ Fluent7_2 = [ x0 \in Ballot |-> FALSE]
/\ Fluent6_2 = [ x0 \in Ballot |-> FALSE]
/\ Fluent14_14 = [ x0 \in Value |-> FALSE]
/\ Fluent15_14 = [ x0 \in Value |-> FALSE]

Phase2a(b,v,a) ==
/\ ~((\E m \in msgs2a : m[1] = b))
/\ msgs2a' = (msgs2a \cup {<<b,v>>})
/\ UNCHANGED <<msgs2b>>
/\ Fluent7_2' = [Fluent7_2 EXCEPT ![b] = TRUE]
/\ Fluent6_2' = [x0 \in Ballot |-> FALSE]
/\ Fluent15_14' = [Fluent15_14 EXCEPT ![v] = TRUE]
/\ UNCHANGED<<Fluent13_14, Fluent14_14>>
/\ CandSep'

Phase2b(a,b,v) ==
/\ (<<b,v>> \in msgs2a)
/\ msgs2b' = (msgs2b \cup {<<a,b,v>>})
/\ UNCHANGED <<msgs2a>>
/\ Fluent13_14' = [Fluent13_14 EXCEPT ![a] = TRUE]
/\ Fluent6_2' = [Fluent6_2 EXCEPT ![b] = TRUE]
/\ Fluent14_14' = [Fluent14_14 EXCEPT ![v] = TRUE]
/\ Fluent15_14' = [x0 \in Value |-> FALSE]
/\ UNCHANGED<<Fluent7_2>>
/\ CandSep'

Next ==
\/ (\E b \in Ballot : (\E v \in Value : (\E a \in Acceptor : Phase2a(b,v,a))))
\/ (\E a \in Acceptor : (\E b \in Ballot : (\E v \in Value : Phase2b(a,b,v))))

Spec == (Init /\ [][Next]_vars)

ChosenAt(b,v) ==
\E Q \in Quorum :
\A a \in Q :
(<<a,b,v>> \in msgs2b)

chosen == { v \in Value : (\E b \in Ballot : ChosenAt(b,v)) }

Safety == (\A v,w \in chosen : v = w)
=============================================================================
