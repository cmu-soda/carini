--------------------------- MODULE C1 ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS Acceptor, Value, Ballot

VARIABLES msgs2a, msgs2b, Fluent14_12, Fluent15_12

vars == <<msgs2a, msgs2b, Fluent14_12, Fluent15_12>>

IncSep ==
/\ \A var0 \in Acceptor : \E var1 \in Ballot : (Fluent15_12[var0][var1]) => (~(Fluent14_12[var0][var1]))

Quorum == { i \in SUBSET(Acceptor) : (Cardinality(i) * 2) > Cardinality(Acceptor) }

None == "None"

TypeOK ==
/\ (msgs2a \in SUBSET((Ballot \X Value)))
/\ (msgs2b \in SUBSET((Acceptor \X Ballot \X Value)))

Init ==
/\ msgs2a = {}
/\ msgs2b = {}
/\ Fluent14_12 = [ x0 \in Acceptor |-> [ x1 \in Ballot |-> FALSE]]
/\ Fluent15_12 = [ x0 \in Acceptor |-> [ x1 \in Ballot |-> FALSE]]

Phase2a(b,v,a) ==
/\ ~((\E m \in msgs2a : m[1] = b))
/\ msgs2a' = (msgs2a \cup {<<b,v>>})
/\ UNCHANGED <<msgs2b>>
/\ Fluent14_12' = [[Fluent14_12 EXCEPT ![a] = [x0 \in Ballot |-> FALSE]] EXCEPT ![a][b] = TRUE]
/\ Fluent15_12' = [Fluent15_12 EXCEPT ![a][b] = TRUE]
/\ UNCHANGED<<>>
/\ IncSep'

Phase2b(a,b,v) ==
/\ (<<b,v>> \in msgs2a)
/\ msgs2b' = (msgs2b \cup {<<a,b,v>>})
/\ UNCHANGED <<msgs2a>>
/\ Fluent14_12' = [Fluent14_12 EXCEPT ![a][b] = TRUE]
/\ UNCHANGED<<Fluent15_12>>
/\ IncSep'

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
