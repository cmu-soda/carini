--------------------------- MODULE T1_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS Acceptor, Value, Ballot

VARIABLES msgs2a, msgs1a, maxBal, Fluent23_12, Fluent22_12

vars == <<msgs2a, msgs1a, maxBal, Fluent23_12, Fluent22_12>>

CandSep ==
\E var0 \in Value : \A var1 \in Ballot : \E var2 \in Acceptor : (Fluent23_12[var1][var0]) => (~(Fluent22_12[var1][var0][var2]))

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
/\ Fluent23_12 = [ x0 \in Ballot |-> [ x1 \in Value |-> FALSE]]
/\ Fluent22_12 = [ x0 \in Ballot |-> [ x1 \in Value |-> [ x2 \in Acceptor |-> FALSE]]]

Phase1a(b) ==
/\ msgs1a' = (msgs1a \cup {b})
/\ UNCHANGED <<maxBal,msgs2a>>
/\ UNCHANGED<<Fluent23_12, Fluent22_12>>

Phase1b(a,b) ==
/\ (b \in msgs1a)
/\ b > maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ UNCHANGED <<msgs1a,msgs2a>>
/\ Fluent22_12' = [Fluent22_12 EXCEPT ![b] = [x0 \in Value |-> [x1 \in Acceptor |-> TRUE]]]
/\ UNCHANGED<<Fluent23_12>>

Phase2a(b,v,a) ==
/\ ~((\E m \in msgs2a : m[1] = b))
/\ msgs2a' = (msgs2a \cup {<<b,v>>})
/\ UNCHANGED <<maxBal,msgs1a>>
/\ Fluent22_12' = [Fluent22_12 EXCEPT ![b][v][a] = FALSE]
/\ UNCHANGED<<Fluent23_12>>

Phase2b(a,b,v) ==
/\ (<<b,v>> \in msgs2a)
/\ b >= maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ UNCHANGED <<msgs1a,msgs2a>>
/\ Fluent23_12' = [Fluent23_12 EXCEPT ![b][v] = TRUE]
/\ Fluent22_12' = [Fluent22_12 EXCEPT ![b][v][a] = TRUE]
/\ UNCHANGED<<>>

Next ==
\/ (\E b \in Ballot : Phase1a(b))
\/ (\E a \in Acceptor : (\E b \in Ballot : Phase1b(a,b)))
\/ (\E b \in Ballot : (\E v \in Value : (\E a \in Acceptor : Phase2a(b,v,a))))
\/ (\E a \in Acceptor : (\E b \in Ballot : (\E v \in Value : Phase2b(a,b,v))))

Spec == (Init /\ [][Next]_vars)
=============================================================================
