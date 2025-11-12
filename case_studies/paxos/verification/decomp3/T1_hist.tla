--------------------------- MODULE T1_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS Acceptor, Value, Ballot

VARIABLES msgs1a, maxBal, Fluent3_14, Fluent4_14, Fluent2_14

vars == <<msgs1a, maxBal, Fluent3_14, Fluent4_14, Fluent2_14>>

CandSep ==
\A var0 \in Acceptor : \A var1 \in Ballot : (Fluent4_14[var0][var1]) => ((Fluent3_14[var0][var1]) => (Fluent2_14[var0][var1]))

Quorum == { i \in SUBSET(Acceptor) : (Cardinality(i) * 2) > Cardinality(Acceptor) }

None == "None"

TypeOK ==
/\ (maxBal \in [Acceptor -> (Ballot \cup {-.(1)})])
/\ (msgs1a \in SUBSET(Ballot))

Init ==
/\ maxBal = [a \in Acceptor |-> -.(1)]
/\ msgs1a = {}
/\ Fluent3_14 = [ x0 \in Acceptor |-> [ x1 \in Ballot |-> FALSE]]
/\ Fluent4_14 = [ x0 \in Acceptor |-> [ x1 \in Ballot |-> FALSE]]
/\ Fluent2_14 = [ x0 \in Acceptor |-> [ x1 \in Ballot |-> FALSE]]

Phase1a(b) ==
/\ msgs1a' = (msgs1a \cup {b})
/\ UNCHANGED <<maxBal>>
/\ UNCHANGED<<Fluent3_14, Fluent4_14, Fluent2_14>>

Phase1b(a,b) ==
/\ (b \in msgs1a)
/\ b > maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ UNCHANGED <<msgs1a>>
/\ Fluent4_14' = [Fluent4_14 EXCEPT ![a][b] = TRUE]
/\ Fluent2_14' = [[Fluent2_14 EXCEPT ![a] = [x0 \in Ballot |-> FALSE]] EXCEPT ![a][b] = TRUE]
/\ UNCHANGED<<Fluent3_14>>

Phase2b(a,b,v) ==
/\ b >= maxBal[a]
/\ maxBal' = [maxBal EXCEPT![a] = b]
/\ UNCHANGED <<msgs1a>>
/\ Fluent3_14' = [Fluent3_14 EXCEPT ![a][b] = TRUE]
/\ UNCHANGED<<Fluent4_14, Fluent2_14>>

Next ==
\/ (\E b \in Ballot : Phase1a(b))
\/ (\E a \in Acceptor : (\E b \in Ballot : Phase1b(a,b)))
\/ (\E a \in Acceptor : (\E b \in Ballot : (\E v \in Value : Phase2b(a,b,v))))

Spec == (Init /\ [][Next]_vars)
=============================================================================
