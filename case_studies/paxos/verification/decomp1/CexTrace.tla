--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS a1, a2, Acceptor, Value, v1, v2, Ballot, NUM0, NUM1

VARIABLES msgs2a, err, Fluent7_2, Fluent6_2, msgs2b, cexTraceIdx

vars == <<msgs2a, err, Fluent7_2, Fluent6_2, msgs2b, cexTraceIdx>>

NoErr == err = FALSE

CandSep == (\A var0 \in Ballot : (\A var1 \in Ballot : (Fluent6_2[var1] => (Fluent7_2[var0] => var0 <= var1))))

Quorum == { i \in SUBSET(Acceptor) : (Cardinality(i) * 2) > Cardinality(Acceptor) }

None == "None"

TypeOK ==
/\ (msgs2a \in SUBSET((Ballot \X Value)))
/\ (msgs2b \in SUBSET((Acceptor \X Ballot \X Value)))

Init ==
/\ msgs2a = {}
/\ msgs2b = {}
/\ Fluent7_2 = [x0 \in Ballot |-> FALSE]
/\ Fluent6_2 = [x0 \in Ballot |-> FALSE]
/\ cexTraceIdx = 0
/\ err = FALSE

Phase2a(b,v,a) ==
/\ ~((\E m \in msgs2a : m[1] = b))
/\ msgs2a' = (msgs2a \cup {<<b,v>>})
/\ UNCHANGED <<msgs2b>>
/\ Fluent7_2' = [Fluent7_2 EXCEPT![b] = TRUE]
/\ Fluent6_2' = [x0 \in Ballot |-> FALSE]
/\ UNCHANGED <<>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

Phase2b(a,b,v) ==
/\ (<<b,v>> \in msgs2a)
/\ msgs2b' = (msgs2b \cup {<<a,b,v>>})
/\ UNCHANGED <<msgs2a>>
/\ Fluent6_2' = [Fluent6_2 EXCEPT![b] = TRUE]
/\ UNCHANGED <<Fluent7_2>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

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

TraceConstraint ==
/\ cexTraceIdx = 0 => Phase2a(0,v2,a1) /\ err' = err
/\ cexTraceIdx = 1 => Phase2b(a1,0,v2) /\ err' = err
/\ cexTraceIdx = 2 => Phase2b(a2,0,v2) /\ err' = err
/\ cexTraceIdx = 3 => Phase2a(1,v1,a1) /\ err' = err
/\ cexTraceIdx = 4 => Phase2b(a2,1,v1) /\ err' = err
/\ cexTraceIdx = 5 => Phase2b(a1,1,v1) /\ err' = TRUE
/\ cexTraceIdx >= 6 => FALSE

InternalAction == UNCHANGED<<cexTraceIdx,err>>

TraceConstraintSpec == Init /\ [][Next /\ (TraceConstraint \/ InternalAction)]_vars
=============================================================================
