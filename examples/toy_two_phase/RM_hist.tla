--------------------------- MODULE RM_hist ---------------------------
EXTENDS Naturals, Sequences, Integers, FiniteSets, TLC

CONSTANTS RMs

VARIABLES Fluent6_0, Fluent5_0, rmState, Fluent13_0, Fluent12_0

vars == <<Fluent6_0, Fluent5_0, rmState, Fluent13_0, Fluent12_0>>

CandSep ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent12_0[var0]) => (~(Fluent13_0[var1]))
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent6_0[var1]) => (Fluent5_0[var0])

Symmetry == Permutations(RMs)

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent5_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent13_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent12_0 = [ x0 \in RMs |-> FALSE]

Prepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ Fluent5_0' = [Fluent5_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent13_0, Fluent12_0>>
/\ CandSep'

Commit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "commit"]
/\ Fluent6_0' = [Fluent6_0 EXCEPT ![rm] = TRUE]
/\ Fluent13_0' = [Fluent13_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent5_0, Fluent12_0>>
/\ CandSep'

Abort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "abort"]
/\ Fluent12_0' = [Fluent12_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent13_0>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "abort"]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent13_0, Fluent12_0>>
/\ CandSep'

Next ==
\E rm \in RMs :
\/ Prepare(rm)
\/ Commit(rm)
\/ Abort(rm)
\/ SilentAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (rmState \in [RMs -> {"working","prepared","commit","abort"}])

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "abort" /\ rmState[rm2] = "commit")))
=============================================================================
