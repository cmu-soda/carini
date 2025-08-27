--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Sequences, Integers, FiniteSets, TLC

CONSTANTS r2, r3, RMs, r1

VARIABLES Fluent6_0, Fluent5_0, err, rmState, cexTraceIdx

vars == <<Fluent6_0, Fluent5_0, err, rmState, cexTraceIdx>>

NoErr == err = FALSE

CandSep == (\A var0 \in RMs : (\A var1 \in RMs : (Fluent6_0[var1] => Fluent5_0[var0])))

Symmetry == Permutations(RMs)

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ Fluent6_0 = [x0 \in RMs |-> FALSE]
/\ Fluent5_0 = [x0 \in RMs |-> FALSE]
/\ cexTraceIdx = 0
/\ err = FALSE

Prepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ Fluent5_0' = [Fluent5_0 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent6_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

Commit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "commit"]
/\ Fluent6_0' = [Fluent6_0 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent5_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

Abort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "abort"]
/\ UNCHANGED <<Fluent6_0,Fluent5_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "abort"]
/\ UNCHANGED <<Fluent6_0,Fluent5_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

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

TraceConstraint ==
/\ cexTraceIdx = 0 => Commit(r1) /\ err' = err
/\ cexTraceIdx = 1 => SilentAbort(r2) /\ err' = TRUE
/\ cexTraceIdx >= 2 => FALSE

InternalAction == UNCHANGED<<cexTraceIdx,err>>

TraceConstraintSpec == Init /\ [][Next /\ (TraceConstraint \/ InternalAction)]_vars
=============================================================================
