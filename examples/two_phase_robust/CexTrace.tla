--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Sequences, Integers, FiniteSets, TLC

CONSTANTS r2, r3, RMs, r1

VARIABLES tmState, err, tmPrepared, rmState, Fluent13_0, cexTraceIdx, Fluent12_0

vars == <<tmState, err, tmPrepared, rmState, Fluent13_0, cexTraceIdx, Fluent12_0>>

NoErr == err = FALSE

CandSep == (\A var0 \in RMs : (Fluent12_0[var0] => Fluent13_0[var0]))

Symmetry == Permutations(RMs)

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent13_0 = [x0 \in RMs |-> FALSE]
/\ Fluent12_0 = [x0 \in RMs |-> FALSE]
/\ cexTraceIdx = 0
/\ err = FALSE

SndPrepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ UNCHANGED <<Fluent13_0,Fluent12_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

RcvPrepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<tmState,rmState>>
/\ UNCHANGED <<Fluent13_0,Fluent12_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

SndCommit(rm) ==
/\ (tmState \in {"init","commmitted"})
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ UNCHANGED <<Fluent13_0,Fluent12_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ UNCHANGED <<Fluent13_0,Fluent12_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ Fluent13_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED <<Fluent12_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ Fluent12_0' = [Fluent12_0 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent13_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ UNCHANGED <<Fluent13_0,Fluent12_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ RcvCommit(rm)
\/ SndAbort(rm)
\/ RcvAbort(rm)
\/ SilentAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))

TraceConstraint ==
/\ cexTraceIdx = 0 => SndPrepare(r1) /\ err' = err
/\ cexTraceIdx = 1 => RcvPrepare(r1) /\ err' = err
/\ cexTraceIdx = 2 => RcvPrepare(r2) /\ err' = err
/\ cexTraceIdx = 3 => SilentAbort(r2) /\ err' = err
/\ cexTraceIdx = 4 => RcvPrepare(r3) /\ err' = err
/\ cexTraceIdx = 5 => SndCommit(r1) /\ err' = err
/\ cexTraceIdx = 6 => RcvCommit(r1) /\ err' = TRUE
/\ cexTraceIdx >= 7 => FALSE

InternalAction == UNCHANGED<<cexTraceIdx,err>>

TraceConstraintSpec == Init /\ [][Next /\ (TraceConstraint \/ InternalAction)]_vars
=============================================================================
