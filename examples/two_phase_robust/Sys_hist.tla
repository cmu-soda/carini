--------------------------- MODULE Sys_hist ---------------------------
EXTENDS Naturals, Sequences, Integers, FiniteSets, TLC

CONSTANTS RMs

VARIABLES Fluent6_0, Fluent5_0, tmState, Fluent4_0, Fluent3_0, tmPrepared, rmState, Fluent13_0, Fluent12_0

vars == <<Fluent6_0, Fluent5_0, tmState, Fluent4_0, Fluent3_0, tmPrepared, rmState, Fluent13_0, Fluent12_0>>

CandSep ==
/\ \A var0 \in RMs : (Fluent4_0[var0]) => (Fluent3_0[var0])
/\ \A var0 \in RMs : (Fluent12_0[var0]) => (Fluent13_0[var0])
/\ \A var0 \in RMs : (Fluent6_0[var0]) => (Fluent5_0[var0])

Symmetry == Permutations(RMs)

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent5_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent4_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent3_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent13_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent12_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ Fluent5_0' = [Fluent5_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent4_0, Fluent3_0, Fluent13_0, Fluent12_0>>
/\ CandSep'

RcvPrepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<tmState,rmState>>
/\ Fluent6_0' = [Fluent6_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent5_0, Fluent4_0, Fluent3_0, Fluent13_0, Fluent12_0>>
/\ CandSep'

SndCommit(rm) ==
/\ (tmState \in {"init","commmitted"})
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ Fluent3_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent4_0, Fluent13_0, Fluent12_0>>
/\ CandSep'

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ Fluent4_0' = [Fluent4_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent3_0, Fluent13_0, Fluent12_0>>
/\ CandSep'

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ Fluent13_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent4_0, Fluent3_0, Fluent12_0>>
/\ CandSep'

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ Fluent12_0' = [Fluent12_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent4_0, Fluent3_0, Fluent13_0>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent4_0, Fluent3_0, Fluent13_0, Fluent12_0>>
/\ CandSep'

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
=============================================================================
