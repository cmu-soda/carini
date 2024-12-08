--------------------------- MODULE D0_hist ---------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS RMs

VARIABLES tmState, tmPrepared, Fluent5, Fluent4, rmState, Fluent3, Fluent2, Fluent1, Fluent0

vars == <<tmState, tmPrepared, Fluent5, Fluent4, rmState, Fluent3, Fluent2, Fluent1, Fluent0>>

CandSep ==
/\ \A var0 \in RMs : \E var1 \in RMs : (Fluent1[var0]) => (Fluent0[var1])
/\ \A var0 \in RMs : \E var1 \in RMs : (Fluent3[var0]) => (Fluent2[var1])
/\ \A var0 \in RMs : (Fluent5[var0]) => (Fluent4[var0])

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent3 = [ x0 \in RMs |-> FALSE]
/\ Fluent2 = [ x0 \in RMs |-> FALSE]
/\ Fluent1 = [ x0 \in RMs |-> FALSE]
/\ Fluent0 = [ x0 \in RMs |-> FALSE]
/\ Fluent5 = [ x0 \in RMs |-> FALSE]
/\ Fluent4 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ Fluent4' = [Fluent4 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent3, Fluent2, Fluent1, Fluent0, Fluent5>>
/\ CandSep'

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ Fluent3' = [Fluent3 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0, Fluent5, Fluent4>>
/\ CandSep'

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ Fluent1' = [Fluent1 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent3, Fluent2, Fluent0, Fluent5, Fluent4>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ UNCHANGED<<Fluent3, Fluent2, Fluent1, Fluent0, Fluent5, Fluent4>>
/\ CandSep'

RcvPrepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<tmState>>
/\ UNCHANGED <<rmState>>
/\ Fluent5' = [Fluent5 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent3, Fluent2, Fluent1, Fluent0, Fluent4>>
/\ CandSep'

SndCommit(rm) ==
/\ (tmState \in {"init","commmitted"})
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED <<rmState>>
/\ Fluent2' = [Fluent2 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent3, Fluent1, Fluent0, Fluent5, Fluent4>>
/\ CandSep'

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED <<rmState>>
/\ Fluent0' = [Fluent0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent3, Fluent2, Fluent1, Fluent5, Fluent4>>
/\ CandSep'

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvCommit(rm)
\/ RcvAbort(rm)
\/ SilentAbort(rm)
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ SndAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))
=============================================================================
