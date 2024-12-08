--------------------------- MODULE D0_hist ---------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS RMs

VARIABLES Fluent11, tmState, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, rmState

vars == <<Fluent11, tmState, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, rmState>>

CandSep ==
/\ \A var0 \in RMs : (Fluent0[var0]) => (Fluent1[var0])
/\ \A var0 \in RMs : (Fluent2[var0]) => (Fluent3[var0])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent4[var0]) => (Fluent5[var1])
/\ \A var0 \in RMs : (Fluent7[var0]) => (Fluent6[var0])
/\ \A var0 \in RMs : \E var1 \in RMs : (Fluent9[var0]) => (Fluent8[var1])
/\ \A var0 \in RMs : \E var1 \in RMs : (Fluent11[var0]) => (Fluent10[var1])

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ tmState = "init"
/\ Fluent11 = [ x0 \in RMs |-> FALSE]
/\ Fluent9 = [ x0 \in RMs |-> FALSE]
/\ Fluent8 = [ x0 \in RMs |-> FALSE]
/\ Fluent7 = [ x0 \in RMs |-> FALSE]
/\ Fluent6 = [ x0 \in RMs |-> FALSE]
/\ Fluent5 = [ x0 \in RMs |-> FALSE]
/\ Fluent10 = [ x0 \in RMs |-> FALSE]
/\ Fluent4 = [ x0 \in RMs |-> FALSE]
/\ Fluent3 = [ x0 \in RMs |-> FALSE]
/\ Fluent2 = [ x0 \in RMs |-> FALSE]
/\ Fluent1 = [ x0 \in RMs |-> FALSE]
/\ Fluent0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ UNCHANGED <<tmState>>
/\ Fluent6' = [Fluent6 EXCEPT ![rm] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent9, Fluent8, Fluent7, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent0>>
/\ CandSep'

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ UNCHANGED <<tmState>>
/\ Fluent11' = [Fluent11 EXCEPT ![rm] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT ![rm] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT ![rm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent3, Fluent1>>
/\ CandSep'

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<tmState>>
/\ Fluent9' = [Fluent9 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<tmState>>
/\ UNCHANGED<<Fluent11, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

RcvPrepare(rm) ==
/\ tmState = "init"
/\ UNCHANGED <<tmState>>
/\ UNCHANGED <<rmState>>
/\ Fluent7' = [Fluent7 EXCEPT ![rm] = TRUE]
/\ Fluent5' = [Fluent5 EXCEPT ![rm] = TRUE]
/\ Fluent3' = [Fluent3 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent9, Fluent8, Fluent6, Fluent10, Fluent4, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

SndCommit(rm) ==
/\ (tmState \in {"init","commmitted"})
/\ tmState' = "committed"
/\ UNCHANGED <<rmState>>
/\ Fluent10' = [Fluent10 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<rmState>>
/\ Fluent8' = [Fluent8 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent9, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
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

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))
=============================================================================
