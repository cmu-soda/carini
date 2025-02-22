--------------------------- MODULE C1_hist ---------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS RMs

VARIABLES msgs, tmState, tmPrepared, rmState, Fluent3, Fluent2, Fluent1, Fluent0

vars == <<msgs, tmState, tmPrepared, rmState, Fluent3, Fluent2, Fluent1, Fluent0>>

CandSep ==
/\ \A var0 \in RMs : (Fluent1[var0]) => (Fluent0[var0])
/\ \A var0 \in RMs : \E var1 \in RMs : (Fluent3[var0]) => (Fluent2[var1])

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))

Init ==
/\ msgs = {}
/\ ((rmState \in [RMs -> {"working","prepared","committed","aborted"}]) /\ Consistent)
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent3 = [ x0 \in RMs |-> FALSE]
/\ Fluent2 = [ x0 \in RMs |-> FALSE]
/\ Fluent1 = [ x0 \in RMs |-> FALSE]
/\ Fluent0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ Fluent1' = [Fluent1 EXCEPT ![rm] = FALSE]
/\ Fluent0' = [Fluent0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent3, Fluent2>>
/\ CandSep'

RcvPrepare(rm) ==
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs,tmState,rmState>>
/\ UNCHANGED<<Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ UNCHANGED<<Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ Fluent1' = [Fluent1 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent3, Fluent2, Fluent0>>
/\ CandSep'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ Fluent3' = [Fluent3 EXCEPT ![rm] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent1, Fluent0>>
/\ CandSep'

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ Fluent3' = [Fluent3 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<tmState,tmPrepared,msgs>>
/\ UNCHANGED<<Fluent3, Fluent2, Fluent1, Fluent0>>
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
/\ (msgs \in SUBSET(Message))
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
=============================================================================
