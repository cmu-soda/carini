--------------------------- MODULE T1_hist ---------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS RMs

VARIABLES msgs, tmState, tmPrepared, rmState, Fluent1, Fluent0

vars == <<msgs, tmState, tmPrepared, rmState, Fluent1, Fluent0>>

CandSep ==
/\ \A var0 \in RMs : \E var1 \in RMs : (Fluent1[var0]) => (Fluent0[var1])

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ rmState = [rm \in RMs |-> "working"]
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent1 = [ x0 \in RMs |-> FALSE]
/\ Fluent0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ UNCHANGED<<Fluent1, Fluent0>>

RcvPrepare(rm) ==
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs,tmState,rmState>>
/\ UNCHANGED<<Fluent1, Fluent0>>

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ UNCHANGED<<Fluent1, Fluent0>>

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ UNCHANGED<<Fluent1, Fluent0>>

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ Fluent1' = [Fluent1 EXCEPT ![rm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<>>

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ Fluent1' = [Fluent1 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent0>>

SilentAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<tmState,tmPrepared,msgs>>
/\ UNCHANGED<<Fluent1, Fluent0>>

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
/\ Fluent1 \in [RMs -> BOOLEAN]
/\ Fluent0 \in [RMs -> BOOLEAN]

IISpec == TypeOK /\ CandSep /\ [][Next]_vars

=============================================================================
