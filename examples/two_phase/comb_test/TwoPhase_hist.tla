--------------------------- MODULE TwoPhase_hist ---------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS RMs

VARIABLES msgs, tmState, Fluent14, tmPrepared, Fluent5, Fluent4, rmState, Fluent3, Fluent2, Fluent1, Fluent0, Fluent15

vars == <<msgs, tmState, Fluent14, tmPrepared, Fluent5, Fluent4, rmState, Fluent3, Fluent2, Fluent1, Fluent0, Fluent15>>

CandSep ==
\A var0 \in RMs : \A var1 \in RMs : (Fluent15[var0]) => (~(Fluent14[var1]))

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ rmState = [rm \in RMs |-> "working"]
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent14 = [ x0 \in RMs |-> FALSE]
/\ Fluent15 = [ x0 \in RMs |-> FALSE]
/\ Fluent5 = [ x0 \in RMs |-> FALSE]
/\ Fluent4 = [ x0 \in RMs |-> FALSE]
/\ Fluent3 = [ x0 \in RMs |-> FALSE]
/\ Fluent2 = [ x0 \in RMs |-> FALSE]
/\ Fluent1 = [ x0 \in RMs |-> FALSE]
/\ Fluent0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ UNCHANGED<<Fluent14, Fluent15>>
/\ Fluent3' = [Fluent3 EXCEPT ![rm] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent5, Fluent4, Fluent2, Fluent0>>

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs,tmState,rmState>>
/\ UNCHANGED<<Fluent14, Fluent15>>
/\ UNCHANGED<<Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ (tmState \in {"init","commmitted"})
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ Fluent14' = [Fluent14 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent15>>
/\ UNCHANGED<<Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ UNCHANGED<<Fluent14, Fluent15>>
/\ Fluent4' = [Fluent4 EXCEPT ![rm] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT ![rm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent5, Fluent3, Fluent1>>

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ Fluent15' = [Fluent15 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent14>>
/\ UNCHANGED<<Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ UNCHANGED<<Fluent14, Fluent15>>
/\ Fluent5' = [Fluent5 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<tmState,tmPrepared,msgs>>
/\ UNCHANGED<<Fluent14, Fluent15>>
/\ UNCHANGED<<Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>

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

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))
=============================================================================
