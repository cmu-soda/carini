--------------------------- MODULE TwoPhase_hist ---------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS RMs

VARIABLES msgs, tmState, Fluent36, rmPrepared, tmPrepared, rmWorking, rmCommitted, Fluent37, rmAborted

vars == <<msgs, tmState, Fluent36, rmPrepared, tmPrepared, rmWorking, rmCommitted, Fluent37, rmAborted>>

CandSep ==
\A var0 \in RMs : (Fluent36[var0]) => (Fluent37[var0])

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ rmWorking = [rm \in RMs |-> TRUE]
/\ rmPrepared = [rm \in RMs |-> FALSE]
/\ rmAborted = [rm \in RMs |-> FALSE]
/\ rmCommitted = [rm \in RMs |-> FALSE]
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent36 = [ x0 \in RMs |-> FALSE]
/\ Fluent37 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ rmWorking[rm]
/\ rmWorking' = [rmWorking EXCEPT![rm] = FALSE]
/\ rmPrepared' = [rmPrepared EXCEPT![rm] = TRUE]
/\ UNCHANGED <<tmState,tmPrepared,rmAborted,rmCommitted>>
/\ UNCHANGED<<Fluent36, Fluent37>>

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs,tmState,rmWorking,rmPrepared,rmAborted,rmCommitted>>
/\ Fluent37' = [Fluent37 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent36>>

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ (tmState \in {"init","commmitted"})
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared,rmWorking,rmPrepared,rmAborted,rmCommitted>>
/\ UNCHANGED<<Fluent36, Fluent37>>

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ rmPrepared' = [rmWorking EXCEPT![rm] = FALSE]
/\ rmCommitted' = [rmPrepared EXCEPT![rm] = TRUE]
/\ UNCHANGED <<msgs,tmState,tmPrepared,rmWorking,rmAborted>>
/\ UNCHANGED<<Fluent36, Fluent37>>

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared,rmWorking,rmPrepared,rmAborted,rmCommitted>>
/\ UNCHANGED<<Fluent36, Fluent37>>

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ rmWorking' = [rmWorking EXCEPT![rm] = FALSE]
/\ rmPrepared' = [rmPrepared EXCEPT![rm] = FALSE]
/\ rmAborted' = [rmAborted EXCEPT![rm] = TRUE]
/\ UNCHANGED <<msgs,tmState,tmPrepared,rmCommitted>>
/\ Fluent36' = [Fluent36 EXCEPT ![rm] = TRUE]
/\ Fluent37' = [Fluent37 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<>>

SilentAbort(rm) ==
/\ rmWorking[rm]
/\ rmWorking' = [rmWorking EXCEPT![rm] = FALSE]
/\ rmAborted' = [rmAborted EXCEPT![rm] = TRUE]
/\ UNCHANGED <<tmState,tmPrepared,msgs,rmCommitted,rmPrepared>>
/\ UNCHANGED<<Fluent36, Fluent37>>

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
/\ (rmWorking \in [RMs -> BOOLEAN])
/\ (rmPrepared \in [RMs -> BOOLEAN])
/\ (rmAborted \in [RMs -> BOOLEAN])
/\ (rmCommitted \in [RMs -> BOOLEAN])
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))

Consistent == (\A rm1,rm2 \in RMs : ~((rmAborted[rm1] /\ rmCommitted[rm2])))

IISpec == ((TypeOK /\ Consistent) /\ [][Next]_vars)
=============================================================================
