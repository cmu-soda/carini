------------------------------- MODULE TwoPhase ----------------------------- 

EXTENDS Sequences, Naturals, Integers

CONSTANTS RMs

VARIABLES msgs, rmWorking, rmPrepared, rmAborted, rmCommitted, tmState, tmPrepared

vars == <<msgs, rmWorking, rmPrepared, rmAborted, rmCommitted, tmState, tmPrepared>>

Message ==
  [type : {"Prepared"}, theRM : RMs]  \cup  [type : {"Commit", "Abort"}]


Init ==   
  /\ msgs = {}
  /\ rmWorking = [rm \in RMs |-> TRUE]
  /\ rmPrepared = [rm \in RMs |-> FALSE]
  /\ rmAborted = [rm \in RMs |-> FALSE]
  /\ rmCommitted = [rm \in RMs |-> FALSE]
  /\ tmState = "init"
  /\ tmPrepared = {}

SndPrepare(rm) == 
  /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> rm]}
  /\ rmWorking[rm]
  /\ rmWorking' = [rmWorking EXCEPT![rm] = FALSE]
  /\ rmPrepared' = [rmPrepared EXCEPT![rm] = TRUE]
  /\ UNCHANGED <<tmState, tmPrepared, rmAborted, rmCommitted>>

RcvPrepare(rm) ==
  /\ [type |-> "Prepared", theRM |-> rm] \in msgs
  /\ tmState = "init"
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<msgs, tmState, rmWorking, rmPrepared, rmAborted, rmCommitted>>

SndCommit(rm) ==
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ tmState \in {"init", "commmitted"}
  /\ tmPrepared = RMs
  /\ tmState' = "committed"
  /\ UNCHANGED <<tmPrepared, rmWorking, rmPrepared, rmAborted, rmCommitted>>

RcvCommit(rm) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmPrepared' = [rmWorking EXCEPT![rm] = FALSE]
  /\ rmCommitted' = [rmPrepared EXCEPT![rm] = TRUE]
  /\ UNCHANGED <<msgs, tmState, tmPrepared, rmWorking, rmAborted>>

SndAbort(rm) ==
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ tmState \in {"init", "aborted"}
  /\ tmState' = "aborted"
  /\ UNCHANGED <<tmPrepared, rmWorking, rmPrepared, rmAborted, rmCommitted>>

RcvAbort(rm) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmWorking' = [rmWorking EXCEPT![rm] = FALSE]
  /\ rmPrepared' = [rmPrepared EXCEPT![rm] = FALSE]
  /\ rmAborted' = [rmAborted EXCEPT![rm] = TRUE]
  /\ UNCHANGED <<msgs, tmState, tmPrepared, rmCommitted>>
  
SilentAbort(rm) ==
  /\ rmWorking[rm]
  /\ rmWorking' = [rmWorking EXCEPT![rm] = FALSE]
  /\ rmAborted' = [rmAborted EXCEPT![rm] = TRUE]
  /\ UNCHANGED <<tmState, tmPrepared, msgs, rmCommitted, rmPrepared>>


Next ==
    \E rm \in RMs :
        \/ SndPrepare(rm)
        \/ RcvPrepare(rm)
        \/ SndCommit(rm)
        \/ RcvCommit(rm)
        \/ SndAbort(rm)
        \/ RcvAbort(rm)
        \/ SilentAbort(rm)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ msgs \in SUBSET Message
  /\ rmWorking \in [RMs -> BOOLEAN]
  /\ rmPrepared \in [RMs -> BOOLEAN]
  /\ rmAborted \in [RMs -> BOOLEAN]
  /\ rmCommitted \in [RMs -> BOOLEAN]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RMs

Consistent == \A rm1,rm2 \in RMs : ~(rmAborted[rm1] /\ rmCommitted[rm2])

(*
RmStateWellFormed ==
    \A rm \in RMs :
        /\ rmWorking[rm] => (~rmPrepared[rm] /\ ~rmAborted[rm] /\ ~rmCommitted[rm])
        /\ rmPrepared[rm] => (~rmWorking[rm] /\ ~rmAborted[rm] /\ ~rmCommitted[rm])
        /\ rmAborted[rm] => (~rmWorking[rm] /\ ~rmPrepared[rm] /\ ~rmCommitted[rm])
        /\ rmCommitted[rm] => (~rmWorking[rm] /\ ~rmPrepared[rm] /\ ~rmAborted[rm])
*)

IISpec == TypeOK /\ Consistent /\ [][Next]_vars

=============================================================================
