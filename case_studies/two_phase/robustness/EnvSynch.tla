------------------------------- MODULE EnvSynch ----------------------------- 

EXTENDS Sequences, Naturals, Integers, TLC

CONSTANTS RMs

VARIABLES msgs, deliver

vars == <<msgs, deliver>>

Symmetry == Permutations(RMs)

Message ==
  [type : {"Prepared"}, theRM : RMs]  \cup  [type : {"Commit", "Abort"}]


Init ==
  /\ msgs = {}
  /\ deliver = FALSE

SndPrepare(rm) == 
  /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> rm]}
  /\ deliver = FALSE
  /\ deliver' = TRUE

RcvPrepare(rm) ==
  /\ [type |-> "Prepared", theRM |-> rm] \in msgs
  /\ msgs' = {}
  /\ deliver = TRUE
  /\ deliver' = FALSE

SndCommit(rm) ==
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ deliver = FALSE
  /\ deliver' = TRUE

RcvCommit(rm) ==
  /\ [type |-> "Commit"] \in msgs
  /\ msgs' = {}
  /\ deliver = TRUE
  /\ deliver' = FALSE

SndAbort(rm) ==
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ deliver = FALSE
  /\ deliver' = TRUE

RcvAbort(rm) ==
  /\ [type |-> "Abort"] \in msgs
  /\ msgs' = {}
  /\ deliver = TRUE
  /\ deliver' = FALSE

Next ==
    \E rm \in RMs :
        \/ SndPrepare(rm)
        \/ RcvPrepare(rm)
        \/ SndCommit(rm)
        \/ RcvCommit(rm)
        \/ SndAbort(rm)
        \/ RcvAbort(rm)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ msgs \in SUBSET Message

=============================================================================
