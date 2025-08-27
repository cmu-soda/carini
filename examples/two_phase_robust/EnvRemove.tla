------------------------------- MODULE EnvRemove ----------------------------- 

EXTENDS Sequences, Naturals, Integers, TLC

CONSTANTS RMs

VARIABLES msgs

vars == <<msgs>>

Symmetry == Permutations(RMs)

Message ==
  [type : {"Prepared"}, theRM : RMs]  \cup  [type : {"Commit", "Abort"}]


Init ==   
  /\ msgs = {}

SndPrepare(rm) == 
  /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> rm]}

RcvPrepare(rm) ==
  /\ [type |-> "Prepared", theRM |-> rm] \in msgs
  /\ msgs' = msgs \ {[type |-> "Prepared", theRM |-> rm]}

SndCommit(rm) ==
  /\ msgs' = msgs \cup {[type |-> "Commit"]}

RcvCommit(rm) ==
  /\ [type |-> "Commit"] \in msgs
  /\ msgs' = msgs \ {[type |-> "Commit"]}

SndAbort(rm) ==
  /\ msgs' = msgs \cup {[type |-> "Abort"]}

RcvAbort(rm) ==
  /\ [type |-> "Abort"] \in msgs
  /\ msgs' = msgs \ {[type |-> "Abort"]}

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
