------------------------------- MODULE RM ----------------------------- 

EXTENDS Sequences, Naturals, Integers, TLC

CONSTANTS RMs

VARIABLES rmState

vars == <<rmState>>

Symmetry == Permutations(RMs)

Message ==
  [type : {"Prepared"}, theRM : RMs]  \cup  [type : {"Commit", "Abort"}]


Init ==   
  /\ rmState = [rm \in RMs |-> "working"]

Prepare(rm) == 
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "prepared"]

Commit(rm) ==
  /\ rmState' = [rmState EXCEPT![rm] = "commit"]

Abort(rm) ==
  /\ rmState' = [rmState EXCEPT![rm] = "abort"]
  
SilentAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "abort"]

Next ==
    \E rm \in RMs :
        \/ Prepare(rm)
        \/ Commit(rm)
        \/ Abort(rm)
        \/ SilentAbort(rm)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ rmState \in [RMs -> {"working", "prepared", "commit", "abort"}]

Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "abort" /\ rmState[rm2] = "commit")

=============================================================================
