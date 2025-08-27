------------------------------- MODULE ToyTwoPhase ----------------------------- 

EXTENDS Sequences, Naturals, Integers, TLC

CONSTANTS RMs

VARIABLES rmState, tmState, tmPrepared

vars == <<rmState, tmState, tmPrepared>>

Symmetry == Permutations(RMs)

Message ==
  [type : {"Prepared"}, theRM : RMs]  \cup  [type : {"Commit", "Abort"}]


Init ==   
  /\ rmState = [rm \in RMs |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}

Prepare(rm) == 
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "prepared"]
  /\ tmState = "init"
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<tmState>>

Commit(rm) ==
  /\ tmState \in {"init", "commmitted"}
  /\ tmPrepared = RMs
  /\ tmState' = "commit"
  /\ rmState' = [rmState EXCEPT![rm] = "commit"]
  /\ UNCHANGED <<tmPrepared>>

Abort(rm) ==
  /\ tmState \in {"init", "abort"}
  /\ tmState' = "abort"
  /\ rmState' = [rmState EXCEPT![rm] = "abort"]
  /\ UNCHANGED <<tmPrepared>>
  
SilentAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "abort"]
  /\ UNCHANGED <<tmState, tmPrepared>>


Next ==
    \E rm \in RMs :
        \/ Prepare(rm)
        \/ Commit(rm)
        \/ Abort(rm)
        \/ SilentAbort(rm)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ rmState \in [RMs -> {"working", "prepared", "commit", "abort"}]
  /\ tmState \in {"init", "commit", "abort"}
  /\ tmPrepared \in SUBSET RMs

Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "abort" /\ rmState[rm2] = "commit")

=============================================================================
