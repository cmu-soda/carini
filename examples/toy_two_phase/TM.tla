------------------------------- MODULE TM ----------------------------- 

EXTENDS Sequences, Naturals, Integers, TLC

CONSTANTS RMs

VARIABLES tmState, tmPrepared

vars == <<tmState, tmPrepared>>

Symmetry == Permutations(RMs)

Message ==
  [type : {"Prepared"}, theRM : RMs]  \cup  [type : {"Commit", "Abort"}]


Init ==   
  /\ tmState = "init"
  /\ tmPrepared = {}

Prepare(rm) == 
  /\ tmState = "init"
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<tmState>>

Commit(rm) ==
  /\ tmState \in {"init", "commmitted"}
  /\ tmPrepared = RMs
  /\ tmState' = "commit"
  /\ UNCHANGED <<tmPrepared>>

Abort(rm) ==
  /\ tmState \in {"init", "abort"}
  /\ tmState' = "abort"
  /\ UNCHANGED <<tmPrepared>>

Next ==
    \E rm \in RMs :
        \/ Prepare(rm)
        \/ Commit(rm)
        \/ Abort(rm)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ tmState \in {"init", "commit", "abort"}
  /\ tmPrepared \in SUBSET RMs

=============================================================================
