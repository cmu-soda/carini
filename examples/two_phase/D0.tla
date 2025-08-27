--------------------------- MODULE D0 ---------------------------
EXTENDS Naturals, Sequences, Integers, TLC

CONSTANTS RMs

VARIABLES rmState

vars == <<rmState>>

Symmetry == Permutations(RMs)

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ rmState = [rm \in RMs |-> "working"]

SndPrepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvCommit(rm)
\/ RcvAbort(rm)
\/ SilentAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))
=============================================================================
