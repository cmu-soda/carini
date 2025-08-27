--------------------------- MODULE D0_hist ---------------------------
EXTENDS Naturals, Sequences, Integers, FiniteSets, TLC

CONSTANTS RMs

VARIABLES Fluent6_0, Fluent5_0, Fluent9_0, Fluent8_0, rmState

vars == <<Fluent6_0, Fluent5_0, Fluent9_0, Fluent8_0, rmState>>

CandSep ==
/\ \A var0 \in RMs : (Fluent5_0[var0]) => (~(Fluent6_0[var0]))
/\ \A var0 \in RMs : (Fluent9_0[var0]) => (Fluent8_0[var0])

Symmetry == Permutations(RMs)

Message == ([type |-> {"Prepared"},theRM |-> RMs] \cup [type |-> {"Commit","Abort"}])

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent5_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent9_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent8_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ Fluent8_0' = [Fluent8_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent9_0>>
/\ CandSep'

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ Fluent5_0' = [Fluent5_0 EXCEPT ![rm] = TRUE]
/\ Fluent9_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent8_0>>
/\ CandSep'

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ Fluent6_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent5_0, Fluent9_0, Fluent8_0>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent9_0, Fluent8_0>>
/\ CandSep'

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
