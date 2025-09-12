--------------------------- MODULE E1 ---------------------------
EXTENDS Naturals, Sequences, Integers, TLC, Randomization

CONSTANTS RMs

VARIABLES tmState, Fluent9, Fluent8, tmPrepared, Fluent10

vars == <<tmState, Fluent9, Fluent8, tmPrepared, Fluent10>>

NextUnchanged == UNCHANGED vars
Symmetry == Permutations(RMs)

CandSep ==
TRUE

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent9 = [ x0 \in RMs |-> FALSE]
/\ Fluent8 = [ x0 \in RMs |-> FALSE]
/\ Fluent10 = [ x0 \in RMs |-> FALSE]

RcvPrepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<tmState>>
/\ UNCHANGED<<>>
/\ CandSep'
/\ Fluent8' = [Fluent8 EXCEPT![rm] = TRUE]
/\ UNCHANGED<<Fluent9, Fluent10>>
/\ CandSep'

SndCommit(rm) ==
/\ (tmState \in {"init","commmitted"})
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED<<>>
/\ CandSep'
/\ Fluent9' = [Fluent9 EXCEPT![rm] = TRUE]
/\ UNCHANGED<<Fluent8, Fluent10>>
/\ CandSep'

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED<<>>
/\ CandSep'
/\ Fluent10' = [Fluent10 EXCEPT![rm] = TRUE]
/\ UNCHANGED<<Fluent9, Fluent8>>
/\ CandSep'

Next ==
\E rm \in RMs :
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ SndAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
/\ Fluent9  \in [RMs -> BOOLEAN]
/\ Fluent8  \in [RMs -> BOOLEAN]
/\ Fluent10 \in [RMs -> BOOLEAN]

Safety ==
/\ \A var0 \in RMs : (\E var1 \in RMs : Fluent9[var1]) => (Fluent8[var0])
/\ \A var0 \in RMs : (Fluent10[var0]) => (\A var1 \in RMs : ~Fluent9[var1])
=============================================================================
