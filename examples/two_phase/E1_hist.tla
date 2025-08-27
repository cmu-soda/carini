--------------------------- MODULE E1_hist ---------------------------
EXTENDS Naturals, Sequences, Integers, FiniteSets, TLC

CONSTANTS RMs

VARIABLES Fluent15_0, Fluent6_0, Fluent14_0, Fluent5_0, tmState, Fluent9_0, tmPrepared, Fluent8_0, Fluent24_0, Fluent23_0

vars == <<Fluent15_0, Fluent6_0, Fluent14_0, Fluent5_0, tmState, Fluent9_0, tmPrepared, Fluent8_0, Fluent24_0, Fluent23_0>>

CandSep ==
/\ \A var0 \in RMs : (Fluent24_0[var0]) => (~(Fluent23_0[var0]))
/\ \A var0 \in RMs : (Fluent14_0[var0]) => (Fluent15_0[var0])

Message == ([type |-> {"Prepared"},theRM |-> RMs] \cup [type |-> {"Commit","Abort"}])

Symmetry == Permutations(RMs)

Init ==
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent15_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent14_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent24_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent23_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent5_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent9_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent8_0 = [ x0 \in RMs |-> FALSE]

RcvPrepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<tmState>>
/\ Fluent15_0' = [Fluent15_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent14_0, Fluent24_0, Fluent23_0>>
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent9_0, Fluent8_0>>

SndCommit(rm) ==
/\ (tmState \in {"init","commmitted"})
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared>>
/\ Fluent14_0' = [x0 \in RMs |-> TRUE]
/\ Fluent24_0' = [Fluent24_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent15_0, Fluent23_0>>
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent9_0, Fluent8_0>>

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared>>
/\ Fluent23_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent15_0, Fluent14_0, Fluent24_0>>
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent9_0, Fluent8_0>>

Next ==
\E rm \in RMs :
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ SndAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
=============================================================================
