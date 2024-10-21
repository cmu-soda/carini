--------------------------- MODULE E1_hist ---------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS RMs

VARIABLES Fluent11, tmState, Fluent9, Fluent8, Fluent7, Fluent6, tmPrepared, Fluent10

vars == <<Fluent11, tmState, Fluent9, Fluent8, Fluent7, Fluent6, tmPrepared, Fluent10>>

CandSep ==
TRUE

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent11 = [ x0 \in RMs |-> TRUE]
/\ Fluent9 = [ x0 \in RMs |-> FALSE]
/\ Fluent8 = [ x0 \in RMs |-> FALSE]
/\ Fluent7 = [ x0 \in RMs |-> TRUE]
/\ Fluent6 = [ x0 \in RMs |-> TRUE]
/\ Fluent10 = [ x0 \in RMs |-> FALSE]

RcvPrepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<tmState>>
/\ UNCHANGED<<>>
/\ CandSep'
/\ Fluent9' = [Fluent9 EXCEPT ![rm] = TRUE]
/\ Fluent7' = [Fluent7 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent11, Fluent8, Fluent6, Fluent10>>
/\ CandSep'

SndCommit(rm) ==
/\ (tmState \in {"init","commmitted"})
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED<<>>
/\ CandSep'
/\ Fluent11' = [Fluent11 EXCEPT ![rm] = FALSE]
/\ Fluent8' = [Fluent8 EXCEPT ![rm] = TRUE]
/\ Fluent6' = [Fluent6 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent9, Fluent7, Fluent10>>
/\ CandSep'

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED<<>>
/\ CandSep'
/\ Fluent10' = [Fluent10 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent9, Fluent8, Fluent7, Fluent6>>
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

Safety ==
/\ \A var0 \in RMs : (Fluent7[var0]) => (Fluent6[var0])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent8[var0]) => (Fluent9[var1])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent10[var1]) => (Fluent11[var0])
=============================================================================
