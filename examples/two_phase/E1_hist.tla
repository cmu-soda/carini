--------------------------- MODULE E1_hist ---------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS RMs

VARIABLES Fluent12, Fluent11, tmState, Fluent9, Fluent14, Fluent8, Fluent13, Fluent7, Fluent6, tmPrepared, Fluent10, Fluent15

vars == <<Fluent12, Fluent11, tmState, Fluent9, Fluent14, Fluent8, Fluent13, Fluent7, Fluent6, tmPrepared, Fluent10, Fluent15>>

CandSep ==
TRUE

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent12 = [ x0 \in RMs |-> FALSE]
/\ Fluent11 = [ x0 \in RMs |-> TRUE]
/\ Fluent9 = [ x0 \in RMs |-> FALSE]
/\ Fluent14 = [ x0 \in RMs |-> TRUE]
/\ Fluent8 = [ x0 \in RMs |-> FALSE]
/\ Fluent13 = [ x0 \in RMs |-> TRUE]
/\ Fluent7 = [ x0 \in RMs |-> FALSE]
/\ Fluent6 = [ x0 \in RMs |-> FALSE]
/\ Fluent10 = [ x0 \in RMs |-> FALSE]
/\ Fluent15 = [ x0 \in RMs |-> FALSE]

RcvPrepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<tmState>>
/\ UNCHANGED<<>>
/\ CandSep'
/\ Fluent8' = [Fluent8 EXCEPT ![rm] = TRUE]
/\ Fluent6' = [Fluent6 EXCEPT ![rm] = TRUE]
/\ Fluent10' = [Fluent10 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent12, Fluent11, Fluent9, Fluent14, Fluent13, Fluent7, Fluent15>>
/\ CandSep'

SndCommit(rm) ==
/\ (tmState \in {"init","commmitted"})
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED<<>>
/\ CandSep'
/\ Fluent12' = [Fluent12 EXCEPT ![rm] = TRUE]
/\ Fluent9' = [Fluent9 EXCEPT ![rm] = TRUE]
/\ Fluent14' = [Fluent14 EXCEPT ![rm] = FALSE]
/\ Fluent7' = [Fluent7 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent8, Fluent13, Fluent6, Fluent10, Fluent15>>
/\ CandSep'

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED<<>>
/\ CandSep'
/\ Fluent11' = [Fluent11 EXCEPT ![rm] = FALSE]
/\ Fluent13' = [Fluent13 EXCEPT ![rm] = FALSE]
/\ Fluent10' = [Fluent10 EXCEPT ![rm] = FALSE]
/\ Fluent15' = [Fluent15 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent12, Fluent9, Fluent14, Fluent8, Fluent7, Fluent6>>
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
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent9[var1]) => (Fluent8[var0])
/\ \A var0 \in RMs : (Fluent10[var0]) => (Fluent11[var0])
/\ \A var0 \in RMs : (Fluent12[var0]) => (Fluent13[var0])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent15[var0]) => (Fluent14[var1])
=============================================================================
