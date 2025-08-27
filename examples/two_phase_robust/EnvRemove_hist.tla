--------------------------- MODULE EnvRemove_hist ---------------------------
EXTENDS Naturals, Sequences, Integers, FiniteSets, TLC

CONSTANTS RMs

VARIABLES Fluent6_0, Fluent15_0, msgs, Fluent5_0, Fluent14_0, Fluent8_0, Fluent7_0

vars == <<Fluent6_0, Fluent15_0, msgs, Fluent5_0, Fluent14_0, Fluent8_0, Fluent7_0>>

CandSep ==
/\ \A var0 \in RMs : (Fluent7_0[var0]) => (Fluent8_0[var0])
/\ \A var0 \in RMs : (Fluent5_0[var0]) => (Fluent6_0[var0])
/\ \A var0 \in RMs : (Fluent14_0[var0]) => (Fluent15_0[var0])

Symmetry == Permutations(RMs)

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent15_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent5_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent14_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent8_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent7_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ Fluent8_0' = [Fluent8_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent15_0, Fluent5_0, Fluent14_0, Fluent7_0>>

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ msgs' = (msgs \ {[type |-> "Prepared",theRM |-> rm]})
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent15_0, Fluent5_0, Fluent14_0, Fluent8_0>>

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ Fluent6_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent15_0, Fluent5_0, Fluent14_0, Fluent8_0, Fluent7_0>>

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ msgs' = (msgs \ {[type |-> "Commit"]})
/\ Fluent5_0' = [Fluent5_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent15_0, Fluent14_0, Fluent8_0, Fluent7_0>>

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ Fluent15_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent14_0, Fluent8_0, Fluent7_0>>

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ msgs' = (msgs \ {[type |-> "Abort"]})
/\ Fluent14_0' = [Fluent14_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent15_0, Fluent5_0, Fluent8_0, Fluent7_0>>

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ RcvCommit(rm)
\/ SndAbort(rm)
\/ RcvAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (msgs \in SUBSET(Message))
=============================================================================
