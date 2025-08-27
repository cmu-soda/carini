--------------------------- MODULE EnvSynch_hist ---------------------------
EXTENDS Naturals, Sequences, Integers, FiniteSets, TLC

CONSTANTS RMs

VARIABLES Fluent6_0, msgs, Fluent5_0, Fluent4_0, Fluent3_0, deliver, Fluent13_0, Fluent12_0

vars == <<Fluent6_0, msgs, Fluent5_0, Fluent4_0, Fluent3_0, deliver, Fluent13_0, Fluent12_0>>

CandSep ==
/\ \A var0 \in RMs : (Fluent4_0[var0]) => (Fluent3_0[var0])
/\ \A var0 \in RMs : (Fluent12_0[var0]) => (Fluent13_0[var0])
/\ \A var0 \in RMs : (Fluent6_0[var0]) => (Fluent5_0[var0])

Symmetry == Permutations(RMs)

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ deliver = FALSE
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent5_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent4_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent3_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent13_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent12_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ deliver = FALSE
/\ deliver' = TRUE
/\ Fluent5_0' = [Fluent5_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent4_0, Fluent3_0, Fluent13_0, Fluent12_0>>

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ msgs' = {}
/\ deliver = TRUE
/\ deliver' = FALSE
/\ Fluent6_0' = [Fluent6_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent5_0, Fluent4_0, Fluent3_0, Fluent13_0, Fluent12_0>>

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ deliver = FALSE
/\ deliver' = TRUE
/\ Fluent3_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent4_0, Fluent13_0, Fluent12_0>>

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ msgs' = {}
/\ deliver = TRUE
/\ deliver' = FALSE
/\ Fluent4_0' = [Fluent4_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent3_0, Fluent13_0, Fluent12_0>>

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ deliver = FALSE
/\ deliver' = TRUE
/\ Fluent13_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent4_0, Fluent3_0, Fluent12_0>>

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ msgs' = {}
/\ deliver = TRUE
/\ deliver' = FALSE
/\ Fluent12_0' = [Fluent12_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent4_0, Fluent3_0, Fluent13_0>>

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
