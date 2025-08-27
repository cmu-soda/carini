--------------------------- MODULE Env_hist ---------------------------
EXTENDS Naturals, Sequences, Integers, FiniteSets, TLC

CONSTANTS RMs

VARIABLES msgs, Fluent4_0, Fluent3_0, Fluent9_0, Fluent8_0, Fluent11_0, Fluent12_0

vars == <<msgs, Fluent4_0, Fluent3_0, Fluent9_0, Fluent8_0, Fluent11_0, Fluent12_0>>

CandSep ==
/\ \A var0 \in RMs : (Fluent4_0[var0]) => (Fluent3_0[var0])
/\ \A var0 \in RMs : (Fluent11_0[var0]) => (Fluent12_0[var0])
/\ \A var0 \in RMs : (Fluent8_0[var0]) => (Fluent9_0[var0])

Symmetry == Permutations(RMs)

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ Fluent4_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent3_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent11_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent9_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent8_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent12_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ Fluent12_0' = [Fluent12_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent4_0, Fluent3_0, Fluent11_0, Fluent9_0, Fluent8_0>>

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ UNCHANGED <<msgs>>
/\ Fluent11_0' = [Fluent11_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent4_0, Fluent3_0, Fluent9_0, Fluent8_0, Fluent12_0>>

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ Fluent3_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent4_0, Fluent11_0, Fluent9_0, Fluent8_0, Fluent12_0>>

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ Fluent4_0' = [Fluent4_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent3_0, Fluent11_0, Fluent9_0, Fluent8_0, Fluent12_0>>

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ Fluent9_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent4_0, Fluent3_0, Fluent11_0, Fluent8_0, Fluent12_0>>

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ Fluent8_0' = [Fluent8_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent4_0, Fluent3_0, Fluent11_0, Fluent9_0, Fluent12_0>>

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
