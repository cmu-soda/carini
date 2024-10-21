--------------------------- MODULE D1_hist ---------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS RMs

VARIABLES msgs, Fluent11, Fluent9, Fluent8, Fluent7, Fluent6, Fluent10, Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0

vars == <<msgs, Fluent11, Fluent9, Fluent8, Fluent7, Fluent6, Fluent10, Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>

CandSep ==
/\ \A var0 \in RMs : (Fluent7[var0]) => (Fluent6[var0])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent8[var0]) => (Fluent9[var1])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent10[var1]) => (Fluent11[var0])

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ Fluent11 = [ x0 \in RMs |-> TRUE]
/\ Fluent9 = [ x0 \in RMs |-> FALSE]
/\ Fluent8 = [ x0 \in RMs |-> FALSE]
/\ Fluent7 = [ x0 \in RMs |-> TRUE]
/\ Fluent6 = [ x0 \in RMs |-> TRUE]
/\ Fluent10 = [ x0 \in RMs |-> FALSE]
/\ Fluent5 = [ x0 \in RMs |-> FALSE]
/\ Fluent4 = [ x0 \in RMs |-> FALSE]
/\ Fluent3 = [ x0 \in RMs |-> FALSE]
/\ Fluent2 = [ x0 \in RMs |-> TRUE]
/\ Fluent1 = [ x0 \in RMs |-> TRUE]
/\ Fluent0 = [ x0 \in RMs |-> TRUE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED<<Fluent11, Fluent9, Fluent8, Fluent7, Fluent6, Fluent10>>
/\ CandSep'
/\ Fluent5' = [Fluent5 EXCEPT ![rm] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent4, Fluent3, Fluent2, Fluent0>>
/\ CandSep'

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ UNCHANGED <<msgs>>
/\ Fluent9' = [Fluent9 EXCEPT ![rm] = TRUE]
/\ Fluent7' = [Fluent7 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent11, Fluent8, Fluent6, Fluent10>>
/\ CandSep'
/\ UNCHANGED<<Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ Fluent11' = [Fluent11 EXCEPT ![rm] = FALSE]
/\ Fluent8' = [Fluent8 EXCEPT ![rm] = TRUE]
/\ Fluent6' = [Fluent6 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent9, Fluent7, Fluent10>>
/\ CandSep'
/\ UNCHANGED<<Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED<<Fluent11, Fluent9, Fluent8, Fluent7, Fluent6, Fluent10>>
/\ CandSep'
/\ Fluent4' = [Fluent4 EXCEPT ![rm] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT ![rm] = FALSE]
/\ Fluent0' = [Fluent0 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent5, Fluent3, Fluent1>>
/\ CandSep'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ Fluent10' = [Fluent10 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent9, Fluent8, Fluent7, Fluent6>>
/\ CandSep'
/\ UNCHANGED<<Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED<<Fluent11, Fluent9, Fluent8, Fluent7, Fluent6, Fluent10>>
/\ CandSep'
/\ Fluent3' = [Fluent3 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent5, Fluent4, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

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

Safety ==
/\ \A var0 \in RMs : (Fluent1[var0]) => (Fluent0[var0])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent3[var1]) => (Fluent2[var0])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent4[var1]) => (Fluent5[var0])
=============================================================================
