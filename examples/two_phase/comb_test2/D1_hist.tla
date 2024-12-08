--------------------------- MODULE D1_hist ---------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS RMs

VARIABLES msgs, Fluent11, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, tmPrepared

vars == <<msgs, Fluent11, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, tmPrepared>>

CandSep ==
/\ \A var0 \in RMs : (Fluent0[var0]) => (Fluent1[var0])
/\ \A var0 \in RMs : (Fluent2[var0]) => (Fluent3[var0])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent4[var0]) => (Fluent5[var1])
/\ \A var0 \in RMs : (Fluent7[var0]) => (Fluent6[var0])
/\ \A var0 \in RMs : \E var1 \in RMs : (Fluent9[var0]) => (Fluent8[var1])
/\ \A var0 \in RMs : \E var1 \in RMs : (Fluent11[var0]) => (Fluent10[var1])

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ tmPrepared = {}
/\ Fluent11 = [ x0 \in RMs |-> FALSE]
/\ Fluent9 = [ x0 \in RMs |-> FALSE]
/\ Fluent8 = [ x0 \in RMs |-> FALSE]
/\ Fluent7 = [ x0 \in RMs |-> FALSE]
/\ Fluent6 = [ x0 \in RMs |-> FALSE]
/\ Fluent5 = [ x0 \in RMs |-> FALSE]
/\ Fluent10 = [ x0 \in RMs |-> FALSE]
/\ Fluent4 = [ x0 \in RMs |-> FALSE]
/\ Fluent3 = [ x0 \in RMs |-> FALSE]
/\ Fluent2 = [ x0 \in RMs |-> FALSE]
/\ Fluent1 = [ x0 \in RMs |-> FALSE]
/\ Fluent0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED <<tmPrepared>>
/\ Fluent6' = [Fluent6 EXCEPT ![rm] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent9, Fluent8, Fluent7, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent0>>

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs>>
/\ Fluent7' = [Fluent7 EXCEPT ![rm] = TRUE]
/\ Fluent5' = [Fluent5 EXCEPT ![rm] = TRUE]
/\ Fluent3' = [Fluent3 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent9, Fluent8, Fluent6, Fluent10, Fluent4, Fluent2, Fluent1, Fluent0>>

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ tmPrepared = RMs
/\ UNCHANGED <<tmPrepared>>
/\ Fluent10' = [Fluent10 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED <<tmPrepared>>
/\ Fluent11' = [Fluent11 EXCEPT ![rm] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT ![rm] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT ![rm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent3, Fluent1>>

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ UNCHANGED <<tmPrepared>>
/\ Fluent8' = [Fluent8 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent9, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED <<tmPrepared>>
/\ Fluent9' = [Fluent9 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>

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
/\ (tmPrepared \in SUBSET(RMs))
=============================================================================
