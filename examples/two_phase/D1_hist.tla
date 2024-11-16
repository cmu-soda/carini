--------------------------- MODULE D1_hist ---------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS RMs

VARIABLES Fluent12, msgs, Fluent11, Fluent9, Fluent14, Fluent8, Fluent13, Fluent7, Fluent6, Fluent10, Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, Fluent15

vars == <<Fluent12, msgs, Fluent11, Fluent9, Fluent14, Fluent8, Fluent13, Fluent7, Fluent6, Fluent10, Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, Fluent15>>

CandSep ==
/\ \A var0 \in RMs : (Fluent6[var0]) => (Fluent7[var0])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent9[var1]) => (Fluent8[var0])
/\ \A var0 \in RMs : (Fluent10[var0]) => (Fluent11[var0])
/\ \A var0 \in RMs : (Fluent12[var0]) => (Fluent13[var0])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent14[var0]) => (Fluent15[var1])

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ Fluent12 = [ x0 \in RMs |-> FALSE]
/\ Fluent11 = [ x0 \in RMs |-> FALSE]
/\ Fluent9 = [ x0 \in RMs |-> FALSE]
/\ Fluent14 = [ x0 \in RMs |-> FALSE]
/\ Fluent8 = [ x0 \in RMs |-> FALSE]
/\ Fluent13 = [ x0 \in RMs |-> FALSE]
/\ Fluent7 = [ x0 \in RMs |-> FALSE]
/\ Fluent6 = [ x0 \in RMs |-> FALSE]
/\ Fluent10 = [ x0 \in RMs |-> FALSE]
/\ Fluent15 = [ x0 \in RMs |-> FALSE]
/\ Fluent5 = [ x0 \in RMs |-> FALSE]
/\ Fluent4 = [ x0 \in RMs |-> FALSE]
/\ Fluent3 = [ x0 \in RMs |-> FALSE]
/\ Fluent2 = [ x0 \in RMs |-> FALSE]
/\ Fluent1 = [ x0 \in RMs |-> FALSE]
/\ Fluent0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED<<Fluent12, Fluent11, Fluent9, Fluent14, Fluent8, Fluent13, Fluent7, Fluent6, Fluent10, Fluent15>>
/\ CandSep'
/\ Fluent3' = [Fluent3 EXCEPT ![rm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent5, Fluent4, Fluent2, Fluent1>>
/\ CandSep'

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ UNCHANGED <<msgs>>
/\ Fluent11' = [Fluent11 EXCEPT ![rm] = FALSE]
/\ Fluent8' = [Fluent8 EXCEPT ![rm] = TRUE]
/\ Fluent7' = [Fluent7 EXCEPT ![rm] = TRUE]
/\ Fluent15' = [Fluent15 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent12, Fluent9, Fluent14, Fluent13, Fluent6, Fluent10>>
/\ CandSep'
/\ UNCHANGED<<Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ Fluent9' = [Fluent9 EXCEPT ![rm] = TRUE]
/\ Fluent14' = [Fluent14 EXCEPT ![rm] = TRUE]
/\ Fluent13' = [Fluent13 EXCEPT ![rm] = FALSE]
/\ Fluent6' = [Fluent6 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent12, Fluent11, Fluent8, Fluent7, Fluent10, Fluent15>>
/\ CandSep'
/\ UNCHANGED<<Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED<<Fluent12, Fluent11, Fluent9, Fluent14, Fluent8, Fluent13, Fluent7, Fluent6, Fluent10, Fluent15>>
/\ CandSep'
/\ Fluent5' = [Fluent5 EXCEPT ![rm] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT ![rm] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent4, Fluent3, Fluent0>>
/\ CandSep'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ Fluent12' = [Fluent12 EXCEPT ![rm] = TRUE]
/\ Fluent11' = [Fluent11 EXCEPT ![rm] = TRUE]
/\ Fluent13' = [Fluent13 EXCEPT ![rm] = TRUE]
/\ Fluent10' = [Fluent10 EXCEPT ![rm] = TRUE]
/\ Fluent15' = [Fluent15 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent9, Fluent14, Fluent8, Fluent7, Fluent6>>
/\ CandSep'
/\ UNCHANGED<<Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED<<Fluent12, Fluent11, Fluent9, Fluent14, Fluent8, Fluent13, Fluent7, Fluent6, Fluent10, Fluent15>>
/\ CandSep'
/\ Fluent4' = [Fluent4 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent5, Fluent3, Fluent2, Fluent1, Fluent0>>
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
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent2[var0]) => (Fluent3[var1])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent4[var1]) => (~(Fluent5[var0]))
=============================================================================
