--------------------------- MODULE D1_hist ---------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS RMs

VARIABLES msgs, Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0

vars == <<msgs, Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>

CandSep ==
/\ \A var0 \in RMs : \E var1 \in RMs : (Fluent1[var0]) => (Fluent0[var1])
/\ \A var0 \in RMs : \E var1 \in RMs : (Fluent3[var0]) => (Fluent2[var1])
/\ \A var0 \in RMs : (Fluent5[var0]) => (Fluent4[var0])

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ Fluent3 = [ x0 \in RMs |-> FALSE]
/\ Fluent2 = [ x0 \in RMs |-> FALSE]
/\ Fluent1 = [ x0 \in RMs |-> FALSE]
/\ Fluent0 = [ x0 \in RMs |-> FALSE]
/\ Fluent5 = [ x0 \in RMs |-> FALSE]
/\ Fluent4 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ Fluent4' = [Fluent4 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent3, Fluent2, Fluent1, Fluent0, Fluent5>>

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ UNCHANGED <<msgs>>
/\ Fluent5' = [Fluent5 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent3, Fluent2, Fluent1, Fluent0, Fluent4>>

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ Fluent2' = [Fluent2 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent3, Fluent1, Fluent0, Fluent5, Fluent4>>

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ Fluent3' = [Fluent3 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0, Fluent5, Fluent4>>

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ Fluent0' = [Fluent0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent3, Fluent2, Fluent1, Fluent5, Fluent4>>

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ Fluent1' = [Fluent1 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent3, Fluent2, Fluent0, Fluent5, Fluent4>>

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
