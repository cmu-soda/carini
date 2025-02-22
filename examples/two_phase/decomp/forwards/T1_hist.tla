--------------------------- MODULE T1_hist ---------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS RMs

VARIABLES Fluent12, Fluent11, tmState, Fluent14, Fluent13, Fluent10, tmPrepared, rmState, Fluent27, Fluent26, Fluent23, msgs, Fluent22, Fluent9, Fluent25, Fluent8, Fluent24, Fluent7, Fluent6, Fluent5, Fluent21, Fluent4, Fluent20, Fluent3, Fluent2, Fluent1, Fluent0, Fluent19, Fluent16, Fluent15, Fluent18, Fluent17

vars == <<Fluent12, Fluent11, tmState, Fluent14, Fluent13, Fluent10, tmPrepared, rmState, Fluent27, Fluent26, Fluent23, msgs, Fluent22, Fluent9, Fluent25, Fluent8, Fluent24, Fluent7, Fluent6, Fluent5, Fluent21, Fluent4, Fluent20, Fluent3, Fluent2, Fluent1, Fluent0, Fluent19, Fluent16, Fluent15, Fluent18, Fluent17>>

CandSep ==
/\ \A var0 \in RMs : (Fluent0[var0]) => (Fluent1[var0])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent2[var1]) => (Fluent3[var0])
/\ \A var0 \in RMs : (Fluent5[var0]) => (Fluent4[var0])
/\ \A var0 \in RMs : (Fluent7[var0]) => (Fluent6[var0])
/\ \A var0 \in RMs : (Fluent9[var0]) => (Fluent8[var0])
/\ \A var0 \in RMs : (Fluent11[var0]) => (Fluent10[var0])
/\ \A var0 \in RMs : \E var1 \in RMs : (Fluent12[var0]) => (Fluent13[var1])
/\ \A var0 \in RMs : (Fluent15[var0]) => (Fluent14[var0])
/\ \A var0 \in RMs : (Fluent17[var0]) => (Fluent16[var0])
/\ \A var0 \in RMs : (Fluent19[var0]) => (Fluent18[var0])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent21[var0]) => (Fluent20[var1])
/\ \A var0 \in RMs : (Fluent23[var0]) => (Fluent22[var0])
/\ \A var0 \in RMs : (Fluent25[var0]) => (Fluent24[var0])
/\ \A var0 \in RMs : (Fluent27[var0]) => (Fluent26[var0])

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ rmState = [rm \in RMs |-> "working"]
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent12 = [ x0 \in RMs |-> FALSE]
/\ Fluent11 = [ x0 \in RMs |-> FALSE]
/\ Fluent14 = [ x0 \in RMs |-> FALSE]
/\ Fluent13 = [ x0 \in RMs |-> FALSE]
/\ Fluent10 = [ x0 \in RMs |-> FALSE]
/\ Fluent27 = [ x0 \in RMs |-> FALSE]
/\ Fluent26 = [ x0 \in RMs |-> FALSE]
/\ Fluent23 = [ x0 \in RMs |-> FALSE]
/\ Fluent22 = [ x0 \in RMs |-> FALSE]
/\ Fluent9 = [ x0 \in RMs |-> FALSE]
/\ Fluent25 = [ x0 \in RMs |-> FALSE]
/\ Fluent8 = [ x0 \in RMs |-> FALSE]
/\ Fluent24 = [ x0 \in RMs |-> FALSE]
/\ Fluent7 = [ x0 \in RMs |-> FALSE]
/\ Fluent6 = [ x0 \in RMs |-> FALSE]
/\ Fluent5 = [ x0 \in RMs |-> FALSE]
/\ Fluent21 = [ x0 \in RMs |-> FALSE]
/\ Fluent4 = [ x0 \in RMs |-> FALSE]
/\ Fluent20 = [ x0 \in RMs |-> FALSE]
/\ Fluent3 = [ x0 \in RMs |-> FALSE]
/\ Fluent2 = [ x0 \in RMs |-> FALSE]
/\ Fluent1 = [ x0 \in RMs |-> FALSE]
/\ Fluent0 = [ x0 \in RMs |-> FALSE]
/\ Fluent19 = [ x0 \in RMs |-> FALSE]
/\ Fluent16 = [ x0 \in RMs |-> FALSE]
/\ Fluent15 = [ x0 \in RMs |-> FALSE]
/\ Fluent18 = [ x0 \in RMs |-> FALSE]
/\ Fluent17 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ Fluent11' = [Fluent11 EXCEPT ![rm] = TRUE]
/\ Fluent10' = [Fluent10 EXCEPT ![rm] = TRUE]
/\ Fluent26' = [Fluent26 EXCEPT ![rm] = FALSE]
/\ Fluent9' = [Fluent9 EXCEPT ![rm] = TRUE]
/\ Fluent8' = [Fluent8 EXCEPT ![rm] = TRUE]
/\ Fluent5' = [Fluent5 EXCEPT ![rm] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT ![rm] = TRUE]
/\ Fluent20' = [Fluent20 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent12, Fluent14, Fluent13, Fluent27, Fluent23, Fluent22, Fluent25, Fluent24, Fluent7, Fluent6, Fluent21, Fluent3, Fluent2, Fluent1, Fluent0, Fluent19, Fluent16, Fluent15, Fluent18, Fluent17>>

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs,tmState,rmState>>
/\ Fluent11' = [Fluent11 EXCEPT ![rm] = TRUE]
/\ Fluent27' = [Fluent27 EXCEPT ![rm] = TRUE]
/\ Fluent26' = [Fluent26 EXCEPT ![rm] = TRUE]
/\ Fluent24' = [Fluent24 EXCEPT ![rm] = FALSE]
/\ Fluent7' = [Fluent7 EXCEPT ![rm] = TRUE]
/\ Fluent6' = [Fluent6 EXCEPT ![rm] = TRUE]
/\ Fluent3' = [Fluent3 EXCEPT ![rm] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT ![rm] = FALSE]
/\ Fluent1' = [Fluent1 EXCEPT ![rm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![rm] = FALSE]
/\ Fluent18' = [Fluent18 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent12, Fluent14, Fluent13, Fluent10, Fluent23, Fluent22, Fluent9, Fluent25, Fluent8, Fluent5, Fluent21, Fluent4, Fluent20, Fluent19, Fluent16, Fluent15, Fluent17>>

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ (tmState \in {"init","commmitted"})
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ Fluent12' = [Fluent12 EXCEPT ![rm] = FALSE]
/\ Fluent14' = [Fluent14 EXCEPT ![rm] = TRUE]
/\ Fluent13' = [Fluent13 EXCEPT ![rm] = TRUE]
/\ Fluent22' = [Fluent22 EXCEPT ![rm] = FALSE]
/\ Fluent21' = [Fluent21 EXCEPT ![rm] = TRUE]
/\ Fluent19' = [Fluent19 EXCEPT ![rm] = TRUE]
/\ Fluent15' = [Fluent15 EXCEPT ![rm] = TRUE]
/\ Fluent18' = [Fluent18 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent10, Fluent27, Fluent26, Fluent23, Fluent9, Fluent25, Fluent8, Fluent24, Fluent7, Fluent6, Fluent5, Fluent4, Fluent20, Fluent3, Fluent2, Fluent1, Fluent0, Fluent16, Fluent17>>

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ Fluent12' = [Fluent12 EXCEPT ![rm] = TRUE]
/\ Fluent9' = [Fluent9 EXCEPT ![rm] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT ![rm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![rm] = TRUE]
/\ Fluent16' = [Fluent16 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent11, Fluent14, Fluent13, Fluent10, Fluent27, Fluent26, Fluent23, Fluent22, Fluent25, Fluent8, Fluent24, Fluent7, Fluent6, Fluent5, Fluent21, Fluent4, Fluent20, Fluent3, Fluent1, Fluent19, Fluent15, Fluent18, Fluent17>>

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ Fluent14' = [Fluent14 EXCEPT ![rm] = FALSE]
/\ Fluent23' = [Fluent23 EXCEPT ![rm] = TRUE]
/\ Fluent22' = [Fluent22 EXCEPT ![rm] = TRUE]
/\ Fluent25' = [Fluent25 EXCEPT ![rm] = TRUE]
/\ Fluent24' = [Fluent24 EXCEPT ![rm] = TRUE]
/\ Fluent20' = [Fluent20 EXCEPT ![rm] = FALSE]
/\ Fluent16' = [Fluent16 EXCEPT ![rm] = TRUE]
/\ Fluent17' = [Fluent17 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent12, Fluent11, Fluent13, Fluent10, Fluent27, Fluent26, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent21, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, Fluent19, Fluent15, Fluent18>>

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ UNCHANGED<<Fluent12, Fluent11, Fluent14, Fluent13, Fluent10, Fluent27, Fluent26, Fluent23, Fluent22, Fluent9, Fluent25, Fluent8, Fluent24, Fluent7, Fluent6, Fluent5, Fluent21, Fluent4, Fluent20, Fluent3, Fluent2, Fluent1, Fluent0, Fluent19, Fluent16, Fluent15, Fluent18, Fluent17>>

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<tmState,tmPrepared,msgs>>
/\ Fluent6' = [Fluent6 EXCEPT ![rm] = FALSE]
/\ Fluent4' = [Fluent4 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent12, Fluent11, Fluent14, Fluent13, Fluent10, Fluent27, Fluent26, Fluent23, Fluent22, Fluent9, Fluent25, Fluent8, Fluent24, Fluent7, Fluent5, Fluent21, Fluent20, Fluent3, Fluent2, Fluent1, Fluent0, Fluent19, Fluent16, Fluent15, Fluent18, Fluent17>>

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ RcvCommit(rm)
\/ SndAbort(rm)
\/ RcvAbort(rm)
\/ SilentAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (msgs \in SUBSET(Message))
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
=============================================================================
