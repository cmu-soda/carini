--------------------------- MODULE T1_hist ---------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS RMs

VARIABLES Fluent12, Fluent34, Fluent11, Fluent33, tmState, Fluent14, Fluent36, Fluent13, Fluent35, Fluent30, Fluent10, Fluent32, Fluent31, rmWorking, rmAborted, tmPrepared, Fluent27, Fluent26, Fluent29, Fluent28, Fluent23, msgs, Fluent22, Fluent9, Fluent25, Fluent8, Fluent24, Fluent7, Fluent6, Fluent5, Fluent21, Fluent4, Fluent20, Fluent3, Fluent2, Fluent1, Fluent0, rmCommitted, rmPrepared, Fluent19, Fluent16, Fluent15, Fluent37, Fluent18, Fluent17

vars == <<Fluent12, Fluent34, Fluent11, Fluent33, tmState, Fluent14, Fluent36, Fluent13, Fluent35, Fluent30, Fluent10, Fluent32, Fluent31, rmWorking, rmAborted, tmPrepared, Fluent27, Fluent26, Fluent29, Fluent28, Fluent23, msgs, Fluent22, Fluent9, Fluent25, Fluent8, Fluent24, Fluent7, Fluent6, Fluent5, Fluent21, Fluent4, Fluent20, Fluent3, Fluent2, Fluent1, Fluent0, rmCommitted, rmPrepared, Fluent19, Fluent16, Fluent15, Fluent37, Fluent18, Fluent17>>

CandSep ==
/\ \A var0 \in RMs : (Fluent1[var0]) => (Fluent0[var0])
/\ \A var0 \in RMs : (Fluent3[var0]) => (Fluent2[var0])
/\ \A var0 \in RMs : (Fluent4[var0]) => (Fluent5[var0])
/\ \A var0 \in RMs : (Fluent7[var0]) => (Fluent6[var0])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent9[var0]) => (Fluent8[var1])
/\ \A var0 \in RMs : (Fluent10[var0]) => (Fluent11[var0])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent13[var1]) => (Fluent12[var0])
/\ \A var0 \in RMs : \E var1 \in RMs : (Fluent15[var0]) => (Fluent14[var1])
/\ \A var0 \in RMs : (Fluent17[var0]) => (Fluent16[var0])
/\ \A var0 \in RMs : (Fluent18[var0]) => (Fluent19[var0])
/\ \A var0 \in RMs : (Fluent20[var0]) => (Fluent21[var0])
/\ \A var0 \in RMs : \E var1 \in RMs : (Fluent22[var0]) => (Fluent23[var1])
/\ \A var0 \in RMs : (Fluent24[var0]) => (Fluent25[var0])
/\ \A var0 \in RMs : (Fluent27[var0]) => (Fluent26[var0])
/\ \A var0 \in RMs : (Fluent28[var0]) => (Fluent29[var0])
/\ \A var0 \in RMs : (Fluent30[var0]) => (Fluent31[var0])
/\ \A var0 \in RMs : (Fluent33[var0]) => (Fluent32[var0])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent35[var1]) => (Fluent34[var0])
/\ \A var0 \in RMs : (Fluent36[var0]) => (Fluent37[var0])

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ rmWorking = [rm \in RMs |-> TRUE]
/\ rmPrepared = [rm \in RMs |-> FALSE]
/\ rmAborted = [rm \in RMs |-> FALSE]
/\ rmCommitted = [rm \in RMs |-> FALSE]
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent12 = [ x0 \in RMs |-> FALSE]
/\ Fluent34 = [ x0 \in RMs |-> FALSE]
/\ Fluent11 = [ x0 \in RMs |-> FALSE]
/\ Fluent33 = [ x0 \in RMs |-> FALSE]
/\ Fluent14 = [ x0 \in RMs |-> FALSE]
/\ Fluent36 = [ x0 \in RMs |-> FALSE]
/\ Fluent13 = [ x0 \in RMs |-> FALSE]
/\ Fluent35 = [ x0 \in RMs |-> FALSE]
/\ Fluent30 = [ x0 \in RMs |-> FALSE]
/\ Fluent10 = [ x0 \in RMs |-> FALSE]
/\ Fluent32 = [ x0 \in RMs |-> FALSE]
/\ Fluent31 = [ x0 \in RMs |-> FALSE]
/\ Fluent27 = [ x0 \in RMs |-> FALSE]
/\ Fluent26 = [ x0 \in RMs |-> FALSE]
/\ Fluent29 = [ x0 \in RMs |-> FALSE]
/\ Fluent28 = [ x0 \in RMs |-> FALSE]
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
/\ Fluent37 = [ x0 \in RMs |-> FALSE]
/\ Fluent18 = [ x0 \in RMs |-> FALSE]
/\ Fluent17 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ rmWorking[rm]
/\ rmWorking' = [rmWorking EXCEPT![rm] = FALSE]
/\ rmPrepared' = [rmPrepared EXCEPT![rm] = TRUE]
/\ UNCHANGED <<tmState,tmPrepared,rmAborted,rmCommitted>>
/\ Fluent9' = [Fluent9 EXCEPT ![rm] = FALSE]
/\ Fluent8' = [Fluent8 EXCEPT ![rm] = TRUE]
/\ Fluent6' = [Fluent6 EXCEPT ![rm] = TRUE]
/\ Fluent3' = [Fluent3 EXCEPT ![rm] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT ![rm] = TRUE]
/\ Fluent16' = [Fluent16 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent12, Fluent34, Fluent11, Fluent33, Fluent14, Fluent36, Fluent13, Fluent35, Fluent30, Fluent10, Fluent32, Fluent31, Fluent27, Fluent26, Fluent29, Fluent28, Fluent23, Fluent22, Fluent25, Fluent24, Fluent7, Fluent5, Fluent21, Fluent4, Fluent20, Fluent1, Fluent0, Fluent19, Fluent15, Fluent37, Fluent18, Fluent17>>

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs,tmState,rmWorking,rmPrepared,rmAborted,rmCommitted>>
/\ Fluent12' = [Fluent12 EXCEPT ![rm] = TRUE]
/\ Fluent34' = [Fluent34 EXCEPT ![rm] = TRUE]
/\ Fluent13' = [Fluent13 EXCEPT ![rm] = FALSE]
/\ Fluent32' = [Fluent32 EXCEPT ![rm] = FALSE]
/\ Fluent25' = [Fluent25 EXCEPT ![rm] = FALSE]
/\ Fluent7' = [Fluent7 EXCEPT ![rm] = TRUE]
/\ Fluent5' = [Fluent5 EXCEPT ![rm] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT ![rm] = TRUE]
/\ Fluent19' = [Fluent19 EXCEPT ![rm] = FALSE]
/\ Fluent37' = [Fluent37 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent11, Fluent33, Fluent14, Fluent36, Fluent35, Fluent30, Fluent10, Fluent31, Fluent27, Fluent26, Fluent29, Fluent28, Fluent23, Fluent22, Fluent9, Fluent8, Fluent24, Fluent6, Fluent21, Fluent20, Fluent3, Fluent2, Fluent1, Fluent0, Fluent16, Fluent15, Fluent18, Fluent17>>

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ (tmState \in {"init","commmitted"})
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared,rmWorking,rmPrepared,rmAborted,rmCommitted>>
/\ Fluent14' = [Fluent14 EXCEPT ![rm] = TRUE]
/\ Fluent31' = [Fluent31 EXCEPT ![rm] = FALSE]
/\ Fluent29' = [Fluent29 EXCEPT ![rm] = TRUE]
/\ Fluent28' = [Fluent28 EXCEPT ![rm] = TRUE]
/\ Fluent21' = [Fluent21 EXCEPT ![rm] = TRUE]
/\ Fluent20' = [Fluent20 EXCEPT ![rm] = TRUE]
/\ Fluent19' = [Fluent19 EXCEPT ![rm] = TRUE]
/\ Fluent16' = [Fluent16 EXCEPT ![rm] = TRUE]
/\ Fluent15' = [Fluent15 EXCEPT ![rm] = FALSE]
/\ Fluent18' = [Fluent18 EXCEPT ![rm] = TRUE]
/\ Fluent17' = [Fluent17 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent12, Fluent34, Fluent11, Fluent33, Fluent36, Fluent13, Fluent35, Fluent30, Fluent10, Fluent32, Fluent27, Fluent26, Fluent23, Fluent22, Fluent9, Fluent25, Fluent8, Fluent24, Fluent7, Fluent6, Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, Fluent37>>

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ rmPrepared' = [rmWorking EXCEPT![rm] = FALSE]
/\ rmCommitted' = [rmPrepared EXCEPT![rm] = TRUE]
/\ UNCHANGED <<msgs,tmState,tmPrepared,rmWorking,rmAborted>>
/\ Fluent12' = [Fluent12 EXCEPT ![rm] = TRUE]
/\ Fluent34' = [Fluent34 EXCEPT ![rm] = TRUE]
/\ Fluent11' = [Fluent11 EXCEPT ![rm] = FALSE]
/\ Fluent13' = [Fluent13 EXCEPT ![rm] = TRUE]
/\ Fluent35' = [Fluent35 EXCEPT ![rm] = TRUE]
/\ Fluent26' = [Fluent26 EXCEPT ![rm] = FALSE]
/\ Fluent9' = [Fluent9 EXCEPT ![rm] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT ![rm] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT ![rm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![rm] = TRUE]
/\ Fluent15' = [Fluent15 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent33, Fluent14, Fluent36, Fluent30, Fluent10, Fluent32, Fluent31, Fluent27, Fluent29, Fluent28, Fluent23, Fluent22, Fluent25, Fluent8, Fluent24, Fluent7, Fluent6, Fluent5, Fluent21, Fluent20, Fluent3, Fluent2, Fluent19, Fluent16, Fluent37, Fluent18, Fluent17>>

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared,rmWorking,rmPrepared,rmAborted,rmCommitted>>
/\ Fluent33' = [Fluent33 EXCEPT ![rm] = TRUE]
/\ Fluent30' = [Fluent30 EXCEPT ![rm] = TRUE]
/\ Fluent32' = [Fluent32 EXCEPT ![rm] = TRUE]
/\ Fluent31' = [Fluent31 EXCEPT ![rm] = TRUE]
/\ Fluent27' = [Fluent27 EXCEPT ![rm] = TRUE]
/\ Fluent26' = [Fluent26 EXCEPT ![rm] = TRUE]
/\ Fluent29' = [Fluent29 EXCEPT ![rm] = FALSE]
/\ Fluent23' = [Fluent23 EXCEPT ![rm] = TRUE]
/\ Fluent22' = [Fluent22 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent12, Fluent34, Fluent11, Fluent14, Fluent36, Fluent13, Fluent35, Fluent10, Fluent28, Fluent9, Fluent25, Fluent8, Fluent24, Fluent7, Fluent6, Fluent5, Fluent21, Fluent4, Fluent20, Fluent3, Fluent2, Fluent1, Fluent0, Fluent19, Fluent16, Fluent15, Fluent37, Fluent18, Fluent17>>

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ rmWorking' = [rmWorking EXCEPT![rm] = FALSE]
/\ rmPrepared' = [rmPrepared EXCEPT![rm] = FALSE]
/\ rmAborted' = [rmAborted EXCEPT![rm] = TRUE]
/\ UNCHANGED <<msgs,tmState,tmPrepared,rmCommitted>>
/\ Fluent34' = [Fluent34 EXCEPT ![rm] = FALSE]
/\ Fluent11' = [Fluent11 EXCEPT ![rm] = TRUE]
/\ Fluent36' = [Fluent36 EXCEPT ![rm] = TRUE]
/\ Fluent10' = [Fluent10 EXCEPT ![rm] = TRUE]
/\ Fluent22' = [Fluent22 EXCEPT ![rm] = TRUE]
/\ Fluent21' = [Fluent21 EXCEPT ![rm] = FALSE]
/\ Fluent0' = [Fluent0 EXCEPT ![rm] = FALSE]
/\ Fluent37' = [Fluent37 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent12, Fluent33, Fluent14, Fluent13, Fluent35, Fluent30, Fluent32, Fluent31, Fluent27, Fluent26, Fluent29, Fluent28, Fluent23, Fluent9, Fluent25, Fluent8, Fluent24, Fluent7, Fluent6, Fluent5, Fluent4, Fluent20, Fluent3, Fluent2, Fluent1, Fluent19, Fluent16, Fluent15, Fluent18, Fluent17>>

SilentAbort(rm) ==
/\ rmWorking[rm]
/\ rmWorking' = [rmWorking EXCEPT![rm] = FALSE]
/\ rmAborted' = [rmAborted EXCEPT![rm] = TRUE]
/\ UNCHANGED <<tmState,tmPrepared,msgs,rmCommitted,rmPrepared>>
/\ Fluent25' = [Fluent25 EXCEPT ![rm] = TRUE]
/\ Fluent24' = [Fluent24 EXCEPT ![rm] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent12, Fluent34, Fluent11, Fluent33, Fluent14, Fluent36, Fluent13, Fluent35, Fluent30, Fluent10, Fluent32, Fluent31, Fluent27, Fluent26, Fluent29, Fluent28, Fluent23, Fluent22, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent21, Fluent4, Fluent20, Fluent3, Fluent1, Fluent0, Fluent19, Fluent16, Fluent15, Fluent37, Fluent18, Fluent17>>

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
/\ (rmWorking \in [RMs -> BOOLEAN])
/\ (rmPrepared \in [RMs -> BOOLEAN])
/\ (rmAborted \in [RMs -> BOOLEAN])
/\ (rmCommitted \in [RMs -> BOOLEAN])
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
=============================================================================
