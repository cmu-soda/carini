--------------------------- MODULE C1_hist ---------------------------
EXTENDS Naturals, Sequences, Integers, Randomization

CONSTANTS RMs

VARIABLES Fluent34, Fluent11, tmState, Fluent35, Fluent10, rmWorking, rmAborted, tmPrepared, msgs, Fluent24, Fluent5, Fluent4, Fluent3, Fluent2, rmCommitted, rmPrepared, Fluent37

vars == <<Fluent34, Fluent11, tmState, Fluent35, Fluent10, rmWorking, rmAborted, tmPrepared, msgs, Fluent24, Fluent5, Fluent4, Fluent3, Fluent2, rmCommitted, rmPrepared, Fluent37>>

CandSep ==
/\ \A var0 \in RMs : (Fluent3[var0]) => (Fluent2[var0])
/\ \A var0 \in RMs : (Fluent4[var0]) => (Fluent5[var0])
/\ \A var0 \in RMs : (Fluent5[var0]) => (Fluent3[var0])
/\ \A var0 \in RMs : (Fluent10[var0]) => (Fluent11[var0])
/\ \A var0 \in RMs : (Fluent24[var0]) => (Fluent5[var0])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent35[var1]) => (Fluent34[var0])
/\ \A var0 \in RMs : (Fluent10[var0]) => (Fluent37[var0])

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ rmWorking = [rm \in RMs |-> TRUE]
/\ rmPrepared = [rm \in RMs |-> FALSE]
/\ rmAborted = [rm \in RMs |-> FALSE]
/\ rmCommitted = [rm \in RMs |-> FALSE]
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent34 = [ x0 \in RMs |-> FALSE]
/\ Fluent11 = [ x0 \in RMs |-> FALSE]
/\ Fluent35 = [ x0 \in RMs |-> FALSE]
/\ Fluent10 = [ x0 \in RMs |-> FALSE]
/\ Fluent24 = [ x0 \in RMs |-> FALSE]
/\ Fluent5 = [ x0 \in RMs |-> FALSE]
/\ Fluent4 = [ x0 \in RMs |-> FALSE]
/\ Fluent3 = [ x0 \in RMs |-> FALSE]
/\ Fluent2 = [ x0 \in RMs |-> FALSE]
/\ Fluent37 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ rmWorking' = [rmWorking EXCEPT![rm] = FALSE]
/\ rmPrepared' = [rmPrepared EXCEPT![rm] = TRUE]
/\ UNCHANGED <<tmState,tmPrepared,rmAborted,rmCommitted>>
/\ Fluent3' = [Fluent3 EXCEPT ![rm] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent34, Fluent11, Fluent35, Fluent10, Fluent24, Fluent5, Fluent4, Fluent37>>
/\ CandSep'

RcvPrepare(rm) ==
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs,tmState,rmWorking,rmPrepared,rmAborted,rmCommitted>>
/\ Fluent34' = [Fluent34 EXCEPT ![rm] = TRUE]
/\ Fluent5' = [Fluent5 EXCEPT ![rm] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT ![rm] = TRUE]
/\ Fluent37' = [Fluent37 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent11, Fluent35, Fluent10, Fluent24, Fluent3, Fluent2>>
/\ CandSep'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared,rmWorking,rmPrepared,rmAborted,rmCommitted>>
/\ UNCHANGED<<Fluent34, Fluent11, Fluent35, Fluent10, Fluent24, Fluent5, Fluent4, Fluent3, Fluent2, Fluent37>>
/\ CandSep'

RcvCommit(rm) ==
/\ rmPrepared' = [rmWorking EXCEPT![rm] = FALSE]
/\ rmCommitted' = [rmPrepared EXCEPT![rm] = TRUE]
/\ UNCHANGED <<msgs,tmState,tmPrepared,rmWorking,rmAborted>>
/\ Fluent34' = [Fluent34 EXCEPT ![rm] = TRUE]
/\ Fluent11' = [Fluent11 EXCEPT ![rm] = FALSE]
/\ Fluent35' = [Fluent35 EXCEPT ![rm] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent10, Fluent24, Fluent5, Fluent3, Fluent2, Fluent37>>
/\ CandSep'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared,rmWorking,rmPrepared,rmAborted,rmCommitted>>
/\ UNCHANGED<<Fluent34, Fluent11, Fluent35, Fluent10, Fluent24, Fluent5, Fluent4, Fluent3, Fluent2, Fluent37>>
/\ CandSep'

RcvAbort(rm) ==
/\ rmWorking' = [rmWorking EXCEPT![rm] = FALSE]
/\ rmPrepared' = [rmPrepared EXCEPT![rm] = FALSE]
/\ rmAborted' = [rmAborted EXCEPT![rm] = TRUE]
/\ UNCHANGED <<msgs,tmState,tmPrepared,rmCommitted>>
/\ Fluent34' = [Fluent34 EXCEPT ![rm] = FALSE]
/\ Fluent11' = [Fluent11 EXCEPT ![rm] = TRUE]
/\ Fluent10' = [Fluent10 EXCEPT ![rm] = TRUE]
/\ Fluent37' = [Fluent37 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent35, Fluent24, Fluent5, Fluent4, Fluent3, Fluent2>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmWorking' = [rmWorking EXCEPT![rm] = FALSE]
/\ rmAborted' = [rmAborted EXCEPT![rm] = TRUE]
/\ UNCHANGED <<tmState,tmPrepared,msgs,rmCommitted,rmPrepared>>
/\ Fluent24' = [Fluent24 EXCEPT ![rm] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent34, Fluent11, Fluent35, Fluent10, Fluent5, Fluent4, Fluent3, Fluent37>>
/\ CandSep'

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
/\ Fluent34 \in [RMs -> BOOLEAN]
/\ Fluent11 \in [RMs -> BOOLEAN]
/\ Fluent35 \in [RMs -> BOOLEAN]
/\ Fluent10 \in [RMs -> BOOLEAN]
/\ Fluent24 \in [RMs -> BOOLEAN]
/\ Fluent5  \in [RMs -> BOOLEAN]
/\ Fluent4  \in [RMs -> BOOLEAN]
/\ Fluent3  \in [RMs -> BOOLEAN]
/\ Fluent2  \in [RMs -> BOOLEAN]
/\ Fluent37 \in [RMs -> BOOLEAN]

TypeOKRand ==
/\ (msgs \in SUBSET(Message))
/\ (rmWorking \in [RMs -> BOOLEAN])
/\ (rmPrepared \in [RMs -> BOOLEAN])
\*/\ (rmAborted \in [RMs -> BOOLEAN])
\*/\ (rmCommitted \in [RMs -> BOOLEAN])
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
/\ Fluent34 \in RandomSubset(1, [RMs -> BOOLEAN])
/\ Fluent11 \in RandomSubset(1, [RMs -> BOOLEAN])
/\ Fluent35 \in RandomSubset(1, [RMs -> BOOLEAN])
/\ Fluent10 \in RandomSubset(1, [RMs -> BOOLEAN])
/\ Fluent24 \in RandomSubset(1, [RMs -> BOOLEAN])
/\ Fluent5  \in RandomSubset(1, [RMs -> BOOLEAN])
/\ Fluent4  \in RandomSubset(1, [RMs -> BOOLEAN])
/\ Fluent3  \in RandomSubset(1, [RMs -> BOOLEAN])
/\ Fluent2  \in RandomSubset(1, [RMs -> BOOLEAN])
/\ Fluent37 \in RandomSubset(1, [RMs -> BOOLEAN])
\*/\ msgs = {}
\*/\ rmWorking = [rm \in RMs |-> TRUE]
\*/\ rmPrepared = [rm \in RMs |-> FALSE]
/\ rmAborted = [rm \in RMs |-> FALSE]
/\ rmCommitted = [rm \in RMs |-> FALSE]
\*/\ tmState = "init"
\*/\ tmPrepared = {}
\*/\ Fluent34 = [ x0 \in RMs |-> FALSE]
\*/\ Fluent11 = [ x0 \in RMs |-> FALSE]
\*/\ Fluent35 = [ x0 \in RMs |-> FALSE]
\*/\ Fluent10 = [ x0 \in RMs |-> FALSE]
\*/\ Fluent24 = [ x0 \in RMs |-> FALSE]
\*/\ Fluent5 = [ x0 \in RMs |-> FALSE]
\*/\ Fluent4 = [ x0 \in RMs |-> FALSE]
\*/\ Fluent3 = [ x0 \in RMs |-> FALSE]
\*/\ Fluent2 = [ x0 \in RMs |-> FALSE]
\*/\ Fluent37 = [ x0 \in RMs |-> FALSE]

Consistent == (\A rm1,rm2 \in RMs : ~((rmAborted[rm1] /\ rmCommitted[rm2])))

IndInv ==
    /\ Consistent

IISpec == TypeOKRand /\ IndInv /\ CandSep /\ [][Next]_vars
=============================================================================
