--------------------------- MODULE C1_hist_ii ---------------------------
EXTENDS Naturals, Sequences, Integers, Randomization

CONSTANTS RMs

VARIABLES tmState, Fluent10, tmPrepared, rmState, Fluent27, msgs, Fluent9, Fluent5, Fluent4, Fluent18, Fluent17

vars == <<tmState, Fluent10, tmPrepared, rmState, Fluent27, msgs, Fluent9, Fluent5, Fluent4, Fluent18, Fluent17>>

CandSep ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent4[var0]) => (Fluent5[var1])
/\ \A var0 \in RMs : (Fluent5[var0]) => (Fluent9[var0])
/\ \A var0 \in RMs : \E var1 \in RMs : (Fluent4[var0]) => (Fluent10[var1])
/\ \A var0 \in RMs : (Fluent10[var0]) => (Fluent17[var0])
/\ \A var0 \in RMs : (Fluent9[var0]) => (Fluent18[var0])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent17[var0]) => (~(Fluent27[var1]))

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ rmState = [rm \in RMs |-> "working"]
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent10 = [ x0 \in RMs |-> FALSE]
/\ Fluent27 = [ x0 \in RMs |-> FALSE]
/\ Fluent9 = [ x0 \in RMs |-> FALSE]
/\ Fluent5 = [ x0 \in RMs |-> FALSE]
/\ Fluent4 = [ x0 \in RMs |-> FALSE]
/\ Fluent18 = [ x0 \in RMs |-> FALSE]
/\ Fluent17 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ Fluent9' = [Fluent9 EXCEPT ![rm] = TRUE]
/\ Fluent18' = [Fluent18 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent10, Fluent27, Fluent5, Fluent4, Fluent17>>
/\ CandSep'

RcvPrepare(rm) ==
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs,tmState,rmState>>
/\ Fluent5' = [Fluent5 EXCEPT ![rm] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent10, Fluent27, Fluent9, Fluent18, Fluent17>>
/\ CandSep'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ Fluent10' = [Fluent10 EXCEPT ![rm] = TRUE]
/\ Fluent17' = [Fluent17 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent27, Fluent9, Fluent5, Fluent4, Fluent18>>
/\ CandSep'

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ Fluent4' = [Fluent4 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent10, Fluent27, Fluent9, Fluent5, Fluent18, Fluent17>>
/\ CandSep'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ UNCHANGED<<Fluent10, Fluent27, Fluent9, Fluent5, Fluent4, Fluent18, Fluent17>>
/\ CandSep'

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ Fluent27' = [Fluent27 EXCEPT ![rm] = TRUE]
/\ Fluent17' = [Fluent17 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent10, Fluent9, Fluent5, Fluent4, Fluent18>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<tmState,tmPrepared,msgs>>
/\ Fluent18' = [Fluent18 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent10, Fluent27, Fluent9, Fluent5, Fluent4, Fluent17>>
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
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
/\ Fluent10 \in [RMs -> BOOLEAN]
/\ Fluent27 \in [RMs -> BOOLEAN]
/\ Fluent9  \in [RMs -> BOOLEAN]
/\ Fluent5  \in [RMs -> BOOLEAN]
/\ Fluent4  \in [RMs -> BOOLEAN]
/\ Fluent18 \in [RMs -> BOOLEAN]
/\ Fluent17 \in [RMs -> BOOLEAN]

TypeOKRand ==
\*/\ (msgs \in SUBSET(Message))
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])
\*/\ (tmState \in {"init","committed","aborted"})
\*/\ (tmPrepared \in SUBSET(RMs))
\*/\ Fluent10 \in RandomSubset(4, [RMs -> BOOLEAN])
\*/\ Fluent27 \in RandomSubset(4, [RMs -> BOOLEAN])
\*/\ Fluent9  \in RandomSubset(4, [RMs -> BOOLEAN])
\*/\ Fluent5  \in RandomSubset(4, [RMs -> BOOLEAN])
\*/\ Fluent4  \in RandomSubset(4, [RMs -> BOOLEAN])
\*/\ Fluent18 \in RandomSubset(4, [RMs -> BOOLEAN])
\*/\ Fluent17 \in RandomSubset(4, [RMs -> BOOLEAN])
/\ msgs = {}
\*/\ rmState = [rm \in RMs |-> "working"]
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent10 = [ x0 \in RMs |-> FALSE]
/\ Fluent27 = [ x0 \in RMs |-> FALSE]
/\ Fluent9 = [ x0 \in RMs |-> FALSE]
/\ Fluent5 = [ x0 \in RMs |-> FALSE]
/\ Fluent4 = [ x0 \in RMs |-> FALSE]
/\ Fluent18 = [ x0 \in RMs |-> FALSE]
/\ Fluent17 = [ x0 \in RMs |-> FALSE]

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))

IISpec == TypeOKRand /\ Consistent /\ CandSep /\ [][Next]_vars

=============================================================================
