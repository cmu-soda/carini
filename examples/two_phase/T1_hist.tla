--------------------------- MODULE T1_hist ---------------------------
EXTENDS Naturals, Sequences, Integers, FiniteSets, TLC

CONSTANTS RMs

VARIABLES Fluent6_0, msgs, Fluent5_0, tmState, Fluent9_0, tmPrepared, Fluent8_0

vars == <<Fluent6_0, msgs, Fluent5_0, tmState, Fluent9_0, tmPrepared, Fluent8_0>>

CandSep ==
/\ \A var0 \in RMs : (Fluent5_0[var0]) => (~(Fluent6_0[var0]))
/\ \A var0 \in RMs : (Fluent9_0[var0]) => (Fluent8_0[var0])

Symmetry == Permutations(RMs)

Message == ([type |-> {"Prepared"},theRM |-> RMs] \cup [type |-> {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent5_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent9_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent8_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED <<tmState,tmPrepared>>
/\ Fluent8_0' = [Fluent8_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent9_0>>

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs,tmState>>
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent9_0, Fluent8_0>>

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ (tmState \in {"init","commmitted"})
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent9_0, Fluent8_0>>

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ Fluent5_0' = [Fluent5_0 EXCEPT ![rm] = TRUE]
/\ Fluent9_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent8_0>>

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent9_0, Fluent8_0>>

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ Fluent6_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent5_0, Fluent9_0, Fluent8_0>>

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
