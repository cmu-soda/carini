--------------------------- MODULE D1_hist ---------------------------
EXTENDS Naturals, Sequences, Integers, FiniteSets, TLC

CONSTANTS RMs

VARIABLES Fluent15_0, Fluent6_0, msgs, Fluent14_0, Fluent5_0, Fluent9_0, Fluent8_0, Fluent24_0, Fluent23_0

vars == <<Fluent15_0, Fluent6_0, msgs, Fluent14_0, Fluent5_0, Fluent9_0, Fluent8_0, Fluent24_0, Fluent23_0>>

CandSep ==
/\ \A var0 \in RMs : (Fluent24_0[var0]) => (~(Fluent23_0[var0]))
/\ \A var0 \in RMs : (Fluent14_0[var0]) => (Fluent15_0[var0])

Message == ([type |-> {"Prepared"},theRM |-> RMs] \cup [type |-> {"Commit","Abort"}])

Symmetry == Permutations(RMs)

Init ==
/\ msgs = {}
/\ Fluent15_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent14_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent24_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent23_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent5_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent9_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent8_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED<<Fluent15_0, Fluent14_0, Fluent24_0, Fluent23_0>>
/\ CandSep'
/\ Fluent8_0' = [Fluent8_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent9_0>>
/\ CandSep'

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ UNCHANGED <<msgs>>
/\ Fluent15_0' = [Fluent15_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent14_0, Fluent24_0, Fluent23_0>>
/\ CandSep'
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent9_0, Fluent8_0>>
/\ CandSep'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ Fluent14_0' = [x0 \in RMs |-> TRUE]
/\ Fluent24_0' = [Fluent24_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent15_0, Fluent23_0>>
/\ CandSep'
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent9_0, Fluent8_0>>
/\ CandSep'

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED<<Fluent15_0, Fluent14_0, Fluent24_0, Fluent23_0>>
/\ CandSep'
/\ Fluent5_0' = [Fluent5_0 EXCEPT ![rm] = TRUE]
/\ Fluent9_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent8_0>>
/\ CandSep'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ Fluent23_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent15_0, Fluent14_0, Fluent24_0>>
/\ CandSep'
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent9_0, Fluent8_0>>
/\ CandSep'

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED<<Fluent15_0, Fluent14_0, Fluent24_0, Fluent23_0>>
/\ CandSep'
/\ Fluent6_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent5_0, Fluent9_0, Fluent8_0>>
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
/\ \A var0 \in RMs : (Fluent5_0[var0]) => (~(Fluent6_0[var0]))
/\ \A var0 \in RMs : (Fluent9_0[var0]) => (Fluent8_0[var0])
=============================================================================
