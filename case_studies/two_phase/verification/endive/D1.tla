--------------------------- MODULE D1 ---------------------------
EXTENDS Naturals, Sequences, Integers, TLC, Randomization

CONSTANTS RMs

VARIABLES msgs, Fluent9, Fluent8, Fluent10, Fluent5, Fluent3, Fluent2

vars == <<msgs, Fluent9, Fluent8, Fluent10, Fluent5, Fluent3, Fluent2>>

NextUnchanged == UNCHANGED vars
Symmetry == Permutations(RMs)

CandSep ==
/\ \A var0 \in RMs : (\E var1 \in RMs : Fluent9[var1]) => (Fluent8[var0])
/\ \A var0 \in RMs : (Fluent10[var0]) => (\A var1 \in RMs : ~Fluent9[var1])

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ Fluent9 = [ x0 \in RMs |-> FALSE]
/\ Fluent8 = [ x0 \in RMs |-> FALSE]
/\ Fluent10 = [ x0 \in RMs |-> FALSE]
/\ Fluent5 = [ x0 \in RMs |-> FALSE]
/\ Fluent3 = [ x0 \in RMs |-> TRUE]
/\ Fluent2 = [ x0 \in RMs |-> TRUE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED<<Fluent9, Fluent8, Fluent10>>
/\ CandSep'
/\ Fluent3' = [Fluent3 EXCEPT![rm] = FALSE]
/\ UNCHANGED<<Fluent5, Fluent2>>
/\ CandSep'

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ UNCHANGED <<msgs>>
/\ Fluent8' = [Fluent8 EXCEPT![rm] = TRUE]
/\ UNCHANGED<<Fluent9, Fluent10>>
/\ CandSep'
/\ UNCHANGED<<Fluent5, Fluent3, Fluent2>>
/\ CandSep'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ Fluent9' = [Fluent9 EXCEPT![rm] = TRUE]
/\ UNCHANGED<<Fluent8, Fluent10>>
/\ CandSep'
/\ UNCHANGED<<Fluent5, Fluent3, Fluent2>>
/\ CandSep'

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED<<Fluent9, Fluent8, Fluent10>>
/\ CandSep'
/\ Fluent2' = [Fluent2 EXCEPT![rm] = FALSE]
/\ UNCHANGED<<Fluent5, Fluent3>>
/\ CandSep'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ Fluent10' = [Fluent10 EXCEPT![rm] = TRUE]
/\ UNCHANGED<<Fluent9, Fluent8>>
/\ CandSep'
/\ UNCHANGED<<Fluent5, Fluent3, Fluent2>>
/\ CandSep'

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED<<Fluent9, Fluent8, Fluent10>>
/\ CandSep'
/\ Fluent5' = [Fluent5 EXCEPT![rm] = TRUE]
/\ UNCHANGED<<Fluent3, Fluent2>>
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
/\ msgs \in SUBSET(Message)
/\ Fluent9  \in [RMs -> BOOLEAN]
/\ Fluent8  \in [RMs -> BOOLEAN]
/\ Fluent10 \in [RMs -> BOOLEAN]
/\ Fluent5  \in [RMs -> BOOLEAN]
/\ Fluent3  \in [RMs -> BOOLEAN]
/\ Fluent2  \in [RMs -> BOOLEAN]

Safety ==
/\ (\E var0 \in RMs : Fluent3[var0]) => (\A var0 \in RMs : Fluent2[var0])
/\ (\E var0 \in RMs : Fluent5[var0]) => (\A var0 \in RMs : Fluent2[var0])
=============================================================================
