--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Sequences, Integers, FiniteSets, TLC

CONSTANTS r2, r3, RMs, r1

VARIABLES Fluent15_0, Fluent6_0, msgs, Fluent14_0, Fluent5_0, err, Fluent9_0, Fluent8_0, cexTraceIdx

vars == <<Fluent15_0, Fluent6_0, msgs, Fluent14_0, Fluent5_0, err, Fluent9_0, Fluent8_0, cexTraceIdx>>

NoErr == err = FALSE

CandSep == (\A var0 \in RMs : (Fluent14_0[var0] => Fluent15_0[var0]))

Message == ([type |-> {"Prepared"},theRM |-> RMs] \cup [type |-> {"Commit","Abort"}])

Symmetry == Permutations(RMs)

Init ==
/\ msgs = {}
/\ Fluent15_0 = [x0 \in RMs |-> FALSE]
/\ Fluent14_0 = [x0 \in RMs |-> FALSE]
/\ Fluent6_0 = [x0 \in RMs |-> FALSE]
/\ Fluent5_0 = [x0 \in RMs |-> FALSE]
/\ Fluent9_0 = [x0 \in RMs |-> FALSE]
/\ Fluent8_0 = [x0 \in RMs |-> FALSE]
/\ cexTraceIdx = 0
/\ err = FALSE

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED <<Fluent15_0,Fluent14_0>>
/\ CandSep'
/\ Fluent8_0' = [Fluent8_0 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent6_0,Fluent5_0,Fluent9_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ UNCHANGED <<msgs>>
/\ Fluent15_0' = [Fluent15_0 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent14_0>>
/\ CandSep'
/\ UNCHANGED <<Fluent6_0,Fluent5_0,Fluent9_0,Fluent8_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ Fluent14_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED <<Fluent15_0>>
/\ CandSep'
/\ UNCHANGED <<Fluent6_0,Fluent5_0,Fluent9_0,Fluent8_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED <<Fluent15_0,Fluent14_0>>
/\ CandSep'
/\ Fluent5_0' = [Fluent5_0 EXCEPT![rm] = TRUE]
/\ Fluent9_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED <<Fluent6_0,Fluent8_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ UNCHANGED <<Fluent15_0,Fluent14_0>>
/\ CandSep'
/\ UNCHANGED <<Fluent6_0,Fluent5_0,Fluent9_0,Fluent8_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED <<Fluent15_0,Fluent14_0>>
/\ CandSep'
/\ Fluent6_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED <<Fluent5_0,Fluent9_0,Fluent8_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

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
/\ (\A var0 \in RMs : (Fluent5_0[var0] => ~(Fluent6_0[var0])))
/\ (\A var0 \in RMs : (Fluent9_0[var0] => Fluent8_0[var0]))

TraceConstraint ==
/\ cexTraceIdx = 0 => SndPrepare(r1) /\ err' = err
/\ cexTraceIdx = 1 => SndPrepare(r2) /\ err' = err
/\ cexTraceIdx = 2 => RcvPrepare(r1) /\ err' = err
/\ cexTraceIdx = 3 => RcvPrepare(r2) /\ err' = err
/\ cexTraceIdx = 4 => SndPrepare(r3) /\ err' = err
/\ cexTraceIdx = 5 => RcvPrepare(r3) /\ err' = err
/\ cexTraceIdx = 6 => SndAbort(r1) /\ err' = err
/\ cexTraceIdx = 7 => SndCommit(r2) /\ err' = err
/\ cexTraceIdx = 8 => RcvCommit(r1) /\ err' = err
/\ cexTraceIdx = 9 => RcvAbort(r1) /\ err' = TRUE
/\ cexTraceIdx >= 10 => FALSE

InternalAction == UNCHANGED<<cexTraceIdx,err>>

TraceConstraintSpec == Init /\ [][Next /\ (TraceConstraint \/ InternalAction)]_vars
=============================================================================
