--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Sequences, Integers, TLC

CONSTANTS r2, r3, RMs, r1

VARIABLES Fluent12, msgs, Fluent11, Fluent9, Fluent13, Fluent8, Fluent7, Fluent6, Fluent10, Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, cexTraceIdx

vars == <<Fluent12, msgs, Fluent11, Fluent9, Fluent13, Fluent8, Fluent7, Fluent6, Fluent10, Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ msgs = {}
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)

/\ cexTraceIdx = 1 =>
  /\ msgs = {[type |-> "Prepared", theRM |-> r2]}
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)

/\ cexTraceIdx = 2 =>
  /\ msgs = {[type |-> "Prepared", theRM |-> r1], [type |-> "Prepared", theRM |-> r2]}
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)

/\ cexTraceIdx = 3 =>
  /\ msgs = {[type |-> "Prepared", theRM |-> r1], [type |-> "Prepared", theRM |-> r2]}
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)

/\ cexTraceIdx = 4 =>
  /\ msgs = { [type |-> "Abort"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2] }
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)

/\ cexTraceIdx = 5 =>
  /\ msgs = { [type |-> "Abort"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2] }
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)

/\ cexTraceIdx = 6 =>
  /\ msgs = { [type |-> "Abort"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2] }
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)

/\ cexTraceIdx = 7 =>
  /\ msgs = { [type |-> "Abort"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2],
    [type |-> "Prepared", theRM |-> r3] }
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent3 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)

/\ cexTraceIdx = 8 =>
  /\ msgs = { [type |-> "Abort"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2],
    [type |-> "Prepared", theRM |-> r3] }
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent3 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent7 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)

/\ cexTraceIdx = 9 =>
  /\ msgs = { [type |-> "Commit"],
    [type |-> "Abort"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2],
    [type |-> "Prepared", theRM |-> r3] }
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent3 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent7 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)

/\ cexTraceIdx = 10 =>
  /\ msgs = { [type |-> "Commit"],
    [type |-> "Abort"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2],
    [type |-> "Prepared", theRM |-> r3] }
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent3 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent7 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)


CandSep ==
/\ (\A var0 \in RMs : (Fluent7[var0] => Fluent6[var0]))
/\ (\A var0 \in RMs : (\A var1 \in RMs : (Fluent9[var1] => Fluent8[var0])))
/\ (\A var0 \in RMs : (Fluent10[var0] => ~(Fluent11[var0])))
/\ (\A var0 \in RMs : (Fluent12[var0] => Fluent13[var0]))

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ Fluent12 = [x0 \in RMs |-> FALSE]
/\ Fluent11 = [x0 \in RMs |-> FALSE]
/\ Fluent9 = [x0 \in RMs |-> FALSE]
/\ Fluent8 = [x0 \in RMs |-> FALSE]
/\ Fluent13 = [x0 \in RMs |-> FALSE]
/\ Fluent7 = [x0 \in RMs |-> FALSE]
/\ Fluent6 = [x0 \in RMs |-> FALSE]
/\ Fluent10 = [x0 \in RMs |-> FALSE]
/\ Fluent5 = [x0 \in RMs |-> FALSE]
/\ Fluent4 = [x0 \in RMs |-> FALSE]
/\ Fluent3 = [x0 \in RMs |-> FALSE]
/\ Fluent2 = [x0 \in RMs |-> FALSE]
/\ Fluent1 = [x0 \in RMs |-> FALSE]
/\ Fluent0 = [x0 \in RMs |-> FALSE]
/\ cexTraceIdx = 0
/\ TraceConstraint

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED <<Fluent12,Fluent11,Fluent9,Fluent8,Fluent13,Fluent7,Fluent6,Fluent10>>
/\ CandSep'
/\ Fluent2' = [Fluent2 EXCEPT![rm] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent5,Fluent4,Fluent3,Fluent0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ UNCHANGED <<msgs>>
/\ Fluent8' = [Fluent8 EXCEPT![rm] = TRUE]
/\ Fluent13' = [Fluent13 EXCEPT![rm] = FALSE]
/\ Fluent6' = [Fluent6 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent12,Fluent11,Fluent9,Fluent7,Fluent10>>
/\ CandSep'
/\ UNCHANGED <<Fluent5,Fluent4,Fluent3,Fluent2,Fluent1,Fluent0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ Fluent9' = [Fluent9 EXCEPT![rm] = TRUE]
/\ Fluent7' = [Fluent7 EXCEPT![rm] = TRUE]
/\ Fluent10' = [Fluent10 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent12,Fluent11,Fluent8,Fluent13,Fluent6>>
/\ CandSep'
/\ UNCHANGED <<Fluent5,Fluent4,Fluent3,Fluent2,Fluent1,Fluent0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED <<Fluent12,Fluent11,Fluent9,Fluent8,Fluent13,Fluent7,Fluent6,Fluent10>>
/\ CandSep'
/\ Fluent4' = [Fluent4 EXCEPT![rm] = TRUE]
/\ Fluent3' = [Fluent3 EXCEPT![rm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent5,Fluent2,Fluent1>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ Fluent12' = [Fluent12 EXCEPT![rm] = TRUE]
/\ Fluent11' = [Fluent11 EXCEPT![rm] = TRUE]
/\ Fluent13' = [Fluent13 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent9,Fluent8,Fluent7,Fluent6,Fluent10>>
/\ CandSep'
/\ UNCHANGED <<Fluent5,Fluent4,Fluent3,Fluent2,Fluent1,Fluent0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED <<Fluent12,Fluent11,Fluent9,Fluent8,Fluent13,Fluent7,Fluent6,Fluent10>>
/\ CandSep'
/\ Fluent5' = [Fluent5 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent4,Fluent3,Fluent2,Fluent1,Fluent0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

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
/\ (\A var0 \in RMs : (Fluent0[var0] => Fluent1[var0]))
/\ (\A var0 \in RMs : (\A var1 \in RMs : (Fluent3[var0] => Fluent2[var1])))
/\ (\A var0 \in RMs : (\A var1 \in RMs : (Fluent4[var0] => ~(Fluent5[var1]))))
=============================================================================
