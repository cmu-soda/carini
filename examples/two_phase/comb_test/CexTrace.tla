--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Sequences, Integers, TLC

CONSTANTS r2, r3, RMs, r1

VARIABLES msgs, Fluent4, cexTraceIdx

vars == <<msgs, Fluent4, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ msgs = {}
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)

/\ cexTraceIdx = 1 =>
  /\ msgs = {[type |-> "Prepared", theRM |-> r2]}
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)

/\ cexTraceIdx = 2 =>
  /\ msgs = {[type |-> "Prepared", theRM |-> r1], [type |-> "Prepared", theRM |-> r2]}
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)

/\ cexTraceIdx = 3 =>
  /\ msgs = {[type |-> "Prepared", theRM |-> r1], [type |-> "Prepared", theRM |-> r2]}
  /\ Fluent4 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)


CandSep == (\A var0 \in RMs : ~(Fluent4[var0]))

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ Fluent4 = [x0 \in RMs |-> FALSE]
/\ cexTraceIdx = 0
/\ TraceConstraint

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED <<Fluent4>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ UNCHANGED <<msgs>>
/\ Fluent4' = [Fluent4 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ UNCHANGED <<Fluent4>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED <<Fluent4>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ UNCHANGED <<Fluent4>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED <<Fluent4>>
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
=============================================================================
