--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Sequences, Integers, TLC

CONSTANTS r2, r3, RMs, r1

VARIABLES msgs, Fluent11, Fluent10, tmPrepared, cexTraceIdx

vars == <<msgs, Fluent11, Fluent10, tmPrepared, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ msgs = {}
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmPrepared = {}

/\ cexTraceIdx = 1 =>
  /\ msgs = {[type |-> "Prepared", theRM |-> r1]}
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmPrepared = {}

/\ cexTraceIdx = 2 =>
  /\ msgs = {[type |-> "Abort"], [type |-> "Prepared", theRM |-> r1]}
  /\ Fluent10 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmPrepared = {}

/\ cexTraceIdx = 3 =>
  /\ msgs = {[type |-> "Abort"], [type |-> "Prepared", theRM |-> r1]}
  /\ Fluent10 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmPrepared = {r1}

/\ cexTraceIdx = 4 =>
  /\ msgs = {[type |-> "Abort"], [type |-> "Prepared", theRM |-> r1]}
  /\ Fluent10 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ tmPrepared = {r1}


CandSep == (\A var0 \in RMs : (Fluent11[var0] => Fluent10[var0]))

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ tmPrepared = {}
/\ Fluent11 = [x0 \in RMs |-> FALSE]
/\ Fluent10 = [x0 \in RMs |-> FALSE]
/\ cexTraceIdx = 0
/\ TraceConstraint

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED <<Fluent11,Fluent10>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs>>
/\ UNCHANGED <<Fluent11,Fluent10>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ tmPrepared = RMs
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED <<Fluent11,Fluent10>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED <<Fluent11,Fluent10>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ UNCHANGED <<tmPrepared>>
/\ Fluent10' = [Fluent10 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent11>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED <<tmPrepared>>
/\ Fluent11' = [Fluent11 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent10>>
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
/\ (tmPrepared \in SUBSET(RMs))
=============================================================================
