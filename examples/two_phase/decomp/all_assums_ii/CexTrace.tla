--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Sequences, Integers, TLC

CONSTANTS r2, r3, RMs, r1

VARIABLES msgs, tmState, tmPrepared, Fluent4, rmState, cexTraceIdx

vars == <<msgs, tmState, tmPrepared, Fluent4, rmState, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ msgs = {}
  /\ rmState = (r1 :> "working" @@ r2 :> "working" @@ r3 :> "working")
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmState = "init"
  /\ tmPrepared = {}

/\ cexTraceIdx = 1 =>
  /\ msgs = {}
  /\ rmState = (r1 :> "aborted" @@ r2 :> "working" @@ r3 :> "working")
  /\ Fluent4 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmState = "init"
  /\ tmPrepared = {}


CandSep == (\A var0 \in RMs : ~(Fluent4[var0]))

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ rmState = [rm \in RMs |-> "working"]
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent4 = [x0 \in RMs |-> FALSE]
/\ cexTraceIdx = 0
/\ TraceConstraint

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ UNCHANGED <<Fluent4>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs,tmState,rmState>>
/\ UNCHANGED <<Fluent4>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ (tmState \in {"init","commmitted"})
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ UNCHANGED <<Fluent4>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ UNCHANGED <<Fluent4>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ UNCHANGED <<Fluent4>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ UNCHANGED <<Fluent4>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<tmState,tmPrepared,msgs>>
/\ Fluent4' = [Fluent4 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<>>
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
\/ SilentAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (msgs \in SUBSET(Message))
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
=============================================================================
