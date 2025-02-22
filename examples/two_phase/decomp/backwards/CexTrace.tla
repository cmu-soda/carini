--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Sequences, Integers, TLC

CONSTANTS r2, r3, RMs, r1

VARIABLES msgs, tmState, tmPrepared, rmState, Fluent1, Fluent0, cexTraceIdx

vars == <<msgs, tmState, tmPrepared, rmState, Fluent1, Fluent0, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ msgs = {}
  /\ rmState = (r1 :> "working" @@ r2 :> "working" @@ r3 :> "working")
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmState = "init"
  /\ tmPrepared = {}

/\ cexTraceIdx = 1 =>
  /\ msgs = {[type |-> "Prepared", theRM |-> r1]}
  /\ rmState = (r1 :> "prepared" @@ r2 :> "working" @@ r3 :> "working")
  /\ Fluent0 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmState = "init"
  /\ tmPrepared = {}

/\ cexTraceIdx = 2 =>
  /\ msgs = {[type |-> "Abort"], [type |-> "Prepared", theRM |-> r1]}
  /\ rmState = (r1 :> "prepared" @@ r2 :> "working" @@ r3 :> "working")
  /\ Fluent0 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmState = "aborted"
  /\ tmPrepared = {}

/\ cexTraceIdx = 3 =>
  /\ msgs = {[type |-> "Abort"], [type |-> "Prepared", theRM |-> r1]}
  /\ rmState = (r1 :> "aborted" @@ r2 :> "working" @@ r3 :> "working")
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmState = "aborted"
  /\ tmPrepared = {}


CandSep == (\A var0 \in RMs : (Fluent1[var0] => Fluent0[var0]))

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ rmState = [rm \in RMs |-> "working"]
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent1 = [x0 \in RMs |-> FALSE]
/\ Fluent0 = [x0 \in RMs |-> FALSE]
/\ cexTraceIdx = 0
/\ TraceConstraint

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ Fluent1' = [Fluent1 EXCEPT![rm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvPrepare(rm) ==
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs,tmState,rmState>>
/\ UNCHANGED <<Fluent1,Fluent0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ UNCHANGED <<Fluent1,Fluent0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ UNCHANGED <<Fluent1,Fluent0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ UNCHANGED <<Fluent1,Fluent0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ Fluent0' = [Fluent0 EXCEPT![rm] = FALSE]
/\ UNCHANGED <<Fluent1>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SilentAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<tmState,tmPrepared,msgs>>
/\ UNCHANGED <<Fluent1,Fluent0>>
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
