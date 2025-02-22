--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Sequences, Integers, TLC

CONSTANTS r2, r3, RMs, r1

VARIABLES Fluent12, Fluent11, Fluent14, tmState, Fluent13, Fluent10, tmPrepared, rmState, Fluent23, msgs, Fluent22, Fluent25, Fluent9, Fluent24, Fluent8, Fluent7, Fluent6, Fluent21, Fluent5, Fluent20, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, Fluent19, Fluent16, Fluent15, Fluent18, cexTraceIdx, Fluent17

vars == <<Fluent12, Fluent11, Fluent14, tmState, Fluent13, Fluent10, tmPrepared, rmState, Fluent23, msgs, Fluent22, Fluent25, Fluent9, Fluent24, Fluent8, Fluent7, Fluent6, Fluent21, Fluent5, Fluent20, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, Fluent19, Fluent16, Fluent15, Fluent18, cexTraceIdx, Fluent17>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ msgs = {}
  /\ rmState = (r1 :> "working" @@ r2 :> "working" @@ r3 :> "working")
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent14 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent15 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent16 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent17 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent18 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent19 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent20 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent21 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent22 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent23 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent24 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmState = "init"
  /\ tmPrepared = {}

/\ cexTraceIdx = 1 =>
  /\ msgs = {[type |-> "Prepared", theRM |-> r1]}
  /\ rmState = (r1 :> "prepared" @@ r2 :> "working" @@ r3 :> "working")
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent14 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent15 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent16 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent17 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent18 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent19 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent20 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent21 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent22 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent23 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent24 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmState = "init"
  /\ tmPrepared = {}

/\ cexTraceIdx = 2 =>
  /\ msgs = {[type |-> "Prepared", theRM |-> r1]}
  /\ rmState = (r1 :> "prepared" @@ r2 :> "working" @@ r3 :> "working")
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent14 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent15 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent16 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent17 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent18 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent19 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent20 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent21 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent22 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent23 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent24 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmState = "init"
  /\ tmPrepared = {r1}

/\ cexTraceIdx = 3 =>
  /\ msgs = {[type |-> "Commit"], [type |-> "Prepared", theRM |-> r1]}
  /\ rmState = (r1 :> "prepared" @@ r2 :> "working" @@ r3 :> "working")
  /\ Fluent10 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent14 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent15 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent16 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent17 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent18 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent19 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent20 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent21 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent22 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent23 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent24 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmState = "committed"
  /\ tmPrepared = {r1}

/\ cexTraceIdx = 4 =>
  /\ msgs = { [type |-> "Commit"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2] }
  /\ rmState = (r1 :> "prepared" @@ r2 :> "prepared" @@ r3 :> "working")
  /\ Fluent10 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent14 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent15 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent16 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent17 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent18 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent19 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent20 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent21 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent22 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent23 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent24 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ tmState = "committed"
  /\ tmPrepared = {r1}

/\ cexTraceIdx = 5 =>
  /\ msgs = { [type |-> "Commit"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2] }
  /\ rmState = (r1 :> "prepared" @@ r2 :> "prepared" @@ r3 :> "working")
  /\ Fluent10 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent14 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent15 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent16 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent17 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent18 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent19 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent20 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent21 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent22 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent23 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent24 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ tmState = "committed"
  /\ tmPrepared = {r1, r2}

/\ cexTraceIdx = 6 =>
  /\ msgs = { [type |-> "Commit"],
    [type |-> "Abort"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2] }
  /\ rmState = (r1 :> "prepared" @@ r2 :> "prepared" @@ r3 :> "working")
  /\ Fluent10 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent14 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent15 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent16 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent17 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent18 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent19 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent20 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent21 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent22 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent23 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent24 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ tmState = "aborted"
  /\ tmPrepared = {r1, r2}

/\ cexTraceIdx = 7 =>
  /\ msgs = { [type |-> "Commit"],
    [type |-> "Abort"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2] }
  /\ rmState = (r1 :> "prepared" @@ r2 :> "aborted" @@ r3 :> "working")
  /\ Fluent10 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent14 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent15 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent16 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent17 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent18 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent19 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent20 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent21 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent22 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent23 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent24 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ tmState = "aborted"
  /\ tmPrepared = {r1, r2}

/\ cexTraceIdx = 8 =>
  /\ msgs = { [type |-> "Commit"],
    [type |-> "Abort"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2],
    [type |-> "Prepared", theRM |-> r3] }
  /\ rmState = (r1 :> "prepared" @@ r2 :> "aborted" @@ r3 :> "prepared")
  /\ Fluent10 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent14 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent15 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent16 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent17 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent18 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent19 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent20 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent21 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent22 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent23 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent24 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ tmState = "aborted"
  /\ tmPrepared = {r1, r2}

/\ cexTraceIdx = 9 =>
  /\ msgs = { [type |-> "Commit"],
    [type |-> "Abort"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2],
    [type |-> "Prepared", theRM |-> r3] }
  /\ rmState = (r1 :> "prepared" @@ r2 :> "aborted" @@ r3 :> "prepared")
  /\ Fluent10 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent14 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent15 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent16 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent17 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent18 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent19 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent20 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent21 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent22 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent23 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent24 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent3 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent7 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent9 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ tmState = "aborted"
  /\ tmPrepared = {r1, r2, r3}

/\ cexTraceIdx = 10 =>
  /\ msgs = { [type |-> "Commit"],
    [type |-> "Abort"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2],
    [type |-> "Prepared", theRM |-> r3] }
  /\ rmState = (r1 :> "committed" @@ r2 :> "aborted" @@ r3 :> "prepared")
  /\ Fluent10 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent14 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent15 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent16 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent17 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent18 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent19 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent20 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent21 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent22 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent23 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent24 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent3 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent4 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent7 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent9 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ tmState = "aborted"
  /\ tmPrepared = {r1, r2, r3}


CandSep ==
/\ (\A var0 \in RMs : (Fluent0[var0] => Fluent1[var0]))
/\ (\A var0 \in RMs : (Fluent3[var0] => Fluent2[var0]))
/\ (\A var0 \in RMs : (\A var1 \in RMs : (Fluent4[var0] => Fluent5[var1])))
/\ (\A var0 \in RMs : (Fluent6[var0] => Fluent7[var0]))
/\ (\A var0 \in RMs : (Fluent8[var0] => Fluent9[var0]))
/\ (\A var0 \in RMs : (\E var1 \in RMs : (Fluent11[var0] => Fluent10[var1])))
/\ (\A var0 \in RMs : (Fluent12[var0] => Fluent13[var0]))
/\ (\A var0 \in RMs : (Fluent15[var0] => Fluent14[var0]))
/\ (\A var0 \in RMs : (Fluent16[var0] => Fluent17[var0]))
/\ (\A var0 \in RMs : (Fluent19[var0] => Fluent18[var0]))
/\ (\A var0 \in RMs : (\E var1 \in RMs : (Fluent21[var0] => Fluent20[var1])))
/\ (\A var0 \in RMs : (Fluent22[var0] => Fluent23[var0]))
/\ (\A var0 \in RMs : (\E var1 \in RMs : (Fluent24[var1] => Fluent25[var0])))

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ rmState = [rm \in RMs |-> "working"]
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent12 = [x0 \in RMs |-> FALSE]
/\ Fluent11 = [x0 \in RMs |-> FALSE]
/\ Fluent14 = [x0 \in RMs |-> FALSE]
/\ Fluent13 = [x0 \in RMs |-> FALSE]
/\ Fluent10 = [x0 \in RMs |-> FALSE]
/\ Fluent23 = [x0 \in RMs |-> FALSE]
/\ Fluent22 = [x0 \in RMs |-> FALSE]
/\ Fluent9 = [x0 \in RMs |-> FALSE]
/\ Fluent25 = [x0 \in RMs |-> FALSE]
/\ Fluent8 = [x0 \in RMs |-> FALSE]
/\ Fluent24 = [x0 \in RMs |-> FALSE]
/\ Fluent7 = [x0 \in RMs |-> FALSE]
/\ Fluent6 = [x0 \in RMs |-> FALSE]
/\ Fluent5 = [x0 \in RMs |-> FALSE]
/\ Fluent21 = [x0 \in RMs |-> FALSE]
/\ Fluent4 = [x0 \in RMs |-> FALSE]
/\ Fluent20 = [x0 \in RMs |-> FALSE]
/\ Fluent3 = [x0 \in RMs |-> FALSE]
/\ Fluent2 = [x0 \in RMs |-> FALSE]
/\ Fluent1 = [x0 \in RMs |-> FALSE]
/\ Fluent0 = [x0 \in RMs |-> FALSE]
/\ Fluent19 = [x0 \in RMs |-> FALSE]
/\ Fluent16 = [x0 \in RMs |-> FALSE]
/\ Fluent15 = [x0 \in RMs |-> FALSE]
/\ Fluent18 = [x0 \in RMs |-> FALSE]
/\ Fluent17 = [x0 \in RMs |-> FALSE]
/\ cexTraceIdx = 0
/\ TraceConstraint

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ Fluent9' = [Fluent9 EXCEPT![rm] = TRUE]
/\ Fluent7' = [Fluent7 EXCEPT![rm] = FALSE]
/\ Fluent1' = [Fluent1 EXCEPT![rm] = TRUE]
/\ Fluent19' = [Fluent19 EXCEPT![rm] = TRUE]
/\ Fluent18' = [Fluent18 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent12,Fluent11,Fluent14,Fluent13,Fluent10,Fluent23,Fluent22,Fluent25,Fluent8,Fluent24,Fluent6,Fluent5,Fluent21,Fluent4,Fluent20,Fluent3,Fluent2,Fluent0,Fluent16,Fluent15,Fluent17>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvPrepare(rm) ==
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs,tmState,rmState>>
/\ Fluent13' = [Fluent13 EXCEPT![rm] = FALSE]
/\ Fluent8' = [Fluent8 EXCEPT![rm] = TRUE]
/\ Fluent7' = [Fluent7 EXCEPT![rm] = TRUE]
/\ Fluent6' = [Fluent6 EXCEPT![rm] = TRUE]
/\ Fluent5' = [Fluent5 EXCEPT![rm] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT![rm] = FALSE]
/\ Fluent3' = [Fluent3 EXCEPT![rm] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent12,Fluent11,Fluent14,Fluent10,Fluent23,Fluent22,Fluent9,Fluent25,Fluent24,Fluent21,Fluent20,Fluent1,Fluent0,Fluent19,Fluent16,Fluent15,Fluent18,Fluent17>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ Fluent12' = [Fluent12 EXCEPT![rm] = TRUE]
/\ Fluent14' = [Fluent14 EXCEPT![rm] = FALSE]
/\ Fluent13' = [Fluent13 EXCEPT![rm] = TRUE]
/\ Fluent10' = [Fluent10 EXCEPT![rm] = TRUE]
/\ Fluent23' = [Fluent23 EXCEPT![rm] = TRUE]
/\ Fluent22' = [Fluent22 EXCEPT![rm] = TRUE]
/\ Fluent24' = [Fluent24 EXCEPT![rm] = TRUE]
/\ Fluent16' = [Fluent16 EXCEPT![rm] = TRUE]
/\ Fluent17' = [Fluent17 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent11,Fluent9,Fluent25,Fluent8,Fluent7,Fluent6,Fluent5,Fluent21,Fluent4,Fluent20,Fluent3,Fluent2,Fluent1,Fluent0,Fluent19,Fluent15,Fluent18>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ Fluent11' = [Fluent11 EXCEPT![rm] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT![rm] = TRUE]
/\ Fluent3' = [Fluent3 EXCEPT![rm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent12,Fluent14,Fluent13,Fluent10,Fluent23,Fluent22,Fluent9,Fluent25,Fluent8,Fluent24,Fluent7,Fluent6,Fluent5,Fluent21,Fluent20,Fluent2,Fluent1,Fluent19,Fluent16,Fluent15,Fluent18,Fluent17>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ Fluent23' = [Fluent23 EXCEPT![rm] = FALSE]
/\ Fluent25' = [Fluent25 EXCEPT![rm] = TRUE]
/\ Fluent24' = [Fluent24 EXCEPT![rm] = TRUE]
/\ Fluent20' = [Fluent20 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent12,Fluent11,Fluent14,Fluent13,Fluent10,Fluent22,Fluent9,Fluent8,Fluent7,Fluent6,Fluent5,Fluent21,Fluent4,Fluent3,Fluent2,Fluent1,Fluent0,Fluent19,Fluent16,Fluent15,Fluent18,Fluent17>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ Fluent14' = [Fluent14 EXCEPT![rm] = TRUE]
/\ Fluent25' = [Fluent25 EXCEPT![rm] = TRUE]
/\ Fluent24' = [Fluent24 EXCEPT![rm] = TRUE]
/\ Fluent21' = [Fluent21 EXCEPT![rm] = TRUE]
/\ Fluent15' = [Fluent15 EXCEPT![rm] = TRUE]
/\ Fluent17' = [Fluent17 EXCEPT![rm] = FALSE]
/\ UNCHANGED <<Fluent12,Fluent11,Fluent13,Fluent10,Fluent23,Fluent22,Fluent9,Fluent8,Fluent7,Fluent6,Fluent5,Fluent4,Fluent20,Fluent3,Fluent2,Fluent1,Fluent0,Fluent19,Fluent16,Fluent18>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SilentAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<tmState,tmPrepared,msgs>>
/\ Fluent18' = [Fluent18 EXCEPT![rm] = FALSE]
/\ UNCHANGED <<Fluent12,Fluent11,Fluent14,Fluent13,Fluent10,Fluent23,Fluent22,Fluent9,Fluent25,Fluent8,Fluent24,Fluent7,Fluent6,Fluent5,Fluent21,Fluent4,Fluent20,Fluent3,Fluent2,Fluent1,Fluent0,Fluent19,Fluent16,Fluent15,Fluent17>>
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
\/ SilentAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (msgs \in SUBSET(Message))
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))
=============================================================================
