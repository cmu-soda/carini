--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Sequences, Integers, TLC

CONSTANTS r2, r3, RMs, r1

VARIABLES Fluent12, Fluent34, Fluent11, Fluent33, Fluent14, tmState, Fluent13, Fluent35, Fluent30, Fluent10, Fluent32, Fluent31, rmWorking, rmAborted, tmPrepared, Fluent27, Fluent26, Fluent29, Fluent28, Fluent23, Fluent22, msgs, Fluent25, Fluent9, Fluent24, Fluent8, Fluent7, Fluent6, Fluent21, Fluent5, Fluent20, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, rmCommitted, rmPrepared, Fluent19, Fluent16, Fluent15, Fluent18, cexTraceIdx, Fluent17

vars == <<Fluent12, Fluent34, Fluent11, Fluent33, Fluent14, tmState, Fluent13, Fluent35, Fluent30, Fluent10, Fluent32, Fluent31, rmWorking, rmAborted, tmPrepared, Fluent27, Fluent26, Fluent29, Fluent28, Fluent23, Fluent22, msgs, Fluent25, Fluent9, Fluent24, Fluent8, Fluent7, Fluent6, Fluent21, Fluent5, Fluent20, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, rmCommitted, rmPrepared, Fluent19, Fluent16, Fluent15, Fluent18, cexTraceIdx, Fluent17>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
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
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent26 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent27 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent28 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent29 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent30 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent31 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent32 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent33 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent34 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent35 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmAborted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
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
  /\ rmCommitted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmPrepared = {}
  /\ msgs = {}
  /\ rmPrepared = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmState = "init"
  /\ rmWorking = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)

/\ cexTraceIdx = 1 =>
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
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent26 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent27 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent28 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent29 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent30 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent31 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent32 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent33 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent34 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent35 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmAborted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmCommitted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmPrepared = {}
  /\ msgs = {[type |-> "Prepared", theRM |-> r1]}
  /\ rmPrepared = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmState = "init"
  /\ rmWorking = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> TRUE)

/\ cexTraceIdx = 2 =>
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
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
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent26 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent27 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent28 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent29 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent30 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent31 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent32 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent33 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent34 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent35 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmAborted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmCommitted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmPrepared = {r1}
  /\ msgs = {[type |-> "Prepared", theRM |-> r1]}
  /\ rmPrepared = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmState = "init"
  /\ rmWorking = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> TRUE)

/\ cexTraceIdx = 3 =>
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent14 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent15 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent16 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent17 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent18 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent19 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent20 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent21 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent22 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent23 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent24 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent26 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent27 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent28 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent29 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent30 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent31 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent32 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent33 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent34 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent35 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmAborted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmCommitted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmPrepared = {r1}
  /\ msgs = {[type |-> "Commit"], [type |-> "Prepared", theRM |-> r1]}
  /\ rmPrepared = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmState = "committed"
  /\ rmWorking = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> TRUE)

/\ cexTraceIdx = 4 =>
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent14 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent15 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent16 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent17 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent18 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent19 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent20 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent21 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent22 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent23 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent24 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent26 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent27 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent28 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent29 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent30 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent31 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent32 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent33 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent34 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent35 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmAborted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmCommitted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmPrepared = {r1}
  /\ msgs = { [type |-> "Commit"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2] }
  /\ rmPrepared = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ tmState = "committed"
  /\ rmWorking = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> TRUE)

/\ cexTraceIdx = 5 =>
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent14 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent15 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent16 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent17 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent18 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent19 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent20 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent21 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent22 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent23 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent24 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent26 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent27 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent28 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent29 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent30 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent31 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent32 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent33 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent34 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent35 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmAborted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmCommitted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmPrepared = {r1, r2}
  /\ msgs = { [type |-> "Commit"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2] }
  /\ rmPrepared = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ tmState = "committed"
  /\ rmWorking = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> TRUE)

/\ cexTraceIdx = 6 =>
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent14 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent15 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent16 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent17 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent18 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent19 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent20 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent21 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent22 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent23 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent24 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent26 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent27 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent28 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent29 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent30 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent31 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent32 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent33 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent34 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent35 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmAborted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmCommitted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmPrepared = {r1, r2}
  /\ msgs = { [type |-> "Commit"],
    [type |-> "Abort"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2] }
  /\ rmPrepared = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ tmState = "aborted"
  /\ rmWorking = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> TRUE)

/\ cexTraceIdx = 7 =>
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> TRUE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> TRUE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent14 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent15 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent16 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent17 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent18 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent19 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent20 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent21 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent22 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent23 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent24 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent26 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent27 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent28 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent29 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent30 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent31 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent32 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent33 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent34 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent35 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmAborted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> TRUE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent3 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent4 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent7 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmCommitted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmPrepared = {r1, r2}
  /\ msgs = { [type |-> "Commit"],
    [type |-> "Abort"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2] }
  /\ rmPrepared = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ tmState = "aborted"
  /\ rmWorking = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)

/\ cexTraceIdx = 8 =>
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> TRUE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> TRUE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent13 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent14 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent15 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent16 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent17 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent18 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent19 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent20 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent21 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent22 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent23 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent24 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent26 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent27 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent28 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent29 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent30 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent31 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent32 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent33 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent34 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent35 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmAborted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> TRUE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent3 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent4 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent7 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmCommitted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmPrepared = {r1, r2}
  /\ msgs = { [type |-> "Commit"],
    [type |-> "Abort"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2],
    [type |-> "Prepared", theRM |-> r3] }
  /\ rmPrepared = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ tmState = "aborted"
  /\ rmWorking = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)

/\ cexTraceIdx = 9 =>
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> TRUE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> TRUE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent13 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent14 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent15 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent16 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent17 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent18 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent19 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent20 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent21 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent22 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent23 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent24 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent26 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent27 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent28 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent29 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent30 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent31 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent32 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent33 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent34 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent35 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmAborted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> TRUE)
  /\ Fluent0 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent3 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent4 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent7 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent9 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmCommitted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmPrepared = {r1, r2, r3}
  /\ msgs = { [type |-> "Commit"],
    [type |-> "Abort"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2],
    [type |-> "Prepared", theRM |-> r3] }
  /\ rmPrepared = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ tmState = "aborted"
  /\ rmWorking = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)

/\ cexTraceIdx = 10 =>
  /\ Fluent10 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> TRUE)
  /\ Fluent11 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> TRUE)
  /\ Fluent12 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent13 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent14 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent15 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent16 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent17 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent18 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent19 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent20 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent21 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent22 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent23 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent24 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent25 = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent26 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent27 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent28 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent29 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent30 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent31 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent32 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent33 = (r1 :> FALSE @@ r2 :> TRUE @@ r3 :> FALSE)
  /\ Fluent34 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent35 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmAborted = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> TRUE)
  /\ Fluent0 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent1 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ Fluent2 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent3 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent4 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent5 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent6 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent7 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent8 = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ Fluent9 = (r1 :> TRUE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ rmCommitted = (r1 :> TRUE @@ r2 :> TRUE @@ r3 :> TRUE)
  /\ tmPrepared = {r1, r2, r3}
  /\ msgs = { [type |-> "Commit"],
    [type |-> "Abort"],
    [type |-> "Prepared", theRM |-> r1],
    [type |-> "Prepared", theRM |-> r2],
    [type |-> "Prepared", theRM |-> r3] }
  /\ rmPrepared = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)
  /\ tmState = "aborted"
  /\ rmWorking = (r1 :> FALSE @@ r2 :> FALSE @@ r3 :> FALSE)


CandSep ==
/\ (\A var0 \in RMs : (Fluent1[var0] => Fluent0[var0]))
/\ (\A var0 \in RMs : (Fluent3[var0] => Fluent2[var0]))
/\ (\A var0 \in RMs : (Fluent4[var0] => Fluent5[var0]))
/\ (\A var0 \in RMs : (Fluent7[var0] => Fluent6[var0]))
/\ (\A var0 \in RMs : (\A var1 \in RMs : (Fluent9[var0] => Fluent8[var1])))
/\ (\A var0 \in RMs : (Fluent10[var0] => Fluent11[var0]))
/\ (\A var0 \in RMs : (\A var1 \in RMs : (Fluent13[var1] => Fluent12[var0])))
/\ (\A var0 \in RMs : (\E var1 \in RMs : (Fluent15[var0] => Fluent14[var1])))
/\ (\A var0 \in RMs : (Fluent17[var0] => Fluent16[var0]))
/\ (\A var0 \in RMs : (Fluent18[var0] => Fluent19[var0]))
/\ (\A var0 \in RMs : (Fluent20[var0] => Fluent21[var0]))
/\ (\A var0 \in RMs : (\E var1 \in RMs : (Fluent22[var0] => Fluent23[var1])))
/\ (\A var0 \in RMs : (Fluent24[var0] => Fluent25[var0]))
/\ (\A var0 \in RMs : (Fluent27[var0] => Fluent26[var0]))
/\ (\A var0 \in RMs : (Fluent28[var0] => Fluent29[var0]))
/\ (\A var0 \in RMs : (Fluent30[var0] => Fluent31[var0]))
/\ (\A var0 \in RMs : (Fluent33[var0] => Fluent32[var0]))
/\ (\A var0 \in RMs : (\A var1 \in RMs : (Fluent35[var1] => Fluent34[var0])))

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ rmWorking = [rm \in RMs |-> TRUE]
/\ rmPrepared = [rm \in RMs |-> FALSE]
/\ rmAborted = [rm \in RMs |-> FALSE]
/\ rmCommitted = [rm \in RMs |-> FALSE]
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent12 = [x0 \in RMs |-> FALSE]
/\ Fluent34 = [x0 \in RMs |-> FALSE]
/\ Fluent11 = [x0 \in RMs |-> FALSE]
/\ Fluent33 = [x0 \in RMs |-> FALSE]
/\ Fluent14 = [x0 \in RMs |-> FALSE]
/\ Fluent13 = [x0 \in RMs |-> FALSE]
/\ Fluent35 = [x0 \in RMs |-> FALSE]
/\ Fluent30 = [x0 \in RMs |-> FALSE]
/\ Fluent10 = [x0 \in RMs |-> FALSE]
/\ Fluent32 = [x0 \in RMs |-> FALSE]
/\ Fluent31 = [x0 \in RMs |-> FALSE]
/\ Fluent27 = [x0 \in RMs |-> FALSE]
/\ Fluent26 = [x0 \in RMs |-> FALSE]
/\ Fluent29 = [x0 \in RMs |-> FALSE]
/\ Fluent28 = [x0 \in RMs |-> FALSE]
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
/\ rmWorking' = [rmWorking EXCEPT![rm] = FALSE]
/\ rmPrepared' = [rmPrepared EXCEPT![rm] = TRUE]
/\ UNCHANGED <<tmState,tmPrepared,rmAborted,rmCommitted>>
/\ Fluent9' = [Fluent9 EXCEPT![rm] = FALSE]
/\ Fluent8' = [Fluent8 EXCEPT![rm] = TRUE]
/\ Fluent6' = [Fluent6 EXCEPT![rm] = TRUE]
/\ Fluent3' = [Fluent3 EXCEPT![rm] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT![rm] = TRUE]
/\ Fluent16' = [Fluent16 EXCEPT![rm] = FALSE]
/\ UNCHANGED <<Fluent12,Fluent34,Fluent11,Fluent33,Fluent14,Fluent13,Fluent35,Fluent30,Fluent10,Fluent32,Fluent31,Fluent27,Fluent26,Fluent29,Fluent28,Fluent23,Fluent22,Fluent25,Fluent24,Fluent7,Fluent5,Fluent21,Fluent4,Fluent20,Fluent1,Fluent0,Fluent19,Fluent15,Fluent18,Fluent17>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvPrepare(rm) ==
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs,tmState,rmWorking,rmPrepared,rmAborted,rmCommitted>>
/\ Fluent12' = [Fluent12 EXCEPT![rm] = TRUE]
/\ Fluent34' = [Fluent34 EXCEPT![rm] = TRUE]
/\ Fluent13' = [Fluent13 EXCEPT![rm] = FALSE]
/\ Fluent32' = [Fluent32 EXCEPT![rm] = FALSE]
/\ Fluent25' = [Fluent25 EXCEPT![rm] = FALSE]
/\ Fluent7' = [Fluent7 EXCEPT![rm] = TRUE]
/\ Fluent5' = [Fluent5 EXCEPT![rm] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT![rm] = TRUE]
/\ Fluent19' = [Fluent19 EXCEPT![rm] = FALSE]
/\ UNCHANGED <<Fluent11,Fluent33,Fluent14,Fluent35,Fluent30,Fluent10,Fluent31,Fluent27,Fluent26,Fluent29,Fluent28,Fluent23,Fluent22,Fluent9,Fluent8,Fluent24,Fluent6,Fluent21,Fluent20,Fluent3,Fluent2,Fluent1,Fluent0,Fluent16,Fluent15,Fluent18,Fluent17>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared,rmWorking,rmPrepared,rmAborted,rmCommitted>>
/\ Fluent14' = [Fluent14 EXCEPT![rm] = TRUE]
/\ Fluent31' = [Fluent31 EXCEPT![rm] = FALSE]
/\ Fluent29' = [Fluent29 EXCEPT![rm] = TRUE]
/\ Fluent28' = [Fluent28 EXCEPT![rm] = TRUE]
/\ Fluent21' = [Fluent21 EXCEPT![rm] = TRUE]
/\ Fluent20' = [Fluent20 EXCEPT![rm] = TRUE]
/\ Fluent19' = [Fluent19 EXCEPT![rm] = TRUE]
/\ Fluent16' = [Fluent16 EXCEPT![rm] = TRUE]
/\ Fluent15' = [Fluent15 EXCEPT![rm] = FALSE]
/\ Fluent18' = [Fluent18 EXCEPT![rm] = TRUE]
/\ Fluent17' = [Fluent17 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent12,Fluent34,Fluent11,Fluent33,Fluent13,Fluent35,Fluent30,Fluent10,Fluent32,Fluent27,Fluent26,Fluent23,Fluent22,Fluent9,Fluent25,Fluent8,Fluent24,Fluent7,Fluent6,Fluent5,Fluent4,Fluent3,Fluent2,Fluent1,Fluent0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvCommit(rm) ==
/\ rmPrepared' = [rmWorking EXCEPT![rm] = FALSE]
/\ rmCommitted' = [rmPrepared EXCEPT![rm] = TRUE]
/\ UNCHANGED <<msgs,tmState,tmPrepared,rmWorking,rmAborted>>
/\ Fluent12' = [Fluent12 EXCEPT![rm] = TRUE]
/\ Fluent34' = [Fluent34 EXCEPT![rm] = TRUE]
/\ Fluent11' = [Fluent11 EXCEPT![rm] = FALSE]
/\ Fluent13' = [Fluent13 EXCEPT![rm] = TRUE]
/\ Fluent35' = [Fluent35 EXCEPT![rm] = TRUE]
/\ Fluent26' = [Fluent26 EXCEPT![rm] = FALSE]
/\ Fluent9' = [Fluent9 EXCEPT![rm] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT![rm] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT![rm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT![rm] = TRUE]
/\ Fluent15' = [Fluent15 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent33,Fluent14,Fluent30,Fluent10,Fluent32,Fluent31,Fluent27,Fluent29,Fluent28,Fluent23,Fluent22,Fluent25,Fluent8,Fluent24,Fluent7,Fluent6,Fluent5,Fluent21,Fluent20,Fluent3,Fluent2,Fluent19,Fluent16,Fluent18,Fluent17>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared,rmWorking,rmPrepared,rmAborted,rmCommitted>>
/\ Fluent33' = [Fluent33 EXCEPT![rm] = TRUE]
/\ Fluent30' = [Fluent30 EXCEPT![rm] = TRUE]
/\ Fluent32' = [Fluent32 EXCEPT![rm] = TRUE]
/\ Fluent31' = [Fluent31 EXCEPT![rm] = TRUE]
/\ Fluent27' = [Fluent27 EXCEPT![rm] = TRUE]
/\ Fluent26' = [Fluent26 EXCEPT![rm] = TRUE]
/\ Fluent29' = [Fluent29 EXCEPT![rm] = FALSE]
/\ Fluent23' = [Fluent23 EXCEPT![rm] = TRUE]
/\ Fluent22' = [Fluent22 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent12,Fluent34,Fluent11,Fluent14,Fluent13,Fluent35,Fluent10,Fluent28,Fluent9,Fluent25,Fluent8,Fluent24,Fluent7,Fluent6,Fluent5,Fluent21,Fluent4,Fluent20,Fluent3,Fluent2,Fluent1,Fluent0,Fluent19,Fluent16,Fluent15,Fluent18,Fluent17>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RcvAbort(rm) ==
/\ rmWorking' = [rmWorking EXCEPT![rm] = FALSE]
/\ rmPrepared' = [rmPrepared EXCEPT![rm] = FALSE]
/\ rmAborted' = [rmAborted EXCEPT![rm] = TRUE]
/\ UNCHANGED <<msgs,tmState,tmPrepared,rmCommitted>>
/\ Fluent34' = [Fluent34 EXCEPT![rm] = FALSE]
/\ Fluent11' = [Fluent11 EXCEPT![rm] = TRUE]
/\ Fluent10' = [Fluent10 EXCEPT![rm] = TRUE]
/\ Fluent22' = [Fluent22 EXCEPT![rm] = TRUE]
/\ Fluent21' = [Fluent21 EXCEPT![rm] = FALSE]
/\ Fluent0' = [Fluent0 EXCEPT![rm] = FALSE]
/\ UNCHANGED <<Fluent12,Fluent33,Fluent14,Fluent13,Fluent35,Fluent30,Fluent32,Fluent31,Fluent27,Fluent26,Fluent29,Fluent28,Fluent23,Fluent9,Fluent25,Fluent8,Fluent24,Fluent7,Fluent6,Fluent5,Fluent4,Fluent20,Fluent3,Fluent2,Fluent1,Fluent19,Fluent16,Fluent15,Fluent18,Fluent17>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SilentAbort(rm) ==
/\ rmWorking' = [rmWorking EXCEPT![rm] = FALSE]
/\ rmAborted' = [rmAborted EXCEPT![rm] = TRUE]
/\ UNCHANGED <<tmState,tmPrepared,msgs,rmCommitted,rmPrepared>>
/\ Fluent25' = [Fluent25 EXCEPT![rm] = TRUE]
/\ Fluent24' = [Fluent24 EXCEPT![rm] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT![rm] = FALSE]
/\ UNCHANGED <<Fluent12,Fluent34,Fluent11,Fluent33,Fluent14,Fluent13,Fluent35,Fluent30,Fluent10,Fluent32,Fluent31,Fluent27,Fluent26,Fluent29,Fluent28,Fluent23,Fluent22,Fluent9,Fluent8,Fluent7,Fluent6,Fluent5,Fluent21,Fluent4,Fluent20,Fluent3,Fluent1,Fluent0,Fluent19,Fluent16,Fluent15,Fluent18,Fluent17>>
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
/\ (rmWorking \in [RMs -> BOOLEAN])
/\ (rmPrepared \in [RMs -> BOOLEAN])
/\ (rmAborted \in [RMs -> BOOLEAN])
/\ (rmCommitted \in [RMs -> BOOLEAN])
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))

Consistent == (\A rm1,rm2 \in RMs : ~((rmAborted[rm1] /\ rmCommitted[rm2])))

IISpec == ((TypeOK /\ Consistent) /\ [][Next]_vars)
=============================================================================
