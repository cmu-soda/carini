--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS req3, req2, n1, n2, n3, req1, Node, DbRequestId, Request, Response, resp2, resp3, id2, resp1, id1

VARIABLES db_request_sent, t, Fluent16, db_response_sent, cexTraceIdx

vars == <<db_request_sent, t, Fluent16, db_response_sent, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ db_request_sent = {}
  /\ db_response_sent = {}
  /\ Fluent16 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ t = {}

/\ cexTraceIdx = 1 =>
  /\ db_request_sent = {<<id1, req1>>}
  /\ db_response_sent = {}
  /\ Fluent16 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ t = {<<id1, n1>>}

/\ cexTraceIdx = 2 =>
  /\ db_request_sent = {<<id1, req1>>, <<id2, req1>>}
  /\ db_response_sent = {}
  /\ Fluent16 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ t = {<<id1, n1>>, <<id2, n1>>}

/\ cexTraceIdx = 3 =>
  /\ db_request_sent = {<<id1, req1>>, <<id2, req1>>}
  /\ db_response_sent = {<<id1, resp1>>}
  /\ Fluent16 = (id1 :> TRUE @@ id2 :> FALSE)
  /\ t = {<<id1, n1>>, <<id2, n1>>}

/\ cexTraceIdx = 4 =>
  /\ db_request_sent = {<<id1, req1>>, <<id2, req1>>}
  /\ db_response_sent = {<<id1, resp1>>, <<id2, resp1>>}
  /\ Fluent16 = (id1 :> TRUE @@ id2 :> TRUE)
  /\ t = {<<id1, n1>>, <<id2, n1>>}


CandSep == (\A var0 \in DbRequestId : (\A var1 \in DbRequestId : (\E var2 \in DbRequestId : (Fluent16[var2] => var1 = var0))))

Symmetry == (((Permutations(Node) \cup Permutations(Request)) \cup Permutations(Response)) \cup Permutations(DbRequestId))

NoneWithId(i) == (\A n \in Node : (<<i,n>> \notin t))

ServerProcessRequest(n,r,i) ==
/\ NoneWithId(i)
/\ t' = (t \cup {<<i,n>>})
/\ db_request_sent' = (db_request_sent \cup {<<i,r>>})
/\ UNCHANGED <<db_response_sent>>
/\ UNCHANGED <<Fluent16>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

DbProcessRequest(i,r,p) ==
/\ (<<i,r>> \in db_request_sent)
/\ db_response_sent' = (db_response_sent \cup {<<i,p>>})
/\ UNCHANGED <<db_request_sent,t>>
/\ Fluent16' = [Fluent16 EXCEPT![i] = TRUE]
/\ UNCHANGED <<>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

ServerProcessDbResponse(n,i,p) ==
/\ (<<i,p>> \in db_response_sent)
/\ (<<i,n>> \in t)
/\ UNCHANGED <<db_request_sent,db_response_sent,t>>
/\ UNCHANGED <<Fluent16>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
\/ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
\/ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p))

Init ==
/\ db_request_sent = {}
/\ db_response_sent = {}
/\ t = {}
/\ Fluent16 = [x0 \in DbRequestId |-> FALSE]
/\ cexTraceIdx = 0
/\ TraceConstraint

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (db_request_sent \in SUBSET((DbRequestId \X Request)))
/\ (db_response_sent \in SUBSET((DbRequestId \X Response)))
/\ (t \in SUBSET((DbRequestId \X Node)))
=============================================================================
