--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS req3, req2, n1, n2, n3, req1, Node, DbRequestId, Request, Response, resp2, resp3, id2, resp1, id1

VARIABLES Fluent12, Fluent11, Fluent9, Fluent8, Fluent7, request_sent, Fluent6, Fluent10, Fluent5, response_sent, Fluent4, match, Fluent3, response_received, Fluent2, Fluent1, Fluent0, cexTraceIdx

vars == <<Fluent12, Fluent11, Fluent9, Fluent8, Fluent7, request_sent, Fluent6, Fluent10, Fluent5, response_sent, Fluent4, match, Fluent3, response_received, Fluent2, Fluent1, Fluent0, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ request_sent = {}
  /\ match = {<<req1, resp1>>}
  /\ response_received = {}
  /\ Fluent10 = ( req1 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    req2 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    req3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent11 = ( id1 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) )
  /\ Fluent12 = ( id1 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) )
  /\ Fluent0 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ Fluent1 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ Fluent2 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ Fluent3 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ Fluent4 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ Fluent5 = ( n1 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    n2 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    n3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent6 = (resp1 :> FALSE @@ resp2 :> FALSE @@ resp3 :> FALSE)
  /\ Fluent7 = (resp1 :> FALSE @@ resp2 :> FALSE @@ resp3 :> FALSE)
  /\ Fluent8 = ( req1 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    req2 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    req3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent9 = ( id1 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) )
  /\ response_sent = {}

/\ cexTraceIdx = 1 =>
  /\ request_sent = {<<n2, req2>>}
  /\ match = {<<req1, resp1>>}
  /\ response_received = {}
  /\ Fluent10 = ( req1 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    req2 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    req3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent11 = ( id1 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) )
  /\ Fluent12 = ( id1 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) )
  /\ Fluent0 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ Fluent1 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ Fluent2 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ Fluent3 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ Fluent4 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ Fluent5 = ( n1 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    n2 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    n3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent6 = (resp1 :> FALSE @@ resp2 :> FALSE @@ resp3 :> FALSE)
  /\ Fluent7 = (resp1 :> FALSE @@ resp2 :> FALSE @@ resp3 :> FALSE)
  /\ Fluent8 = ( req1 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    req2 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    req3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent9 = ( id1 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) )
  /\ response_sent = {}

/\ cexTraceIdx = 2 =>
  /\ request_sent = {<<n1, req1>>, <<n2, req2>>}
  /\ match = {<<req1, resp1>>}
  /\ response_received = {}
  /\ Fluent10 = ( req1 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    req2 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    req3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent11 = ( id1 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) )
  /\ Fluent12 = ( id1 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) )
  /\ Fluent0 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ Fluent1 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ Fluent2 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ Fluent3 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ Fluent4 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ Fluent5 = ( n1 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    n2 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    n3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent6 = (resp1 :> FALSE @@ resp2 :> FALSE @@ resp3 :> FALSE)
  /\ Fluent7 = (resp1 :> FALSE @@ resp2 :> FALSE @@ resp3 :> FALSE)
  /\ Fluent8 = ( req1 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    req2 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    req3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent9 = ( id1 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) )
  /\ response_sent = {}

/\ cexTraceIdx = 3 =>
  /\ request_sent = {<<n1, req1>>, <<n2, req2>>}
  /\ match = {<<req1, resp1>>}
  /\ response_received = {}
  /\ Fluent10 = ( req1 :> (id1 :> TRUE @@ id2 :> FALSE) @@
    req2 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    req3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent11 = ( id1 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) )
  /\ Fluent12 = ( id1 :> (req1 :> TRUE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) )
  /\ Fluent0 = (id1 :> TRUE @@ id2 :> FALSE)
  /\ Fluent1 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ Fluent2 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ Fluent3 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ Fluent4 = (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ Fluent5 = ( n1 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    n2 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    n3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent6 = (resp1 :> FALSE @@ resp2 :> FALSE @@ resp3 :> FALSE)
  /\ Fluent7 = (resp1 :> FALSE @@ resp2 :> FALSE @@ resp3 :> FALSE)
  /\ Fluent8 = ( req1 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    req2 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    req3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent9 = ( id1 :> (req1 :> TRUE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) )
  /\ response_sent = {}

/\ cexTraceIdx = 4 =>
  /\ request_sent = {<<n1, req1>>, <<n2, req2>>}
  /\ match = {<<req1, resp1>>}
  /\ response_received = {}
  /\ Fluent10 = ( req1 :> (id1 :> TRUE @@ id2 :> FALSE) @@
    req2 :> (id1 :> FALSE @@ id2 :> TRUE) @@
    req3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent11 = ( id1 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) )
  /\ Fluent12 = ( id1 :> (req1 :> TRUE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> TRUE @@ req3 :> FALSE) )
  /\ Fluent0 = (id1 :> TRUE @@ id2 :> TRUE)
  /\ Fluent1 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ Fluent2 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ Fluent3 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ Fluent4 = (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> FALSE)
  /\ Fluent5 = ( n1 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    n2 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    n3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent6 = (resp1 :> FALSE @@ resp2 :> FALSE @@ resp3 :> FALSE)
  /\ Fluent7 = (resp1 :> FALSE @@ resp2 :> FALSE @@ resp3 :> FALSE)
  /\ Fluent8 = ( req1 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    req2 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    req3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent9 = ( id1 :> (req1 :> TRUE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> TRUE @@ req3 :> FALSE) )
  /\ response_sent = {}

/\ cexTraceIdx = 5 =>
  /\ request_sent = {<<n1, req1>>, <<n2, req2>>}
  /\ match = {<<req1, resp1>>}
  /\ response_received = {}
  /\ Fluent10 = ( req1 :> (id1 :> TRUE @@ id2 :> FALSE) @@
    req2 :> (id1 :> FALSE @@ id2 :> TRUE) @@
    req3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent11 = ( id1 :> (req1 :> TRUE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) )
  /\ Fluent12 = ( id1 :> (req1 :> TRUE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> TRUE @@ req3 :> FALSE) )
  /\ Fluent0 = (id1 :> TRUE @@ id2 :> TRUE)
  /\ Fluent1 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ Fluent2 = (id1 :> FALSE @@ id2 :> FALSE)
  /\ Fluent3 = (id1 :> TRUE @@ id2 :> FALSE)
  /\ Fluent4 = (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> FALSE)
  /\ Fluent5 = ( n1 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    n2 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    n3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent6 = (resp1 :> FALSE @@ resp2 :> FALSE @@ resp3 :> FALSE)
  /\ Fluent7 = (resp1 :> TRUE @@ resp2 :> FALSE @@ resp3 :> FALSE)
  /\ Fluent8 = ( req1 :> (id1 :> TRUE @@ id2 :> FALSE) @@
    req2 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    req3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent9 = ( id1 :> (req1 :> TRUE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> TRUE @@ req3 :> FALSE) )
  /\ response_sent = {}

/\ cexTraceIdx = 6 =>
  /\ request_sent = {<<n1, req1>>, <<n2, req2>>}
  /\ match = {<<req1, resp1>>}
  /\ response_received = {}
  /\ Fluent10 = ( req1 :> (id1 :> TRUE @@ id2 :> FALSE) @@
    req2 :> (id1 :> FALSE @@ id2 :> TRUE) @@
    req3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent11 = ( id1 :> (req1 :> TRUE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) )
  /\ Fluent12 = ( id1 :> (req1 :> TRUE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> TRUE @@ req3 :> FALSE) )
  /\ Fluent0 = (id1 :> TRUE @@ id2 :> TRUE)
  /\ Fluent1 = (id1 :> TRUE @@ id2 :> FALSE)
  /\ Fluent2 = (id1 :> TRUE @@ id2 :> FALSE)
  /\ Fluent3 = (id1 :> TRUE @@ id2 :> FALSE)
  /\ Fluent4 = (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> FALSE)
  /\ Fluent5 = ( n1 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    n2 :> (id1 :> TRUE @@ id2 :> FALSE) @@
    n3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent6 = (resp1 :> TRUE @@ resp2 :> FALSE @@ resp3 :> FALSE)
  /\ Fluent7 = (resp1 :> TRUE @@ resp2 :> FALSE @@ resp3 :> FALSE)
  /\ Fluent8 = ( req1 :> (id1 :> TRUE @@ id2 :> FALSE) @@
    req2 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    req3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent9 = ( id1 :> (req1 :> TRUE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> TRUE @@ req3 :> FALSE) )
  /\ response_sent = {<<n2, resp1>>}

/\ cexTraceIdx = 7 =>
  /\ request_sent = {<<n1, req1>>, <<n2, req2>>}
  /\ match = {<<req1, resp1>>}
  /\ response_received = {<<n2, resp1>>}
  /\ Fluent10 = ( req1 :> (id1 :> TRUE @@ id2 :> FALSE) @@
    req2 :> (id1 :> FALSE @@ id2 :> TRUE) @@
    req3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent11 = ( id1 :> (req1 :> TRUE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> FALSE @@ req3 :> FALSE) )
  /\ Fluent12 = ( id1 :> (req1 :> TRUE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> TRUE @@ req3 :> FALSE) )
  /\ Fluent0 = (id1 :> TRUE @@ id2 :> TRUE)
  /\ Fluent1 = (id1 :> TRUE @@ id2 :> FALSE)
  /\ Fluent2 = (id1 :> TRUE @@ id2 :> FALSE)
  /\ Fluent3 = (id1 :> TRUE @@ id2 :> FALSE)
  /\ Fluent4 = (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> FALSE)
  /\ Fluent5 = ( n1 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    n2 :> (id1 :> TRUE @@ id2 :> FALSE) @@
    n3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent6 = (resp1 :> TRUE @@ resp2 :> FALSE @@ resp3 :> FALSE)
  /\ Fluent7 = (resp1 :> TRUE @@ resp2 :> FALSE @@ resp3 :> FALSE)
  /\ Fluent8 = ( req1 :> (id1 :> TRUE @@ id2 :> FALSE) @@
    req2 :> (id1 :> FALSE @@ id2 :> FALSE) @@
    req3 :> (id1 :> FALSE @@ id2 :> FALSE) )
  /\ Fluent9 = ( id1 :> (req1 :> TRUE @@ req2 :> FALSE @@ req3 :> FALSE) @@
    id2 :> (req1 :> FALSE @@ req2 :> TRUE @@ req3 :> FALSE) )
  /\ response_sent = {<<n2, resp1>>}


CandSep ==
/\ (\A var0 \in DbRequestId : (Fluent1[var0] => Fluent0[var0]))
/\ (\A var0 \in DbRequestId : (Fluent2[var0] => Fluent3[var0]))
/\ (\A var0 \in DbRequestId : (\A var1 \in Node : (Fluent5[var1][var0] => Fluent4[var1])))
/\ (\A var0 \in Response : (Fluent6[var0] => Fluent7[var0]))
/\ (\A var0 \in DbRequestId : (\E var1 \in DbRequestId : (\A var2 \in Request : (Fluent8[var2][var0] => Fluent9[var1][var2]))))
/\ (\A var0 \in DbRequestId : (\E var1 \in Request : (\A var2 \in Request : (Fluent10[var2][var0] => var1 = var2))))
/\ (\A var0 \in Request : (\A var1 \in DbRequestId : (Fluent11[var1][var0] => Fluent12[var1][var0])))

Symmetry == (((Permutations(Node) \cup Permutations(Request)) \cup Permutations(Response)) \cup Permutations(DbRequestId))

ResponseMatched(n,p) ==
\E r \in Request :
/\ (<<n,r>> \in request_sent)
/\ (<<r,p>> \in match)

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<match,response_sent,response_received>>
/\ UNCHANGED <<Fluent12,Fluent11,Fluent9,Fluent8,Fluent7,Fluent6,Fluent5,Fluent10,Fluent4,Fluent3,Fluent2,Fluent1,Fluent0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

ServerProcessRequest(n,r,i) ==
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ Fluent12' = [Fluent12 EXCEPT![i][r] = TRUE]
/\ Fluent9' = [Fluent9 EXCEPT![i][r] = TRUE]
/\ Fluent10' = [Fluent10 EXCEPT![r][i] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT![n] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT![i] = TRUE]
/\ UNCHANGED <<Fluent11,Fluent8,Fluent7,Fluent6,Fluent5,Fluent3,Fluent2,Fluent1>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

DbProcessRequest(i,r,p) ==
/\ (<<r,p>> \in match)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ Fluent11' = [Fluent11 EXCEPT![i][r] = TRUE]
/\ Fluent8' = [Fluent8 EXCEPT![r][i] = TRUE]
/\ Fluent7' = [Fluent7 EXCEPT![p] = TRUE]
/\ Fluent3' = [Fluent3 EXCEPT![i] = TRUE]
/\ UNCHANGED <<Fluent12,Fluent9,Fluent6,Fluent5,Fluent10,Fluent4,Fluent2,Fluent1,Fluent0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

ServerProcessDbResponse(n,i,p) ==
/\ response_sent' = (response_sent \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_received>>
/\ Fluent6' = [Fluent6 EXCEPT![p] = TRUE]
/\ Fluent5' = [Fluent5 EXCEPT![n][i] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT![i] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT![i] = TRUE]
/\ UNCHANGED <<Fluent12,Fluent11,Fluent9,Fluent8,Fluent7,Fluent10,Fluent4,Fluent3,Fluent0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

ReceiveResponse(n,p) ==
/\ (<<n,p>> \in response_sent)
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_sent>>
/\ UNCHANGED <<Fluent12,Fluent11,Fluent9,Fluent8,Fluent7,Fluent6,Fluent5,Fluent10,Fluent4,Fluent3,Fluent2,Fluent1,Fluent0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\/ (\E n \in Node, r \in Request : NewRequest(n,r))
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
\/ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
\/ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p))
\/ (\E n \in Node, p \in Response : ReceiveResponse(n,p))

Init ==
/\ (match \in SUBSET((Request \X Response)))
/\ request_sent = {}
/\ response_sent = {}
/\ response_received = {}
/\ Fluent12 = [x0 \in DbRequestId |-> [x1 \in Request |-> FALSE]]
/\ Fluent11 = [x0 \in DbRequestId |-> [x1 \in Request |-> FALSE]]
/\ Fluent9 = [x0 \in DbRequestId |-> [x1 \in Request |-> FALSE]]
/\ Fluent8 = [x0 \in Request |-> [x1 \in DbRequestId |-> FALSE]]
/\ Fluent7 = [x0 \in Response |-> FALSE]
/\ Fluent6 = [x0 \in Response |-> FALSE]
/\ Fluent5 = [x0 \in Node |-> [x1 \in DbRequestId |-> FALSE]]
/\ Fluent10 = [x0 \in Request |-> [x1 \in DbRequestId |-> FALSE]]
/\ Fluent4 = [x0 \in Node |-> FALSE]
/\ Fluent3 = [x0 \in DbRequestId |-> FALSE]
/\ Fluent2 = [x0 \in DbRequestId |-> FALSE]
/\ Fluent1 = [x0 \in DbRequestId |-> FALSE]
/\ Fluent0 = [x0 \in DbRequestId |-> FALSE]
/\ cexTraceIdx = 0
/\ TraceConstraint

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_sent \in SUBSET((Node \X Response)))
/\ (response_received \in SUBSET((Node \X Response)))

Safety == (\A n \in Node, p \in Response : ((<<n,p>> \in response_received) => ResponseMatched(n,p)))
=============================================================================
