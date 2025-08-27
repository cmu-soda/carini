--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS req3, req2, n1, n2, n3, req1, Node, DbRequestId, Request, Response, resp2, id2, resp1, id1

VARIABLES err, request_sent, response_sent, match, response_received, cexTraceIdx, Fluent7_29

vars == <<err, request_sent, response_sent, match, response_received, cexTraceIdx, Fluent7_29>>

NoErr == err = FALSE

CandSep == (\A var0 \in DbRequestId : (\E var1 \in Node : (\A var2 \in Node : (Fluent7_29[var2][var0] => var2 = var1))))

Symmetry == (((Permutations(Node) \cup Permutations(Request)) \cup Permutations(Response)) \cup Permutations(DbRequestId))

ResponseMatched(n,p) ==
\E r \in Request :
/\ (<<n,r>> \in request_sent)
/\ (<<r,p>> \in match)

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<match,response_sent,response_received>>
/\ UNCHANGED <<Fluent7_29>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

ServerProcessRequest(n,r,i) ==
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ Fluent7_29' = [Fluent7_29 EXCEPT![n][i] = TRUE]
/\ UNCHANGED <<>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

DbProcessRequest(i,r,p) ==
/\ (<<r,p>> \in match)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ UNCHANGED <<Fluent7_29>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

ServerProcessDbResponse(n,i,p) ==
/\ response_sent' = (response_sent \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_received>>
/\ UNCHANGED <<Fluent7_29>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

ReceiveResponse(n,p) ==
/\ (<<n,p>> \in response_sent)
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_sent>>
/\ UNCHANGED <<Fluent7_29>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

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
/\ Fluent7_29 = [x0 \in Node |-> [x1 \in DbRequestId |-> FALSE]]
/\ cexTraceIdx = 0
/\ err = FALSE

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_sent \in SUBSET((Node \X Response)))
/\ (response_received \in SUBSET((Node \X Response)))

Safety == (\A n \in Node, p \in Response : ((<<n,p>> \in response_received) => ResponseMatched(n,p)))

TraceConstraint ==
/\ cexTraceIdx = 0 => NewRequest(n1,req1) /\ err' = err
/\ cexTraceIdx = 1 => NewRequest(n2,req2) /\ err' = err
/\ cexTraceIdx = 2 => ServerProcessRequest(n1,req1,id1) /\ err' = err
/\ cexTraceIdx = 3 => ServerProcessRequest(n2,req2,id2) /\ err' = err
/\ cexTraceIdx = 4 => DbProcessRequest(id1,req1,resp1) /\ err' = err
/\ cexTraceIdx = 5 => DbProcessRequest(id2,req2,resp2) /\ err' = err
/\ cexTraceIdx = 6 => ServerProcessDbResponse(n2,id2,resp1) /\ err' = err
/\ cexTraceIdx = 7 => ReceiveResponse(n2,resp1) /\ err' = TRUE
/\ cexTraceIdx >= 8 => FALSE

InternalAction == UNCHANGED<<cexTraceIdx,err>>

TraceConstraintSpec == Init /\ [][Next /\ (TraceConstraint \/ InternalAction)]_vars
=============================================================================
