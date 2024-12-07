--------------------------- MODULE D0_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES Fluent12, Fluent11, Fluent9, Fluent14, Fluent8, Fluent13, Fluent7, request_sent, Fluent6, response_sent, Fluent5, Fluent10, Fluent4, match, Fluent3, response_received, Fluent2, Fluent1, Fluent0

vars == <<Fluent12, Fluent11, Fluent9, Fluent14, Fluent8, Fluent13, Fluent7, request_sent, Fluent6, response_sent, Fluent5, Fluent10, Fluent4, match, Fluent3, response_received, Fluent2, Fluent1, Fluent0>>

CandSep ==
/\ \A var0 \in DbRequestId : (Fluent1[var0]) => (Fluent0[var0])
/\ \A var0 \in DbRequestId : (Fluent2[var0]) => (Fluent3[var0])
/\ \A var0 \in DbRequestId : \A var1 \in Node : (Fluent5[var1][var0]) => (Fluent4[var1])
/\ \A var0 \in Response : (Fluent6[var0]) => (Fluent7[var0])
/\ \A var0 \in DbRequestId : \E var1 \in DbRequestId : \A var2 \in Request : (Fluent8[var2][var0]) => (Fluent9[var1][var2])
/\ \A var0 \in DbRequestId : \E var1 \in Request : \A var2 \in Request : (Fluent10[var2][var0]) => (var1 = var2)
/\ \A var0 \in Request : \A var1 \in DbRequestId : (Fluent11[var1][var0]) => (Fluent12[var1][var0])
/\ \A var0 \in DbRequestId : \A var1 \in Node : (Fluent14[var0][var1]) => (Fluent13[var1][var0])

Symmetry == (((Permutations(Node) \cup Permutations(Request)) \cup Permutations(Response)) \cup Permutations(DbRequestId))

ResponseMatched(n,p) ==
\E r \in Request :
/\ (<<n,r>> \in request_sent)
/\ (<<r,p>> \in match)

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<match,response_sent,response_received>>
/\ UNCHANGED<<Fluent12, Fluent11, Fluent9, Fluent14, Fluent8, Fluent13, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

ServerProcessRequest(n,r,i) ==
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ Fluent12' = [Fluent12 EXCEPT ![i][r] = TRUE]
/\ Fluent9' = [Fluent9 EXCEPT ![i][r] = TRUE]
/\ Fluent13' = [Fluent13 EXCEPT ![n][i] = TRUE]
/\ Fluent10' = [Fluent10 EXCEPT ![r][i] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT ![n] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent14, Fluent8, Fluent7, Fluent6, Fluent5, Fluent3, Fluent2, Fluent1>>
/\ CandSep'

DbProcessRequest(i,r,p) ==
/\ (<<r,p>> \in match)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ Fluent11' = [Fluent11 EXCEPT ![i][r] = TRUE]
/\ Fluent8' = [Fluent8 EXCEPT ![r][i] = TRUE]
/\ Fluent7' = [Fluent7 EXCEPT ![p] = TRUE]
/\ Fluent3' = [Fluent3 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent12, Fluent9, Fluent14, Fluent13, Fluent6, Fluent5, Fluent10, Fluent4, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

ServerProcessDbResponse(n,i,p) ==
/\ response_sent' = (response_sent \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_received>>
/\ Fluent14' = [Fluent14 EXCEPT ![i][n] = TRUE]
/\ Fluent6' = [Fluent6 EXCEPT ![p] = TRUE]
/\ Fluent5' = [Fluent5 EXCEPT ![n][i] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT ![i] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent12, Fluent11, Fluent9, Fluent8, Fluent13, Fluent7, Fluent10, Fluent4, Fluent3, Fluent0>>
/\ CandSep'

ReceiveResponse(n,p) ==
/\ (<<n,p>> \in response_sent)
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_sent>>
/\ UNCHANGED<<Fluent12, Fluent11, Fluent9, Fluent14, Fluent8, Fluent13, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

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
/\ Fluent12 = [ x0 \in DbRequestId |-> [ x1 \in Request |-> FALSE]]
/\ Fluent11 = [ x0 \in DbRequestId |-> [ x1 \in Request |-> FALSE]]
/\ Fluent9 = [ x0 \in DbRequestId |-> [ x1 \in Request |-> FALSE]]
/\ Fluent14 = [ x0 \in DbRequestId |-> [ x1 \in Node |-> FALSE]]
/\ Fluent8 = [ x0 \in Request |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent13 = [ x0 \in Node |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent7 = [ x0 \in Response |-> FALSE]
/\ Fluent6 = [ x0 \in Response |-> FALSE]
/\ Fluent5 = [ x0 \in Node |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent10 = [ x0 \in Request |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent4 = [ x0 \in Node |-> FALSE]
/\ Fluent3 = [ x0 \in DbRequestId |-> FALSE]
/\ Fluent2 = [ x0 \in DbRequestId |-> FALSE]
/\ Fluent1 = [ x0 \in DbRequestId |-> FALSE]
/\ Fluent0 = [ x0 \in DbRequestId |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_sent \in SUBSET((Node \X Response)))
/\ (response_received \in SUBSET((Node \X Response)))

Safety == (\A n \in Node, p \in Response : ((<<n,p>> \in response_received) => ResponseMatched(n,p)))
=============================================================================
