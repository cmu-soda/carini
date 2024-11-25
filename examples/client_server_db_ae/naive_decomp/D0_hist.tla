--------------------------- MODULE D0_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES Fluent8, Fluent7, request_sent, Fluent6, Fluent5, Fluent4, match, Fluent3, response_received, Fluent2, Fluent1, Fluent0

vars == <<Fluent8, Fluent7, request_sent, Fluent6, Fluent5, Fluent4, match, Fluent3, response_received, Fluent2, Fluent1, Fluent0>>

CandSep ==
/\ \A var0 \in Response : (Fluent0[var0]) => (Fluent1[var0])
/\ \A var0 \in Request : (Fluent2[var0]) => (Fluent3[var0])
/\ \A var0 \in Node : (Fluent5[var0]) => (Fluent4[var0])
/\ \A var0 \in DbRequestId : \E var1 \in Node : ~(Fluent6[var1][var0])
/\ \A var0 \in Request : \A var1 \in DbRequestId : (Fluent8[var0][var1]) => (Fluent7[var1][var0])

ResponseMatched(n,p) ==
\E r \in Request :
/\ (<<n,r>> \in request_sent)
/\ (<<r,p>> \in match)

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<match,response_received>>
/\ UNCHANGED<<Fluent8, Fluent7, Fluent6, Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

ServerProcessRequest(n,r,i) ==
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<match,request_sent,response_received>>
/\ Fluent7' = [Fluent7 EXCEPT ![i][r] = TRUE]
/\ Fluent6' = [Fluent6 EXCEPT ![n][i] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT ![n] = TRUE]
/\ Fluent3' = [Fluent3 EXCEPT ![r] = TRUE]
/\ UNCHANGED<<Fluent8, Fluent5, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

DbProcessRequest(i,r,p) ==
/\ (<<r,p>> \in match)
/\ UNCHANGED <<match,request_sent,response_received>>
/\ Fluent8' = [Fluent8 EXCEPT ![r][i] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT ![r] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT ![p] = TRUE]
/\ UNCHANGED<<Fluent7, Fluent6, Fluent5, Fluent4, Fluent3, Fluent0>>
/\ CandSep'

ReceiveResponse(n,p) ==
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent>>
/\ Fluent5' = [Fluent5 EXCEPT ![n] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![p] = TRUE]
/\ UNCHANGED<<Fluent8, Fluent7, Fluent6, Fluent4, Fluent3, Fluent2, Fluent1>>
/\ CandSep'

Next ==
\/ (\E n \in Node, r \in Request : NewRequest(n,r))
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
\/ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
\/ (\E n \in Node, p \in Response : ReceiveResponse(n,p))

Init ==
/\ (match \in SUBSET((Request \X Response)))
/\ request_sent = {}
/\ response_received = {}
/\ Fluent8 = [ x0 \in Request |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent7 = [ x0 \in DbRequestId |-> [ x1 \in Request |-> FALSE]]
/\ Fluent6 = [ x0 \in Node |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent5 = [ x0 \in Node |-> FALSE]
/\ Fluent4 = [ x0 \in Node |-> FALSE]
/\ Fluent3 = [ x0 \in Request |-> FALSE]
/\ Fluent2 = [ x0 \in Request |-> FALSE]
/\ Fluent1 = [ x0 \in Response |-> FALSE]
/\ Fluent0 = [ x0 \in Response |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_received \in SUBSET((Node \X Response)))

Safety == (\A n \in Node, p \in Response : ((<<n,p>> \in response_received) => ResponseMatched(n,p)))
=============================================================================
