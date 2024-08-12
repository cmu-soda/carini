--------------------------- MODULE D0_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES Fluent8, Fluent7, request_sent, Fluent6, response_sent, Fluent5, Fluent4, match, Fluent3, response_received, Fluent2, Fluent1, Fluent0, t

vars == <<Fluent8, Fluent7, request_sent, Fluent6, response_sent, Fluent5, Fluent4, match, Fluent3, response_received, Fluent2, Fluent1, Fluent0, t>>

CandSep ==
/\ \A var0 \in DbRequestId : (Fluent0[var0]) => (Fluent1[var0])
/\ \A var0 \in Response : (Fluent2[var0]) => (Fluent3[var0])
/\ \A var0 \in DbRequestId : \E var1 \in Request : Fluent4[var0][var1]
/\ \A var0 \in DbRequestId : (Fluent5[var0]) => (Fluent6[var0])
/\ \A var0 \in DbRequestId : \A var1 \in Response : (Fluent7[var1][var0]) => (Fluent8[var1][var0])

NoneWithId(i) == (\A n \in Node : (<<i,n>> \notin t))

ResponseMatched(n,p) ==
\E r \in Request :
/\ (<<n,r>> \in request_sent)
/\ (<<r,p>> \in match)

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<match,response_sent,response_received,t>>
/\ UNCHANGED<<Fluent8, Fluent7, Fluent6, Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

ServerProcessRequest(n,r,i) ==
/\ NoneWithId(i)
/\ t' = (t \cup {<<i,n>>})
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ Fluent6' = [Fluent6 EXCEPT![i] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT![i][r] = FALSE]
/\ Fluent1' = [Fluent1 EXCEPT![i] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT![i] = TRUE]
/\ UNCHANGED<<Fluent8, Fluent7, Fluent5, Fluent3, Fluent2>>
/\ CandSep'

DbProcessRequest(i,r,p) ==
/\ (<<r,p>> \in match)
/\ UNCHANGED <<match,request_sent,response_sent,response_received,t>>
/\ Fluent8' = [Fluent8 EXCEPT![p][i] = TRUE]
/\ Fluent5' = [Fluent5 EXCEPT![i] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT![i][r] = FALSE]
/\ Fluent3' = [Fluent3 EXCEPT![p] = FALSE]
/\ Fluent2' = [Fluent2 EXCEPT![p] = FALSE]
/\ Fluent1' = [Fluent1 EXCEPT![i] = FALSE]
/\ Fluent0' = [Fluent0 EXCEPT![i] = FALSE]
/\ UNCHANGED<<Fluent7, Fluent6>>
/\ CandSep'

ServerProcessDbResponse(n,i,p) ==
/\ (<<i,n>> \in t)
/\ response_sent' = (response_sent \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_received,t>>
/\ Fluent7' = [Fluent7 EXCEPT![p][i] = TRUE]
/\ Fluent3' = [Fluent3 EXCEPT![p] = FALSE]
/\ Fluent1' = [Fluent1 EXCEPT![i] = FALSE]
/\ UNCHANGED<<Fluent8, Fluent6, Fluent5, Fluent4, Fluent2, Fluent0>>
/\ CandSep'

ReceiveResponse(n,p) ==
/\ (<<n,p>> \in response_sent)
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_sent,t>>
/\ UNCHANGED<<Fluent8, Fluent7, Fluent6, Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
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
/\ t = {}
/\ Fluent8 = [ x0 \in Response |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent7 = [ x0 \in Response |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent6 = [ x0 \in DbRequestId |-> FALSE]
/\ Fluent5 = [ x0 \in DbRequestId |-> FALSE]
/\ Fluent4 = [ x0 \in DbRequestId |-> [ x1 \in Request |-> TRUE]]
/\ Fluent3 = [ x0 \in Response |-> TRUE]
/\ Fluent2 = [ x0 \in Response |-> TRUE]
/\ Fluent1 = [ x0 \in DbRequestId |-> TRUE]
/\ Fluent0 = [ x0 \in DbRequestId |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_sent \in SUBSET((Node \X Response)))
/\ (response_received \in SUBSET((Node \X Response)))
/\ (t \in SUBSET((DbRequestId \X Node)))

Safety == (\A n \in Node, p \in Response : ((<<n,p>> \in response_received) => ResponseMatched(n,p)))
=============================================================================
