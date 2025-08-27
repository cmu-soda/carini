--------------------------- MODULE D0_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES Fluent12_60, request_sent, Fluent8_63, response_sent, Fluent13_60, match, response_received, Fluent9_63, Fluent15_46, Fluent14_46, Fluent7_29

vars == <<Fluent12_60, request_sent, Fluent8_63, response_sent, Fluent13_60, match, response_received, Fluent9_63, Fluent15_46, Fluent14_46, Fluent7_29>>

CandSep ==
/\ \A var0 \in DbRequestId : \E var1 \in Request : \A var2 \in Node : (Fluent12_60[var2][var0]) => (Fluent13_60[var2][var0][var1])
/\ \A var0 \in DbRequestId : \E var1 \in Node : \A var2 \in Request : (Fluent8_63[var2][var0]) => (Fluent9_63[var2][var0][var1])
/\ \A var0 \in DbRequestId : \A var1 \in Node : \A var2 \in Response : (Fluent15_46[var2][var0][var1]) => (Fluent14_46[var2][var0])
/\ \A var0 \in DbRequestId : \E var1 \in Node : \A var2 \in Node : (Fluent7_29[var2][var0]) => (var2 = var1)

Symmetry == (((Permutations(Node) \cup Permutations(Request)) \cup Permutations(Response)) \cup Permutations(DbRequestId))

ResponseMatched(n,p) ==
\E r \in Request :
/\ (<<n,r>> \in request_sent)
/\ (<<r,p>> \in match)

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<match,response_sent,response_received>>
/\ UNCHANGED<<Fluent12_60, Fluent8_63, Fluent13_60, Fluent9_63, Fluent15_46, Fluent14_46, Fluent7_29>>
/\ CandSep'

ServerProcessRequest(n,r,i) ==
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ Fluent13_60' = [Fluent13_60 EXCEPT ![n][i][r] = TRUE]
/\ Fluent9_63' = [Fluent9_63 EXCEPT ![r][i][n] = TRUE]
/\ Fluent7_29' = [Fluent7_29 EXCEPT ![n][i] = TRUE]
/\ UNCHANGED<<Fluent12_60, Fluent8_63, Fluent15_46, Fluent14_46>>
/\ CandSep'

DbProcessRequest(i,r,p) ==
/\ (<<r,p>> \in match)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ Fluent8_63' = [Fluent8_63 EXCEPT ![r][i] = TRUE]
/\ Fluent14_46' = [Fluent14_46 EXCEPT ![p][i] = TRUE]
/\ UNCHANGED<<Fluent12_60, Fluent13_60, Fluent9_63, Fluent15_46, Fluent7_29>>
/\ CandSep'

ServerProcessDbResponse(n,i,p) ==
/\ response_sent' = (response_sent \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_received>>
/\ Fluent12_60' = [Fluent12_60 EXCEPT ![n][i] = TRUE]
/\ Fluent15_46' = [Fluent15_46 EXCEPT ![p][i][n] = TRUE]
/\ UNCHANGED<<Fluent8_63, Fluent13_60, Fluent9_63, Fluent14_46, Fluent7_29>>
/\ CandSep'

ReceiveResponse(n,p) ==
/\ (<<n,p>> \in response_sent)
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_sent>>
/\ UNCHANGED<<Fluent12_60, Fluent8_63, Fluent13_60, Fluent9_63, Fluent15_46, Fluent14_46, Fluent7_29>>
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
/\ Fluent12_60 = [ x0 \in Node |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent8_63 = [ x0 \in Request |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent13_60 = [ x0 \in Node |-> [ x1 \in DbRequestId |-> [ x2 \in Request |-> FALSE]]]
/\ Fluent9_63 = [ x0 \in Request |-> [ x1 \in DbRequestId |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent15_46 = [ x0 \in Response |-> [ x1 \in DbRequestId |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent14_46 = [ x0 \in Response |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent7_29 = [ x0 \in Node |-> [ x1 \in DbRequestId |-> FALSE]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_sent \in SUBSET((Node \X Response)))
/\ (response_received \in SUBSET((Node \X Response)))

Safety == (\A n \in Node, p \in Response : ((<<n,p>> \in response_received) => ResponseMatched(n,p)))
=============================================================================
