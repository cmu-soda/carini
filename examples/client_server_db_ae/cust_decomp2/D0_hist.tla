--------------------------- MODULE D0_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES Fluent13_62, Fluent20_47, Fluent12_62, Fluent15_60, Fluent17_41, request_sent, Fluent16_41, response_sent, Fluent14_60, match, response_received, Fluent21_47

vars == <<Fluent13_62, Fluent20_47, Fluent12_62, Fluent15_60, Fluent17_41, request_sent, Fluent16_41, response_sent, Fluent14_60, match, response_received, Fluent21_47>>

CandSep ==
/\ \A var0 \in DbRequestId : \A var1 \in Request : (Fluent14_60[var1][var0]) => (Fluent15_60[var1][var0])
/\ \A var0 \in Node : \A var1 \in DbRequestId : (Fluent12_62[var1][var0]) => (Fluent13_62[var1][var0])
/\ \A var0 \in Node : \A var1 \in DbRequestId : (Fluent16_41[var0][var1]) => (Fluent17_41[var0][var1])
/\ \A var0 \in Response : \A var1 \in DbRequestId : (Fluent21_47[var1][var0]) => (Fluent20_47[var1][var0])

Symmetry == (((Permutations(Node) \cup Permutations(Request)) \cup Permutations(Response)) \cup Permutations(DbRequestId))

ResponseMatched(n,p) ==
\E r \in Request :
/\ (<<n,r>> \in request_sent)
/\ (<<r,p>> \in match)

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<match,response_sent,response_received>>
/\ UNCHANGED<<Fluent13_62, Fluent20_47, Fluent12_62, Fluent15_60, Fluent17_41, Fluent16_41, Fluent14_60, Fluent21_47>>
/\ CandSep'

ServerProcessRequest(n,r,i) ==
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ Fluent13_62' = [[Fluent13_62 EXCEPT ![i] = [x0 \in Node |-> FALSE]] EXCEPT ![i][n] = TRUE]
/\ Fluent12_62' = [Fluent12_62 EXCEPT ![i][n] = TRUE]
/\ Fluent15_60' = [Fluent15_60 EXCEPT ![r][i] = TRUE]
/\ Fluent17_41' = [Fluent17_41 EXCEPT ![n][i] = TRUE]
/\ UNCHANGED<<Fluent20_47, Fluent16_41, Fluent14_60, Fluent21_47>>
/\ CandSep'

DbProcessRequest(i,r,p) ==
/\ (<<r,p>> \in match)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ Fluent20_47' = [Fluent20_47 EXCEPT ![i][p] = TRUE]
/\ Fluent14_60' = [Fluent14_60 EXCEPT ![r][i] = TRUE]
/\ UNCHANGED<<Fluent13_62, Fluent12_62, Fluent15_60, Fluent17_41, Fluent16_41, Fluent21_47>>
/\ CandSep'

ServerProcessDbResponse(n,i,p) ==
/\ response_sent' = (response_sent \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_received>>
/\ Fluent16_41' = [Fluent16_41 EXCEPT ![n][i] = TRUE]
/\ Fluent21_47' = [Fluent21_47 EXCEPT ![i][p] = TRUE]
/\ UNCHANGED<<Fluent13_62, Fluent20_47, Fluent12_62, Fluent15_60, Fluent17_41, Fluent14_60>>
/\ CandSep'

ReceiveResponse(n,p) ==
/\ (<<n,p>> \in response_sent)
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_sent>>
/\ UNCHANGED<<Fluent13_62, Fluent20_47, Fluent12_62, Fluent15_60, Fluent17_41, Fluent16_41, Fluent14_60, Fluent21_47>>
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
/\ Fluent13_62 = [ x0 \in DbRequestId |-> [ x1 \in Node |-> FALSE]]
/\ Fluent20_47 = [ x0 \in DbRequestId |-> [ x1 \in Response |-> FALSE]]
/\ Fluent12_62 = [ x0 \in DbRequestId |-> [ x1 \in Node |-> FALSE]]
/\ Fluent15_60 = [ x0 \in Request |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent17_41 = [ x0 \in Node |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent16_41 = [ x0 \in Node |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent14_60 = [ x0 \in Request |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent21_47 = [ x0 \in DbRequestId |-> [ x1 \in Response |-> FALSE]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_sent \in SUBSET((Node \X Response)))
/\ (response_received \in SUBSET((Node \X Response)))

Safety == (\A n \in Node, p \in Response : ((<<n,p>> \in response_received) => ResponseMatched(n,p)))
=============================================================================
