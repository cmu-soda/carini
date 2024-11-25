--------------------------- MODULE T1_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES db_request_sent, Fluent11, Fluent9, t, response_sent, Fluent10, db_response_sent

vars == <<db_request_sent, Fluent11, Fluent9, t, response_sent, Fluent10, db_response_sent>>

CandSep ==
\A var0 \in Request : \A var1 \in Node : (Fluent10[var0]) => ((Fluent11[var1]) => (Fluent9[var0][var1]))

NoneWithId(i) == (\A n \in Node : (<<i,n>> \notin t))

ServerProcessRequest(n,r,i) ==
/\ NoneWithId(i)
/\ t' = (t \cup {<<i,n>>})
/\ db_request_sent' = (db_request_sent \cup {<<i,r>>})
/\ UNCHANGED <<response_sent,db_response_sent>>
/\ Fluent9' = [Fluent9 EXCEPT ![r][n] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent10>>

DbProcessRequest(i,r,p) ==
/\ (<<i,r>> \in db_request_sent)
/\ db_response_sent' = (db_response_sent \cup {<<i,p>>})
/\ UNCHANGED <<response_sent,db_request_sent,t>>
/\ Fluent10' = [Fluent10 EXCEPT ![r] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent9>>

ServerProcessDbResponse(n,i,p) ==
/\ (<<i,p>> \in db_response_sent)
/\ (<<i,n>> \in t)
/\ response_sent' = (response_sent \cup {<<n,p>>})
/\ UNCHANGED <<db_request_sent,db_response_sent,t>>
/\ UNCHANGED<<Fluent11, Fluent9, Fluent10>>

ReceiveResponse(n,p) ==
/\ (<<n,p>> \in response_sent)
/\ UNCHANGED <<response_sent,db_request_sent,db_response_sent,t>>
/\ Fluent11' = [Fluent11 EXCEPT ![n] = TRUE]
/\ UNCHANGED<<Fluent9, Fluent10>>

Next ==
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
\/ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
\/ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p))
\/ (\E n \in Node, p \in Response : ReceiveResponse(n,p))

Init ==
/\ response_sent = {}
/\ db_request_sent = {}
/\ db_response_sent = {}
/\ t = {}
/\ Fluent11 = [ x0 \in Node |-> FALSE]
/\ Fluent9 = [ x0 \in Request |-> [ x1 \in Node |-> FALSE]]
/\ Fluent10 = [ x0 \in Request |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (response_sent \in SUBSET((Node \X Response)))
/\ (db_request_sent \in SUBSET((DbRequestId \X Request)))
/\ (db_response_sent \in SUBSET((DbRequestId \X Response)))
/\ (t \in SUBSET((DbRequestId \X Node)))
=============================================================================
