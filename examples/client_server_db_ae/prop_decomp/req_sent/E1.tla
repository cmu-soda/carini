--------------------------- MODULE E1 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES db_request_sent, match, db_response_sent

vars == <<match,db_request_sent,db_response_sent>>

ServerProcessRequest(n,r,i) ==
/\ db_request_sent' = (db_request_sent \cup {<<i,r>>})
/\ UNCHANGED <<match,db_response_sent>>

DbProcessRequest(i,r,p) ==
/\ (<<i,r>> \in db_request_sent)
/\ (<<r,p>> \in match)
/\ db_response_sent' = (db_response_sent \cup {<<i,p>>})
/\ UNCHANGED <<match,db_request_sent>>

ServerProcessDbResponse(n,i,p) ==
/\ (<<i,p>> \in db_response_sent)
/\ UNCHANGED <<match,db_request_sent,db_response_sent>>

Next ==
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
\/ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
\/ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p))

Init ==
/\ (match \in SUBSET((Request \X Response)))
/\ db_request_sent = {}
/\ db_response_sent = {}

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (db_request_sent \in SUBSET((DbRequestId \X Request)))
/\ (db_response_sent \in SUBSET((DbRequestId \X Response)))
=============================================================================
