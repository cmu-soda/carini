---- MODULE T1 ----

EXTENDS TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLE response_sent

VARIABLE db_request_sent
VARIABLE db_response_sent

VARIABLE t

vars == <<response_sent,db_request_sent,db_response_sent,t>>

NoneWithId(i) == \A n \in Node : <<i,n>> \notin t

ServerProcessRequest(n,r,i) ==
    /\ NoneWithId(i)
    /\ t' = t \cup {<<i,n>>}
    /\ db_request_sent' = db_request_sent \cup {<<i,r>>}
    /\ UNCHANGED <<response_sent,db_response_sent>>

DbProcessRequest(i,r,p) ==
    /\ <<i,r>> \in db_request_sent
    /\ db_response_sent' = db_response_sent \cup {<<i,p>>}
    /\ UNCHANGED <<response_sent,db_request_sent,t>>

ServerProcessDbResponse(n,i,p) ==
    /\ <<i,p>> \in db_response_sent
    /\ <<i,n>> \in t
    /\ response_sent' = response_sent \cup {<<n,p>>}
    /\ UNCHANGED <<db_request_sent,db_response_sent,t>>

ReceiveResponse(n,p) ==
    /\ <<n,p>> \in response_sent
    /\ UNCHANGED <<response_sent,db_request_sent,db_response_sent,t>>

Next ==
    \/ \E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)
    \/ \E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)
    \/ \E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)
    \/ \E n \in Node, p \in Response : ReceiveResponse(n,p)

Init ==
    /\ response_sent = {}
    /\ db_request_sent = {}
    /\ db_response_sent = {}
    /\ t = {}

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ response_sent \in SUBSET (Node \X Response)
    /\ db_request_sent \in SUBSET (DbRequestId \X Request)
    /\ db_response_sent \in SUBSET (DbRequestId \X Response)
    /\ t \in SUBSET (DbRequestId \X Node)

====
