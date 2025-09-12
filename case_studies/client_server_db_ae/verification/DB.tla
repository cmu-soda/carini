--------------------------- MODULE DB ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES db_request_sent, db_response_sent, t

Symmetry == Permutations(Node) \cup Permutations(Request) \cup Permutations(Response) \cup Permutations(DbRequestId)

vars == <<db_request_sent,db_response_sent, t>>

NoneWithId(i) == (\A n \in Node : (<<i,n>> \notin t))

ServerProcessRequest(n,r,i) ==
/\ NoneWithId(i)
/\ t' = (t \cup {<<i,n>>})
/\ db_request_sent' = (db_request_sent \cup {<<i,r>>})
/\ UNCHANGED <<db_response_sent>>

DbProcessRequest(i,r,p) ==
/\ (<<i,r>> \in db_request_sent)
/\ db_response_sent' = (db_response_sent \cup {<<i,p>>})
/\ UNCHANGED <<db_request_sent,t>>

ServerProcessDbResponse(n,i,p) ==
/\ (<<i,p>> \in db_response_sent)
/\ (<<i,n>> \in t)
/\ UNCHANGED <<db_request_sent,db_response_sent,t>>

Next ==
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
\/ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
\/ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p))

Init ==
/\ db_request_sent = {}
/\ db_response_sent = {}
/\ t = {}

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (db_request_sent \in SUBSET((DbRequestId \X Request)))
/\ (db_response_sent \in SUBSET((DbRequestId \X Response)))
/\ (t \in SUBSET((DbRequestId \X Node)))
=============================================================================
