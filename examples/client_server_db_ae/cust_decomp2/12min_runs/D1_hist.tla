--------------------------- MODULE D1_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES db_request_sent, Fluent12_60, t, Fluent8_63, Fluent13_60, Fluent9_63, Fluent15_46, db_response_sent, Fluent14_46, Fluent7_29

vars == <<db_request_sent, Fluent12_60, t, Fluent8_63, Fluent13_60, Fluent9_63, Fluent15_46, db_response_sent, Fluent14_46, Fluent7_29>>

CandSep ==
/\ \A var0 \in DbRequestId : \E var1 \in Request : \A var2 \in Node : (Fluent12_60[var2][var0]) => (Fluent13_60[var2][var0][var1])
/\ \A var0 \in DbRequestId : \E var1 \in Node : \A var2 \in Request : (Fluent8_63[var2][var0]) => (Fluent9_63[var2][var0][var1])
/\ \A var0 \in DbRequestId : \A var1 \in Node : \A var2 \in Response : (Fluent15_46[var2][var0][var1]) => (Fluent14_46[var2][var0])
/\ \A var0 \in DbRequestId : \E var1 \in Node : \A var2 \in Node : (Fluent7_29[var2][var0]) => (var2 = var1)

Symmetry == (((Permutations(Node) \cup Permutations(Request)) \cup Permutations(Response)) \cup Permutations(DbRequestId))

NoneWithId(i) == (\A n \in Node : (<<i,n>> \notin t))

ServerProcessRequest(n,r,i) ==
/\ NoneWithId(i)
/\ t' = (t \cup {<<i,n>>})
/\ db_request_sent' = (db_request_sent \cup {<<i,r>>})
/\ UNCHANGED <<db_response_sent>>
/\ Fluent13_60' = [Fluent13_60 EXCEPT ![n][i][r] = TRUE]
/\ Fluent9_63' = [Fluent9_63 EXCEPT ![r][i][n] = TRUE]
/\ Fluent7_29' = [Fluent7_29 EXCEPT ![n][i] = TRUE]
/\ UNCHANGED<<Fluent12_60, Fluent8_63, Fluent15_46, Fluent14_46>>

DbProcessRequest(i,r,p) ==
/\ (<<i,r>> \in db_request_sent)
/\ db_response_sent' = (db_response_sent \cup {<<i,p>>})
/\ UNCHANGED <<db_request_sent,t>>
/\ Fluent8_63' = [Fluent8_63 EXCEPT ![r][i] = TRUE]
/\ Fluent14_46' = [Fluent14_46 EXCEPT ![p][i] = TRUE]
/\ UNCHANGED<<Fluent12_60, Fluent13_60, Fluent9_63, Fluent15_46, Fluent7_29>>

ServerProcessDbResponse(n,i,p) ==
/\ (<<i,p>> \in db_response_sent)
/\ (<<i,n>> \in t)
/\ UNCHANGED <<db_request_sent,db_response_sent,t>>
/\ Fluent12_60' = [Fluent12_60 EXCEPT ![n][i] = TRUE]
/\ Fluent15_46' = [Fluent15_46 EXCEPT ![p][i][n] = TRUE]
/\ UNCHANGED<<Fluent8_63, Fluent13_60, Fluent9_63, Fluent14_46, Fluent7_29>>

Next ==
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
\/ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
\/ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p))

Init ==
/\ db_request_sent = {}
/\ db_response_sent = {}
/\ t = {}
/\ Fluent12_60 = [ x0 \in Node |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent8_63 = [ x0 \in Request |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent13_60 = [ x0 \in Node |-> [ x1 \in DbRequestId |-> [ x2 \in Request |-> FALSE]]]
/\ Fluent9_63 = [ x0 \in Request |-> [ x1 \in DbRequestId |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent15_46 = [ x0 \in Response |-> [ x1 \in DbRequestId |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent14_46 = [ x0 \in Response |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent7_29 = [ x0 \in Node |-> [ x1 \in DbRequestId |-> FALSE]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (db_request_sent \in SUBSET((DbRequestId \X Request)))
/\ (db_response_sent \in SUBSET((DbRequestId \X Response)))
/\ (t \in SUBSET((DbRequestId \X Node)))
=============================================================================
