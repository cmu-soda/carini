--------------------------- MODULE D1_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES db_request_sent, Fluent12, Fluent11, Fluent9, Fluent8, Fluent13, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, db_response_sent, t

vars == <<db_request_sent, Fluent12, Fluent11, Fluent9, Fluent8, Fluent13, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, db_response_sent, t>>

CandSep ==
/\ \A var0 \in DbRequestId : (Fluent0[var0]) => (Fluent1[var0])
/\ \A var0 \in DbRequestId : (Fluent2[var0]) => (Fluent3[var0])
/\ \A var0 \in DbRequestId : \A var1 \in Response : (Fluent4[var0][var1]) => (Fluent5[var0][var1])
/\ \A var0 \in DbRequestId : \A var1 \in Node : (Fluent7[var1][var0]) => (Fluent6[var0][var1])
/\ \A var0 \in DbRequestId : \A var1 \in Request : (Fluent8[var0][var1]) => (Fluent9[var1])
/\ \A var0 \in DbRequestId : \A var1 \in Request : (Fluent10[var1][var0]) => (Fluent11[var0][var1])
/\ \A var0 \in DbRequestId : \E var1 \in Node : \A var2 \in Request : (Fluent13[var2][var0]) => (Fluent12[var0][var1][var2])

Symmetry == (((Permutations(Node) \cup Permutations(Request)) \cup Permutations(Response)) \cup Permutations(DbRequestId))

NoneWithId(i) == (\A n \in Node : (<<i,n>> \notin t))

ServerProcessRequest(n,r,i) ==
/\ NoneWithId(i)
/\ t' = (t \cup {<<i,n>>})
/\ db_request_sent' = (db_request_sent \cup {<<i,r>>})
/\ UNCHANGED <<db_response_sent>>
/\ Fluent12' = [Fluent12 EXCEPT ![i][n][r] = TRUE]
/\ Fluent11' = [Fluent11 EXCEPT ![i][r] = TRUE]
/\ Fluent9' = [Fluent9 EXCEPT ![r] = TRUE]
/\ Fluent13' = [Fluent13 EXCEPT ![r][i] = TRUE]
/\ Fluent6' = [Fluent6 EXCEPT ![i][n] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent8, Fluent7, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent0>>

DbProcessRequest(i,r,p) ==
/\ (<<i,r>> \in db_request_sent)
/\ db_response_sent' = (db_response_sent \cup {<<i,p>>})
/\ UNCHANGED <<db_request_sent,t>>
/\ Fluent8' = [Fluent8 EXCEPT ![i][r] = TRUE]
/\ Fluent5' = [Fluent5 EXCEPT ![i][p] = TRUE]
/\ Fluent10' = [Fluent10 EXCEPT ![r][i] = TRUE]
/\ Fluent3' = [Fluent3 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent12, Fluent11, Fluent9, Fluent13, Fluent7, Fluent6, Fluent4, Fluent2, Fluent1, Fluent0>>

ServerProcessDbResponse(n,i,p) ==
/\ (<<i,p>> \in db_response_sent)
/\ (<<i,n>> \in t)
/\ UNCHANGED <<db_request_sent,db_response_sent,t>>
/\ Fluent7' = [Fluent7 EXCEPT ![n][i] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT ![i][p] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT ![i] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent12, Fluent11, Fluent9, Fluent8, Fluent13, Fluent6, Fluent5, Fluent10, Fluent3, Fluent1>>

Next ==
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
\/ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
\/ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p))

Init ==
/\ db_request_sent = {}
/\ db_response_sent = {}
/\ t = {}
/\ Fluent12 = [ x0 \in DbRequestId |-> [ x1 \in Node |-> [ x2 \in Request |-> FALSE]]]
/\ Fluent11 = [ x0 \in DbRequestId |-> [ x1 \in Request |-> FALSE]]
/\ Fluent9 = [ x0 \in Request |-> FALSE]
/\ Fluent8 = [ x0 \in DbRequestId |-> [ x1 \in Request |-> FALSE]]
/\ Fluent13 = [ x0 \in Request |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent7 = [ x0 \in Node |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent6 = [ x0 \in DbRequestId |-> [ x1 \in Node |-> FALSE]]
/\ Fluent5 = [ x0 \in DbRequestId |-> [ x1 \in Response |-> FALSE]]
/\ Fluent10 = [ x0 \in Request |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent4 = [ x0 \in DbRequestId |-> [ x1 \in Response |-> FALSE]]
/\ Fluent3 = [ x0 \in DbRequestId |-> FALSE]
/\ Fluent2 = [ x0 \in DbRequestId |-> FALSE]
/\ Fluent1 = [ x0 \in DbRequestId |-> FALSE]
/\ Fluent0 = [ x0 \in DbRequestId |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (db_request_sent \in SUBSET((DbRequestId \X Request)))
/\ (db_response_sent \in SUBSET((DbRequestId \X Response)))
/\ (t \in SUBSET((DbRequestId \X Node)))
=============================================================================
