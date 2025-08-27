--------------------------- MODULE D1_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES db_request_sent, Fluent13_62, Fluent20_47, Fluent12_62, t, Fluent15_60, Fluent17_41, Fluent16_41, Fluent14_60, db_response_sent, Fluent21_47

vars == <<db_request_sent, Fluent13_62, Fluent20_47, Fluent12_62, t, Fluent15_60, Fluent17_41, Fluent16_41, Fluent14_60, db_response_sent, Fluent21_47>>

CandSep ==
/\ \A var0 \in DbRequestId : \A var1 \in Request : (Fluent14_60[var1][var0]) => (Fluent15_60[var1][var0])
/\ \A var0 \in Node : \A var1 \in DbRequestId : (Fluent12_62[var1][var0]) => (Fluent13_62[var1][var0])
/\ \A var0 \in Node : \A var1 \in DbRequestId : (Fluent16_41[var0][var1]) => (Fluent17_41[var0][var1])
/\ \A var0 \in Response : \A var1 \in DbRequestId : (Fluent21_47[var1][var0]) => (Fluent20_47[var1][var0])

Symmetry == (((Permutations(Node) \cup Permutations(Request)) \cup Permutations(Response)) \cup Permutations(DbRequestId))

NoneWithId(i) == (\A n \in Node : (<<i,n>> \notin t))

ServerProcessRequest(n,r,i) ==
/\ NoneWithId(i)
/\ t' = (t \cup {<<i,n>>})
/\ db_request_sent' = (db_request_sent \cup {<<i,r>>})
/\ UNCHANGED <<db_response_sent>>
/\ Fluent13_62' = [[Fluent13_62 EXCEPT ![i] = [x0 \in Node |-> FALSE]] EXCEPT ![i][n] = TRUE]
/\ Fluent12_62' = [Fluent12_62 EXCEPT ![i][n] = TRUE]
/\ Fluent15_60' = [Fluent15_60 EXCEPT ![r][i] = TRUE]
/\ Fluent17_41' = [Fluent17_41 EXCEPT ![n][i] = TRUE]
/\ UNCHANGED<<Fluent20_47, Fluent16_41, Fluent14_60, Fluent21_47>>

DbProcessRequest(i,r,p) ==
/\ (<<i,r>> \in db_request_sent)
/\ db_response_sent' = (db_response_sent \cup {<<i,p>>})
/\ UNCHANGED <<db_request_sent,t>>
/\ Fluent20_47' = [Fluent20_47 EXCEPT ![i][p] = TRUE]
/\ Fluent14_60' = [Fluent14_60 EXCEPT ![r][i] = TRUE]
/\ UNCHANGED<<Fluent13_62, Fluent12_62, Fluent15_60, Fluent17_41, Fluent16_41, Fluent21_47>>

ServerProcessDbResponse(n,i,p) ==
/\ (<<i,p>> \in db_response_sent)
/\ (<<i,n>> \in t)
/\ UNCHANGED <<db_request_sent,db_response_sent,t>>
/\ Fluent16_41' = [Fluent16_41 EXCEPT ![n][i] = TRUE]
/\ Fluent21_47' = [Fluent21_47 EXCEPT ![i][p] = TRUE]
/\ UNCHANGED<<Fluent13_62, Fluent20_47, Fluent12_62, Fluent15_60, Fluent17_41, Fluent14_60>>

Next ==
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
\/ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
\/ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p))

Init ==
/\ db_request_sent = {}
/\ db_response_sent = {}
/\ t = {}
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
/\ (db_request_sent \in SUBSET((DbRequestId \X Request)))
/\ (db_response_sent \in SUBSET((DbRequestId \X Response)))
/\ (t \in SUBSET((DbRequestId \X Node)))
=============================================================================
