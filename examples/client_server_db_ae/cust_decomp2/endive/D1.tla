--------------------------- MODULE D1 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC, Randomization

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES db_request_sent, db_response_sent, t, Fluent12, Fluent11, Fluent14, Fluent13, Fluent16, Fluent15

vars == <<db_request_sent, db_response_sent, t, Fluent12, Fluent11, Fluent14, Fluent13, Fluent16, Fluent15>>

CandSep ==
\*/\ \A var0 \in DbRequestId : (Fluent0[var0]) => (Fluent1[var0])
\*/\ \A var0 \in DbRequestId : (Fluent2[var0]) => (Fluent3[var0])
\*/\ \A var0 \in Request : (Fluent5[var0]) => (Fluent4[var0])
\*/\ \A var0 \in Node : (Fluent6[var0]) => (Fluent7[var0])
\*/\ \A var0 \in Response : (Fluent9[var0]) => (Fluent8[var0])
/\ \A var0 \in DbRequestId : \E var1 \in Request : \A var2 \in Request : (Fluent11[var0][var2]) => (var1 = var2)
/\ \A var0 \in Request : \A var1 \in DbRequestId : (Fluent12[var0][var1]) => (Fluent11[var1][var0])
/\ \A var0 \in Node : \A var1 \in DbRequestId : (Fluent13[var1][var0]) => (Fluent14[var1][var0])
/\ \A var0 \in Response : \A var1 \in DbRequestId : (Fluent16[var1][var0]) => (Fluent15[var1][var0])

Symmetry == (((Permutations(Node) \cup Permutations(Request)) \cup Permutations(Response)) \cup Permutations(DbRequestId))

NoneWithId(i) == (\A n \in Node : (<<i,n>> \notin t))

ServerProcessRequest(n,r,i) ==
/\ NoneWithId(i)
/\ t' = (t \cup {<<i,n>>})
/\ db_request_sent' = (db_request_sent \cup {<<i,r>>})
/\ UNCHANGED <<db_response_sent>>
/\ Fluent11' = [Fluent11 EXCEPT ![i][r] = TRUE]
/\ Fluent14' = [Fluent14 EXCEPT ![i][n] = TRUE]
/\ UNCHANGED<<Fluent12, Fluent13, Fluent16, Fluent15>>

DbProcessRequest(i,r,p) ==
/\ (<<i,r>> \in db_request_sent)
/\ db_response_sent' = (db_response_sent \cup {<<i,p>>})
/\ UNCHANGED <<db_request_sent,t>>
/\ Fluent12' = [Fluent12 EXCEPT ![r][i] = TRUE]
/\ Fluent15' = [Fluent15 EXCEPT ![i][p] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent14, Fluent13, Fluent16>>

ServerProcessDbResponse(n,i,p) ==
/\ (<<i,p>> \in db_response_sent)
/\ (<<i,n>> \in t)
/\ UNCHANGED <<db_request_sent,db_response_sent,t>>
/\ Fluent13' = [Fluent13 EXCEPT ![i][n] = TRUE]
/\ Fluent16' = [Fluent16 EXCEPT ![i][p] = TRUE]
/\ UNCHANGED<<Fluent12, Fluent11, Fluent14, Fluent15>>

Next ==
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
\/ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
\/ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p))

Init ==
/\ db_request_sent = {}
/\ db_response_sent = {}
/\ t = {}
/\ Fluent12 = [ x0 \in Request |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent11 = [ x0 \in DbRequestId |-> [ x1 \in Request |-> FALSE]]
/\ Fluent14 = [ x0 \in DbRequestId |-> [ x1 \in Node |-> FALSE]]
/\ Fluent13 = [ x0 \in DbRequestId |-> [ x1 \in Node |-> FALSE]]
/\ Fluent16 = [ x0 \in DbRequestId |-> [ x1 \in Response |-> FALSE]]
/\ Fluent15 = [ x0 \in DbRequestId |-> [ x1 \in Response |-> FALSE]]

NextUnchanged == UNCHANGED vars


Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (db_request_sent \in SUBSET((DbRequestId \X Request)))
/\ (db_response_sent \in SUBSET((DbRequestId \X Response)))
/\ (t \in SUBSET((DbRequestId \X Node)))
/\ Fluent12 \in [Request -> [DbRequestId -> BOOLEAN]]
/\ Fluent11 \in [DbRequestId -> [Request -> BOOLEAN]]
/\ Fluent14 \in [DbRequestId -> [Node -> BOOLEAN]]
/\ Fluent13 \in [DbRequestId -> [Node -> BOOLEAN]]
/\ Fluent16 \in [DbRequestId -> [Response -> BOOLEAN]]
/\ Fluent15 \in [DbRequestId -> [Response -> BOOLEAN]]

RandNum1 == 5
RandNum2 == 7
TypeOKRandom ==
/\ db_request_sent \in RandomSubset(RandNum1, SUBSET((DbRequestId \X Request)))
/\ db_response_sent \in RandomSubset(RandNum1, SUBSET((DbRequestId \X Response)))
/\ t \in RandomSubset(RandNum1, SUBSET((DbRequestId \X Node)))
/\ Fluent12 \in RandomSubset(RandNum2, [Request -> [DbRequestId -> BOOLEAN]])
/\ Fluent11 \in RandomSubset(RandNum2, [DbRequestId -> [Request -> BOOLEAN]])
/\ Fluent14 \in RandomSubset(RandNum2, [DbRequestId -> [Node -> BOOLEAN]])
/\ Fluent13 \in RandomSubset(RandNum2, [DbRequestId -> [Node -> BOOLEAN]])
/\ Fluent16 \in RandomSubset(RandNum2, [DbRequestId -> [Response -> BOOLEAN]])
/\ Fluent15 \in RandomSubset(RandNum2, [DbRequestId -> [Response -> BOOLEAN]])


\* Endive output

Inv224_1_0_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (Fluent12[VARR2][VARID]) \/ (~(Fluent15[VARID][VARP]))
Inv191_1_1_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (Fluent11[VARID][VARR]) \/ (~(<<VARID,VARR>> \in db_request_sent))
Inv159_1_2_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (Fluent11[VARID][VARR2]) \/ ((NoneWithId(VARID)))
Inv497_1_3_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : ~(Fluent11[VARID][VARR]) \/ (~(NoneWithId(VARID)))
Inv302_1_0_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (Fluent14[VARID][VARI]) \/ (~(<<VARID,VARI>> \in t))
Inv343_1_1_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (Fluent15[VARID][VARP]) \/ (~(<<VARID,VARP>> \in db_response_sent))

\* The inductive invariant candidate.
\* Total duration: 123.00 secs.
\* python3 endive.py --spec benchmarks/D1 --seed 23 --ninvs 5000 --niters 3  4    510.90s user 9.95s system 423% cpu 2:03.07 total
IndAuto ==
  /\ CandSep
  /\ Inv224_1_0_def
  /\ Inv191_1_1_def
  /\ Inv159_1_2_def
  /\ Inv497_1_3_def
  /\ Inv302_1_0_def
  /\ Inv343_1_1_def

IndInv == TypeOK /\ IndAuto
IndInvRand == TypeOKRandom /\ IndAuto
IISpec == IndInvRand /\ [][Next]_vars

=============================================================================
