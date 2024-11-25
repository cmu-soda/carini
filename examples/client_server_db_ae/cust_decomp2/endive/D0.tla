--------------------------- MODULE D0 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC, Randomization

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES Fluent12, Fluent11, Fluent14, Fluent13, request_sent, response_sent, match, response_received, Fluent16, Fluent15

vars == <<Fluent12, Fluent11, Fluent14, Fluent13, request_sent, response_sent, match, response_received, Fluent16, Fluent15>>

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

ResponseMatched(n,p) ==
\E r \in Request :
/\ (<<n,r>> \in request_sent)
/\ (<<r,p>> \in match)

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<match,response_sent,response_received>>
/\ UNCHANGED<<Fluent12, Fluent11, Fluent14, Fluent13, Fluent16, Fluent15>>
/\ CandSep'

ServerProcessRequest(n,r,i) ==
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ Fluent11' = [Fluent11 EXCEPT ![i][r] = TRUE]
/\ Fluent14' = [Fluent14 EXCEPT ![i][n] = TRUE]
/\ UNCHANGED<<Fluent12, Fluent13, Fluent16, Fluent15>>
/\ CandSep'

DbProcessRequest(i,r,p) ==
/\ (<<r,p>> \in match)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ Fluent12' = [Fluent12 EXCEPT ![r][i] = TRUE]
/\ Fluent15' = [Fluent15 EXCEPT ![i][p] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent14, Fluent13, Fluent16>>
/\ CandSep'

ServerProcessDbResponse(n,i,p) ==
/\ response_sent' = (response_sent \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_received>>
/\ Fluent13' = [Fluent13 EXCEPT ![i][n] = TRUE]
/\ Fluent16' = [Fluent16 EXCEPT ![i][p] = TRUE]
/\ UNCHANGED<<Fluent12, Fluent11, Fluent14, Fluent15>>
/\ CandSep'

ReceiveResponse(n,p) ==
/\ (<<n,p>> \in response_sent)
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_sent>>
/\ UNCHANGED<<Fluent12, Fluent11, Fluent14, Fluent13, Fluent16, Fluent15>>
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
/\ Fluent12 = [ x0 \in Request |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent11 = [ x0 \in DbRequestId |-> [ x1 \in Request |-> FALSE]]
/\ Fluent14 = [ x0 \in DbRequestId |-> [ x1 \in Node |-> FALSE]]
/\ Fluent13 = [ x0 \in DbRequestId |-> [ x1 \in Node |-> FALSE]]
/\ Fluent16 = [ x0 \in DbRequestId |-> [ x1 \in Response |-> FALSE]]
/\ Fluent15 = [ x0 \in DbRequestId |-> [ x1 \in Response |-> FALSE]]

NextUnchanged == UNCHANGED vars

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_sent \in SUBSET((Node \X Response)))
/\ (response_received \in SUBSET((Node \X Response)))
/\ Fluent12 \in [Request -> [DbRequestId -> BOOLEAN]]
/\ Fluent11 \in [DbRequestId -> [Request -> BOOLEAN]]
/\ Fluent14 \in [DbRequestId -> [Node -> BOOLEAN]]
/\ Fluent13 \in [DbRequestId -> [Node -> BOOLEAN]]
/\ Fluent16 \in [DbRequestId -> [Response -> BOOLEAN]]
/\ Fluent15 \in [DbRequestId -> [Response -> BOOLEAN]]

RandNum == 5
TypeOKRandom ==
/\ match \in RandomSubset(RandNum, SUBSET (Request \X Response))
/\ request_sent \in RandomSubset(RandNum, SUBSET (Node \X Request))
/\ response_sent \in RandomSubset(RandNum, SUBSET (Node \X Response))
/\ response_received \in RandomSubset(RandNum, SUBSET (Node \X Response))
/\ Fluent12 \in RandomSubset(RandNum, [Request -> [DbRequestId -> BOOLEAN]])
/\ Fluent11 \in RandomSubset(RandNum, [DbRequestId -> [Request -> BOOLEAN]])
/\ Fluent14 \in RandomSubset(RandNum, [DbRequestId -> [Node -> BOOLEAN]])
/\ Fluent13 \in RandomSubset(RandNum, [DbRequestId -> [Node -> BOOLEAN]])
/\ Fluent16 \in RandomSubset(RandNum, [DbRequestId -> [Response -> BOOLEAN]])
/\ Fluent15 \in RandomSubset(RandNum, [DbRequestId -> [Response -> BOOLEAN]])

Safety == (\A n \in Node, p \in Response : ((<<n,p>> \in response_received) => ResponseMatched(n,p)))


\* Endive output

Inv689_1_0_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (ResponseMatched(VARI,VARP)) \/ (~(<<VARI,VARP>> \in response_sent))
Inv228_1_1_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (<<VARJ,VARP>> \in response_sent) \/ (~(<<VARJ,VARP>> \in response_received))
Inv421_1_2_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (Fluent11[VARID][VARR2]) \/ (~(Fluent15[VARID][VARP]))
Inv3533_2_3_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (ResponseMatched(VARI,VARP)) \/ (~(Fluent14[VARID][VARI]) \/ (~(Fluent16[VARID][VARP])))
Inv486_1_0_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (Fluent12[VARR2][VARID]) \/ (~(Fluent15[VARID][VARP]))
Inv388_1_1_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (<<VARR2,VARP>> \in match) \/ (~(Fluent15[VARID][VARP]))
Inv601_1_2_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (Fluent14[VARID][VARI]) \/ (~(Fluent13[VARID][VARI]))
Inv482_1_3_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (Fluent12[VARR2][VARID]) \/ (~(Fluent13[VARID][VARI]))
Inv658_1_4_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (Fluent15[VARID][VARP]) \/ (~(Fluent16[VARID][VARP]))
Inv420_1_5_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (Fluent11[VARID][VARR2]) \/ (~(Fluent14[VARID][VARI]))
Inv122_1_6_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (<<VARI,VARR2>> \in request_sent) \/ (~(Fluent14[VARID][VARI]))
Inv3554_2_7_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (ResponseMatched(VARI,VARP)) \/ (~(Fluent15[VARID][VARP])) \/ (~(Fluent14[VARID][VARI]))
Inv1008_2_8_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (<<VARI,VARR>> \in request_sent) \/ (~(Fluent11[VARID][VARR])) \/ (~(Fluent14[VARID][VARI]))
Inv1968_2_9_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (<<VARR,VARP>> \in match) \/ (~(Fluent11[VARID][VARR]) \/ (~(Fluent15[VARID][VARP])))

\* The inductive invariant candidate.
\* Total duration: 508.35 secs.
\* python3 endive.py --spec benchmarks/D0 --seed 22 --ninvs 5000 --niters 3  4    2437.53s user 21.60s system 483% cpu 8:28.43 total
IndAuto ==
  /\ Safety
  /\ Inv689_1_0_def
  /\ Inv228_1_1_def
  /\ Inv421_1_2_def
  /\ Inv3533_2_3_def
  /\ Inv486_1_0_def
  /\ Inv388_1_1_def
  /\ Inv601_1_2_def
  /\ Inv482_1_3_def
  /\ Inv658_1_4_def
  /\ Inv420_1_5_def
  /\ Inv122_1_6_def
  /\ Inv3554_2_7_def
  /\ Inv1008_2_8_def
  /\ Inv1968_2_9_def

IndInv == TypeOK /\ IndAuto
IndInvRand == TypeOKRandom /\ IndAuto
IISpec == IndInvRand /\ [][Next]_vars

=============================================================================
