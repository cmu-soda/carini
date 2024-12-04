--------------------------------- MODULE D0 ---------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

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

Safety == (\A n \in Node, p \in Response : ((<<n,p>> \in response_received) => ResponseMatched(n,p)))


\* Endive output

Inv689_1_0_def == \A VARI \in Node : \A VARP \in Response : (ResponseMatched(VARI,VARP)) \/ (~(<<VARI,VARP>> \in response_sent))
Inv228_1_1_def == \A VARJ \in Node : \A VARP \in Response : (<<VARJ,VARP>> \in response_sent) \/ (~(<<VARJ,VARP>> \in response_received))
Inv421_1_2_def == \A VARID \in DbRequestId : \A VARP \in Response : \E VARR2 \in Request : (Fluent11[VARID][VARR2]) \/ (~(Fluent15[VARID][VARP]))
Inv3533_2_3_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARP \in Response : (ResponseMatched(VARI,VARP)) \/ (~(Fluent14[VARID][VARI]) \/ (~(Fluent16[VARID][VARP])))
Inv486_1_0_def == \A VARID \in DbRequestId : \A VARP \in Response : \E VARR2 \in Request : (Fluent12[VARR2][VARID]) \/ (~(Fluent15[VARID][VARP]))
Inv388_1_1_def == \A VARID \in DbRequestId : \A VARP \in Response : \E VARR2 \in Request : (<<VARR2,VARP>> \in match) \/ (~(Fluent15[VARID][VARP]))
Inv601_1_2_def == \A VARI \in Node : \A VARID \in DbRequestId : (Fluent14[VARID][VARI]) \/ (~(Fluent13[VARID][VARI]))
Inv482_1_3_def == \A VARI \in Node : \A VARID \in DbRequestId : \E VARR2 \in Request : (Fluent12[VARR2][VARID]) \/ (~(Fluent13[VARID][VARI]))
Inv658_1_4_def == \A VARID \in DbRequestId : \A VARP \in Response : (Fluent15[VARID][VARP]) \/ (~(Fluent16[VARID][VARP]))
Inv420_1_5_def == \A VARI \in Node : \A VARID \in DbRequestId : \E VARR2 \in Request : (Fluent11[VARID][VARR2]) \/ (~(Fluent14[VARID][VARI]))
Inv122_1_6_def == \A VARI \in Node : \A VARID \in DbRequestId : \E VARR2 \in Request : (<<VARI,VARR2>> \in request_sent) \/ (~(Fluent14[VARID][VARI]))
Inv3554_2_7_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARP \in Response : (ResponseMatched(VARI,VARP)) \/ (~(Fluent15[VARID][VARP])) \/ (~(Fluent14[VARID][VARI]))
Inv1008_2_8_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : (<<VARI,VARR>> \in request_sent) \/ (~(Fluent11[VARID][VARR])) \/ (~(Fluent14[VARID][VARI]))
Inv1968_2_9_def == \A VARID \in DbRequestId : \A VARR \in Request : \A VARP \in Response : (<<VARR,VARP>> \in match) \/ (~(Fluent11[VARID][VARR]) \/ (~(Fluent15[VARID][VARP])))

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

IndInv == TypeOK /\ IndAuto /\ CandSep
IISpec == IndInv /\ [][Next]_vars



\* proofs

ASSUME NodeIsFinite == IsFiniteSet(Node)
ASSUME RequestIsFinite == IsFiniteSet(Request)
ASSUME ResponseIsFinite == IsFiniteSet(Response)
ASSUME DbRequestIdIsFinite == IsFiniteSet(DbRequestId)
ASSUME NodeNonZero == Node # {}
ASSUME RequestNonZero == Request # {}
ASSUME ResponseNonZero == Response # {}
ASSUME DbRequestIdNonZero == DbRequestId # {}

THEOREM Init => IndInv
PROOF BY RequestNonZero DEF Init, IndInv, TypeOK, IndAuto, CandSep, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
        Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def


THEOREM IndInv /\ Next => IndInv'
PROOF
<1>1. IndInv /\ Next => TypeOK'
    <2>1. IndInv /\ (\E n \in Node, r \in Request : NewRequest(n,r)) => TypeOK'
        BY DEF IndInv, TypeOK, NewRequest
    <2>2. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => TypeOK'
        BY DEF IndInv, TypeOK, ServerProcessRequest
    <2>3. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => TypeOK'
        BY DEF IndInv, TypeOK, DbProcessRequest
    <2>4. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => TypeOK'
        BY DEF IndInv, TypeOK, ServerProcessDbResponse
    <2>5. IndInv /\ (\E n \in Node, p \in Response : ReceiveResponse(n,p)) => TypeOK'
        BY DEF IndInv, TypeOK, ReceiveResponse
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>2. IndInv /\ Next => Safety'
    <2>1. IndInv /\ (\E n \in Node, r \in Request : NewRequest(n,r)) => Safety'
        <3>. SUFFICES ASSUME IndInv, (\E n \in Node, r \in Request : NewRequest(n,r))
             PROVE Safety' OBVIOUS
        <3>. PICK n \in Node, r \in Request : NewRequest(n,r) OBVIOUS
        <3>. QED BY DEF NewRequest, IndInv, IndAuto, TypeOK, Safety, ResponseMatched
    <2>2. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Safety'
        BY DEF IndInv, TypeOK, ResponseMatched, ServerProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>3. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Safety'
        BY DEF IndInv, TypeOK, ResponseMatched, DbProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>4. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Safety'
        BY DEF IndInv, TypeOK, ResponseMatched, ServerProcessDbResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>5. IndInv /\ (\E n \in Node, p \in Response : ReceiveResponse(n,p)) => Safety'
        BY DEF IndInv, TypeOK, ResponseMatched, ReceiveResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>3. IndInv /\ Next => Inv689_1_0_def'
    <2>1. IndInv /\ (\E n \in Node, r \in Request : NewRequest(n,r)) => Inv689_1_0_def'
        BY DEF IndInv, TypeOK, ResponseMatched, NewRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>2. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Inv689_1_0_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ServerProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>3. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Inv689_1_0_def'
        BY DEF IndInv, TypeOK, ResponseMatched, DbProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>4. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Inv689_1_0_def'
        <3>. SUFFICES ASSUME IndInv, (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p))
             PROVE Inv689_1_0_def' OBVIOUS
        <3>. PICK n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p) OBVIOUS
        <3>1. Fluent14[i][n]
            <4>1. Fluent13'[i][n] BY DEF ServerProcessDbResponse, IndInv, TypeOK
            <4>2. Fluent14'[i][n] BY <4>1 DEF ServerProcessDbResponse, CandSep, IndInv, TypeOK
            <4>. QED BY <4>2 DEF ServerProcessDbResponse, IndInv, TypeOK
        <3>2. Fluent15[i][p]
            <4>1. Fluent16'[i][p] BY DEF ServerProcessDbResponse, IndInv, TypeOK
            <4>2. Fluent15'[i][p] BY <4>1 DEF ServerProcessDbResponse, CandSep, IndInv, TypeOK
            <4>. QED BY <4>2 DEF ServerProcessDbResponse, IndInv, TypeOK
        <3>3. ResponseMatched(n,p)
            BY RequestNonZero, <3>1, <3>2 DEF IndInv, TypeOK, ResponseMatched, CandSep, ServerProcessDbResponse, IndAuto, Safety,
                Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def, Inv388_1_1_def, Inv601_1_2_def,
                Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
        <3>. QED BY <3>3 DEF ServerProcessDbResponse, ResponseMatched, IndInv, TypeOK, IndAuto, Inv689_1_0_def
    <2>5. IndInv /\ (\E n \in Node, p \in Response : ReceiveResponse(n,p)) => Inv689_1_0_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ReceiveResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>4. IndInv /\ Next => Inv228_1_1_def'
    <2>1. IndInv /\ (\E n \in Node, r \in Request : NewRequest(n,r)) => Inv228_1_1_def'
        BY DEF IndInv, TypeOK, ResponseMatched, NewRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>2. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Inv228_1_1_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ServerProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>3. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Inv228_1_1_def'
        BY DEF IndInv, TypeOK, ResponseMatched, DbProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>4. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Inv228_1_1_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ServerProcessDbResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>5. IndInv /\ (\E n \in Node, p \in Response : ReceiveResponse(n,p)) => Inv228_1_1_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ReceiveResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>5. IndInv /\ Next => Inv421_1_2_def'
    <2>1. IndInv /\ (\E n \in Node, r \in Request : NewRequest(n,r)) => Inv421_1_2_def'
        BY DEF IndInv, TypeOK, ResponseMatched, NewRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>2. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Inv421_1_2_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ServerProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>3. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Inv421_1_2_def'
        <3>. SUFFICES ASSUME IndInv, (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
             PROVE Inv421_1_2_def' OBVIOUS
        <3>. PICK r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p) OBVIOUS
        <3>. QED
            BY RequestNonZero DEF IndInv, TypeOK, ResponseMatched, CandSep, DbProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>4. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Inv421_1_2_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ServerProcessDbResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>5. IndInv /\ (\E n \in Node, p \in Response : ReceiveResponse(n,p)) => Inv421_1_2_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ReceiveResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>6. IndInv /\ Next => Inv3533_2_3_def'
    <2>1. IndInv /\ (\E n \in Node, r \in Request : NewRequest(n,r)) => Inv3533_2_3_def'
        BY DEF IndInv, TypeOK, ResponseMatched, NewRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>2. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Inv3533_2_3_def'
        <3>. SUFFICES ASSUME IndInv, (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
             PROVE Inv3533_2_3_def' OBVIOUS
        <3>. PICK n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i) OBVIOUS
        \* \A VARI \in Node : \A VARID \in DbRequestId : \A VARP \in Response : (ResponseMatched(VARI,VARP)) \/ (~(Fluent14[VARID][VARI]) \/ (~(Fluent16[VARID][VARP])))
        <3>. SUFFICES ASSUME NEW VARI \in Node, NEW VARID \in DbRequestId, NEW VARP \in Response
             PROVE ResponseMatched(VARI,VARP)' \/ ~Fluent14'[VARID][VARI] \/ ~Fluent16'[VARID][VARP]
             BY DEF Inv3533_2_3_def
        <3>1. CASE VARI = n /\ VARID = i
            <4>. SUFFICES ASSUME Fluent14'[VARID][VARI], Fluent16'[VARID][VARP]
                 PROVE ResponseMatched(VARI,VARP)
                 BY DEF ServerProcessRequest, IndInv, TypeOK, ResponseMatched
            <4>1. <<VARI,r>> \in request_sent BY <3>1 DEF ServerProcessRequest
            <4>2. <<r,VARP>> \in match
                BY <3>1 DEF ServerProcessRequest, IndInv, TypeOK, ResponseMatched, CandSep, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
                Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
            <4>. QED BY <4>1, <4>2 DEF ResponseMatched
        <3>2. CASE VARID # i
            <4>1. Fluent14'[VARID][VARI] = Fluent14[VARID][VARI] BY <3>2 DEF ServerProcessRequest, IndInv, TypeOK
            <4>. QED BY <4>1 DEF ServerProcessRequest, IndInv, TypeOK, IndAuto, Inv3533_2_3_def, ResponseMatched
        <3>3. CASE VARI # n
            <4>1. Fluent14' = [Fluent14 EXCEPT ![i][n] = TRUE] BY DEF ServerProcessRequest
            <4>2. Fluent14'[VARID][VARI] = Fluent14[VARID][VARI] BY <3>3, <4>1
            <4>. QED BY <4>2 DEF ServerProcessRequest, IndInv, TypeOK, IndAuto, Inv3533_2_3_def, ResponseMatched
        <3>. QED BY <3>1, <3>2, <3>3
    <2>3. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Inv3533_2_3_def'
        BY DEF IndInv, TypeOK, ResponseMatched, DbProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>4. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Inv3533_2_3_def'
        BY DEF IndInv, TypeOK, ResponseMatched, CandSep, ServerProcessDbResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>5. IndInv /\ (\E n \in Node, p \in Response : ReceiveResponse(n,p)) => Inv3533_2_3_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ReceiveResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>7. IndInv /\ Next => Inv486_1_0_def'
    <2>1. IndInv /\ (\E n \in Node, r \in Request : NewRequest(n,r)) => Inv486_1_0_def'
        BY DEF IndInv, TypeOK, ResponseMatched, NewRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>2. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Inv486_1_0_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ServerProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>3. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Inv486_1_0_def'
        BY DEF IndInv, TypeOK, ResponseMatched, DbProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>4. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Inv486_1_0_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ServerProcessDbResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>5. IndInv /\ (\E n \in Node, p \in Response : ReceiveResponse(n,p)) => Inv486_1_0_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ReceiveResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>8. IndInv /\ Next => Inv388_1_1_def'
    <2>1. IndInv /\ (\E n \in Node, r \in Request : NewRequest(n,r)) => Inv388_1_1_def'
        BY DEF IndInv, TypeOK, ResponseMatched, NewRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>2. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Inv388_1_1_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ServerProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>3. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Inv388_1_1_def'
        <3>. SUFFICES ASSUME IndInv, (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
             PROVE Inv388_1_1_def' OBVIOUS
        <3>. PICK r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p) OBVIOUS
        \* \A VARID \in DbRequestId : \A VARP \in Response : \E VARR2 \in Request : (<<VARR2,VARP>> \in match) \/ (~(Fluent15[VARID][VARP]))
        <3>. SUFFICES ASSUME NEW VARID \in DbRequestId, NEW VARP \in Response
             PROVE \E VARR2 \in Request : (<<VARR2,VARP>> \in match') \/ (~(Fluent15'[VARID][VARP]))
             BY DEF Inv388_1_1_def
        <3>1. CASE VARID = i /\ VARP = p
            BY <3>1 DEF DbProcessRequest, IndInv, TypeOK, Inv388_1_1_def
        <3>2. CASE VARID # i
            <4>1. Fluent15'[VARID][VARP] = Fluent15[VARID][VARP] BY <3>2 DEF DbProcessRequest, IndInv, TypeOK
            <4>. QED BY <4>1 DEF DbProcessRequest, IndInv, TypeOK, IndAuto, Inv388_1_1_def
        <3>3. CASE VARP # p
            <4>1. Fluent15'[VARID][VARP] = Fluent15[VARID][VARP] BY <3>3 DEF DbProcessRequest, IndInv, TypeOK
            <4>. QED BY <4>1 DEF DbProcessRequest, IndInv, TypeOK, IndAuto, Inv388_1_1_def
        <3>. QED BY <3>1, <3>2, <3>3
    <2>4. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Inv388_1_1_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ServerProcessDbResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>5. IndInv /\ (\E n \in Node, p \in Response : ReceiveResponse(n,p)) => Inv388_1_1_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ReceiveResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>9. IndInv /\ Next => Inv601_1_2_def'
    <2>1. IndInv /\ (\E n \in Node, r \in Request : NewRequest(n,r)) => Inv601_1_2_def'
        BY DEF IndInv, TypeOK, ResponseMatched, NewRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>2. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Inv601_1_2_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ServerProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>3. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Inv601_1_2_def'
        BY DEF IndInv, TypeOK, ResponseMatched, DbProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>4. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Inv601_1_2_def'
        BY DEF IndInv, TypeOK, ResponseMatched, CandSep, ServerProcessDbResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>5. IndInv /\ (\E n \in Node, p \in Response : ReceiveResponse(n,p)) => Inv601_1_2_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ReceiveResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>10. IndInv /\ Next => Inv482_1_3_def'
    <2>1. IndInv /\ (\E n \in Node, r \in Request : NewRequest(n,r)) => Inv482_1_3_def'
        BY DEF IndInv, TypeOK, ResponseMatched, NewRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>2. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Inv482_1_3_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ServerProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>3. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Inv482_1_3_def'
        BY DEF IndInv, TypeOK, ResponseMatched, DbProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>4. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Inv482_1_3_def'
        BY DEF IndInv, TypeOK, ResponseMatched, CandSep, ServerProcessDbResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>5. IndInv /\ (\E n \in Node, p \in Response : ReceiveResponse(n,p)) => Inv482_1_3_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ReceiveResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>11. IndInv /\ Next => Inv658_1_4_def'
    <2>1. IndInv /\ (\E n \in Node, r \in Request : NewRequest(n,r)) => Inv658_1_4_def'
        BY DEF IndInv, TypeOK, ResponseMatched, NewRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>2. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Inv658_1_4_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ServerProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>3. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Inv658_1_4_def'
        BY DEF IndInv, TypeOK, ResponseMatched, DbProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>4. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Inv658_1_4_def'
        BY DEF IndInv, TypeOK, ResponseMatched, CandSep, ServerProcessDbResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>5. IndInv /\ (\E n \in Node, p \in Response : ReceiveResponse(n,p)) => Inv658_1_4_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ReceiveResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>12. IndInv /\ Next => Inv420_1_5_def'
    <2>1. IndInv /\ (\E n \in Node, r \in Request : NewRequest(n,r)) => Inv420_1_5_def'
        BY DEF IndInv, TypeOK, ResponseMatched, NewRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>2. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Inv420_1_5_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ServerProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>3. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Inv420_1_5_def'
        BY DEF IndInv, TypeOK, ResponseMatched, DbProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>4. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Inv420_1_5_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ServerProcessDbResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>5. IndInv /\ (\E n \in Node, p \in Response : ReceiveResponse(n,p)) => Inv420_1_5_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ReceiveResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>13. IndInv /\ Next => Inv122_1_6_def'
    <2>1. IndInv /\ (\E n \in Node, r \in Request : NewRequest(n,r)) => Inv122_1_6_def'
        BY DEF IndInv, TypeOK, ResponseMatched, NewRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>2. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Inv122_1_6_def'
        <3>. SUFFICES ASSUME IndInv, (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
             PROVE Inv122_1_6_def' OBVIOUS
        <3>. PICK n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i) OBVIOUS
        \* \A VARI \in Node : \A VARID \in DbRequestId : \E VARR2 \in Request : (<<VARI,VARR2>> \in request_sent) \/ (~(Fluent14[VARID][VARI]))
        <3>. SUFFICES ASSUME NEW VARI \in Node, NEW VARID \in DbRequestId
             PROVE \E VARR2 \in Request : (<<VARI,VARR2>> \in request_sent') \/ (~(Fluent14'[VARID][VARI]))
             BY DEF Inv122_1_6_def
        <3>1. CASE VARI = n /\ VARID = i
            BY <3>1 DEF ServerProcessRequest, IndInv, TypeOK, Inv122_1_6_def
        <3>2. CASE VARID # i
            <4>1. Fluent14'[VARID][VARI] = Fluent14[VARID][VARI] BY <3>2 DEF ServerProcessRequest, IndInv, TypeOK
            <4>. QED BY <4>1 DEF ServerProcessRequest, IndInv, TypeOK, IndAuto, Inv122_1_6_def
        <3>3. CASE VARI # n
            <4>1. Fluent14' = [Fluent14 EXCEPT ![i][n] = TRUE] BY DEF ServerProcessRequest
            <4>2. Fluent14'[VARID][VARI] = Fluent14[VARID][VARI] BY <3>3, <4>1
            <4>. QED BY <4>2 DEF ServerProcessRequest, IndInv, TypeOK, IndAuto, Inv122_1_6_def
        <3>. QED BY <3>1, <3>2, <3>3
    <2>3. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Inv122_1_6_def'
        BY DEF IndInv, TypeOK, ResponseMatched, DbProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>4. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Inv122_1_6_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ServerProcessDbResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>5. IndInv /\ (\E n \in Node, p \in Response : ReceiveResponse(n,p)) => Inv122_1_6_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ReceiveResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>14. IndInv /\ Next => Inv3554_2_7_def'
    <2>1. IndInv /\ (\E n \in Node, r \in Request : NewRequest(n,r)) => Inv3554_2_7_def'
        BY DEF IndInv, TypeOK, ResponseMatched, NewRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>2. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Inv3554_2_7_def'
        <3>. SUFFICES ASSUME IndInv, (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
             PROVE Inv3554_2_7_def' OBVIOUS
        <3>. PICK n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i) OBVIOUS
        \* \A VARI \in Node : \A VARID \in DbRequestId : \A VARP \in Response : (ResponseMatched(VARI,VARP)) \/ (~(Fluent15[VARID][VARP])) \/ (~(Fluent14[VARID][VARI]))
        <3>. SUFFICES ASSUME NEW VARI \in Node, NEW VARID \in DbRequestId, NEW VARP \in Response,
                             Fluent15'[VARID][VARP], Fluent14'[VARID][VARI]
             PROVE ResponseMatched(VARI,VARP)'
             BY DEF Inv3554_2_7_def
        <3>1. CASE VARI = n /\ VARID = i
            <4>1. <<VARI,r>> \in request_sent' BY <3>1 DEF ServerProcessRequest, IndInv, TypeOK
            <4>2. <<r,VARP>> \in match'
                BY <3>1 DEF ServerProcessRequest, IndInv, TypeOK, ResponseMatched, CandSep, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
                Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
            <4>. QED BY <4>1, <4>2 DEF ResponseMatched
        <3>2. CASE VARID # i
            <4>1. Fluent14'[VARID][VARI] = Fluent14[VARID][VARI] BY <3>2 DEF ServerProcessRequest, IndInv, TypeOK
            <4>. QED BY <4>1 DEF ServerProcessRequest, IndInv, TypeOK, IndAuto, Inv3554_2_7_def, ResponseMatched
        <3>3. CASE VARI # n
            <4>1. Fluent14' = [Fluent14 EXCEPT ![i][n] = TRUE] BY DEF ServerProcessRequest
            <4>2. Fluent14'[VARID][VARI] = Fluent14[VARID][VARI] BY <3>3, <4>1 DEF IndInv, TypeOK
            <4>. QED BY <4>2 DEF ServerProcessRequest, IndInv, TypeOK, IndAuto, Inv3554_2_7_def, ResponseMatched
        <3>. QED BY <3>1, <3>2, <3>3
    <2>3. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Inv3554_2_7_def'
        <3>. SUFFICES ASSUME IndInv, (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
             PROVE Inv3554_2_7_def' OBVIOUS
        <3>. PICK r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p) OBVIOUS
        \* \A VARI \in Node : \A VARID \in DbRequestId : \A VARP \in Response : (ResponseMatched(VARI,VARP)) \/ (~(Fluent15[VARID][VARP])) \/ (~(Fluent14[VARID][VARI]))
        <3>. SUFFICES ASSUME NEW VARI \in Node, NEW VARID \in DbRequestId, NEW VARP \in Response,
                             Fluent15'[VARID][VARP], Fluent14'[VARID][VARI]
             PROVE ResponseMatched(VARI,VARP)'
             BY DEF Inv3554_2_7_def
        <3>1. CASE VARID = i /\ VARP = p
            <4>1. <<VARI,r>> \in request_sent'
                BY <3>1 DEF DbProcessRequest, IndInv, TypeOK, ResponseMatched, CandSep, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
                Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
            <4>2. <<r,VARP>> \in match' BY <3>1 DEF DbProcessRequest, IndInv, TypeOK
            <4>. QED BY <4>1, <4>2 DEF ResponseMatched
        <3>2. CASE VARID # i
            BY <3>2 DEF DbProcessRequest, IndInv, TypeOK, ResponseMatched, IndAuto, Inv3554_2_7_def
        <3>3. CASE VARP # p /\ VARID = i
            BY <3>3 DEF DbProcessRequest, IndInv, TypeOK, ResponseMatched, IndAuto, Inv3554_2_7_def
        <3>. QED BY <3>1, <3>2, <3>3
    <2>4. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Inv3554_2_7_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ServerProcessDbResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>5. IndInv /\ (\E n \in Node, p \in Response : ReceiveResponse(n,p)) => Inv3554_2_7_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ReceiveResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>15. IndInv /\ Next => Inv1008_2_8_def'
    <2>1. IndInv /\ (\E n \in Node, r \in Request : NewRequest(n,r)) => Inv1008_2_8_def'
        BY DEF IndInv, TypeOK, ResponseMatched, NewRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>2. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Inv1008_2_8_def'
        <3>. SUFFICES ASSUME IndInv, (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
             PROVE Inv1008_2_8_def' OBVIOUS
        <3>. PICK n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i) OBVIOUS
        \* \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : (<<VARI,VARR>> \in request_sent) \/ (~(Fluent11[VARID][VARR])) \/ (~(Fluent14[VARID][VARI]))
        <3>. SUFFICES ASSUME NEW VARI \in Node, NEW VARID \in DbRequestId, NEW VARR \in Request,
                             Fluent11'[VARID][VARR], Fluent14'[VARID][VARI]
             PROVE <<VARI,VARR>> \in request_sent'
             BY DEF Inv1008_2_8_def
        <3>1. CASE n = VARI /\ r = VARR
            BY <3>1 DEF ServerProcessRequest
        <3>2. CASE n # VARI
            <4>. SUFFICES ASSUME TRUE
                 PROVE <<VARI,VARR>> \in request_sent
                 BY DEF ServerProcessRequest
            <4>1. Fluent14[VARID][VARI]
                <5>1. Fluent14' = [Fluent14 EXCEPT ![i][n] = TRUE] BY DEF ServerProcessRequest
                <5>. QED BY <3>2, <5>1
            <4>. QED
                BY <4>1 DEF IndInv, TypeOK, ResponseMatched, CandSep, ServerProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
                    Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
        <3>3. CASE r # VARR /\ n = VARI
            <4>. SUFFICES ASSUME TRUE
                 PROVE <<VARI,VARR>> \in request_sent
                 BY DEF ServerProcessRequest
            <4>1. Fluent11[VARID][VARR] BY <3>3 DEF ServerProcessRequest, IndInv, TypeOK
            <4>2. CASE i = VARID
                BY <3>3, <4>1, <4>2 DEF IndInv, TypeOK, ResponseMatched, CandSep, ServerProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
                Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
            <4>3. CASE i # VARID
                <5>1. Fluent14[VARID][VARI] BY <3>3, <4>3 DEF IndInv, TypeOK, ServerProcessRequest
                <5>. QED BY <3>3, <4>1, <5>1 DEF IndInv, IndAuto, Inv1008_2_8_def
            <4>. QED BY <4>2, <4>3
        <3>. QED BY <3>1, <3>2, <3>3
    <2>3. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Inv1008_2_8_def'
        BY DEF IndInv, TypeOK, ResponseMatched, DbProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>4. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Inv1008_2_8_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ServerProcessDbResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>5. IndInv /\ (\E n \in Node, p \in Response : ReceiveResponse(n,p)) => Inv1008_2_8_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ReceiveResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>16. IndInv /\ Next => Inv1968_2_9_def'
    <2>1. IndInv /\ (\E n \in Node, r \in Request : NewRequest(n,r)) => Inv1968_2_9_def'
        BY DEF IndInv, TypeOK, ResponseMatched, CandSep, NewRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>2. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Inv1968_2_9_def'
        <3>. SUFFICES ASSUME IndInv, (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
             PROVE Inv1968_2_9_def' OBVIOUS
        <3>. PICK n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i) OBVIOUS
        \* \A VARID \in DbRequestId : \A VARR \in Request : \A VARP \in Response : (<<VARR,VARP>> \in match) \/ (~(Fluent11[VARID][VARR]) \/ (~(Fluent15[VARID][VARP])))
        <3>. SUFFICES ASSUME NEW VARID \in DbRequestId, NEW VARR \in Request, NEW VARP \in Response,
                             Fluent11'[VARID][VARR], Fluent15'[VARID][VARP]
             PROVE <<VARR,VARP>> \in match'
             BY DEF Inv1968_2_9_def
        <3>1. CASE VARID = i /\ VARR = r
            BY <3>1 DEF ServerProcessRequest, IndInv, TypeOK, ResponseMatched, CandSep, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
                Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
        <3>2. CASE VARID # i
            BY <3>2 DEF ServerProcessRequest, IndInv, TypeOK, IndAuto, Inv1968_2_9_def, ResponseMatched
        <3>3. CASE VARR # r
            BY <3>3 DEF ServerProcessRequest, IndInv, TypeOK, IndAuto, Inv1968_2_9_def, ResponseMatched
        <3>. QED BY <3>1, <3>2, <3>3
    <2>3. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Inv1968_2_9_def'
        <3>. SUFFICES ASSUME IndInv, (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
             PROVE Inv1968_2_9_def' OBVIOUS
        <3>. PICK r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p) OBVIOUS
        \* \A VARID \in DbRequestId : \A VARR \in Request : \A VARP \in Response : (<<VARR,VARP>> \in match) \/ (~(Fluent11[VARID][VARR]) \/ (~(Fluent15[VARID][VARP])))
        <3>. SUFFICES ASSUME NEW VARID \in DbRequestId, NEW VARR \in Request, NEW VARP \in Response,
                             Fluent11'[VARID][VARR], Fluent15'[VARID][VARP]
             PROVE <<VARR,VARP>> \in match'
             BY DEF Inv1968_2_9_def
        <3>1. CASE VARID = i /\ VARR = r
            \*<4>1. <<VARR,p>> \in match BY <3>1 DEF DbProcessRequest
            <4>1. CASE p = VARP BY <3>1, <4>1 DEF IndInv, TypeOK, CandSep, DbProcessRequest
            <4>2. CASE p # VARP
                BY <3>1, <4>2 DEF IndInv, TypeOK, CandSep, ReceiveResponse, DbProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
                    Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
            <4>. QED BY <4>1, <4>2
        <3>2. CASE VARID # i
            BY <3>2 DEF DbProcessRequest, IndInv, TypeOK, IndAuto, Inv1968_2_9_def, ResponseMatched
        <3>3. CASE VARR # r /\ VARID = i
            BY <3>3 DEF IndInv, TypeOK, ResponseMatched, CandSep, DbProcessRequest, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
                Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
        <3>. QED BY <3>1, <3>2, <3>3
    <2>4. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Inv1968_2_9_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ServerProcessDbResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>5. IndInv /\ (\E n \in Node, p \in Response : ReceiveResponse(n,p)) => Inv1968_2_9_def'
        BY DEF IndInv, TypeOK, ResponseMatched, ReceiveResponse, IndAuto, Safety, Inv689_1_0_def, Inv228_1_1_def, Inv421_1_2_def, Inv3533_2_3_def, Inv486_1_0_def,
            Inv388_1_1_def, Inv601_1_2_def, Inv482_1_3_def, Inv658_1_4_def, Inv420_1_5_def, Inv122_1_6_def, Inv3554_2_7_def, Inv1008_2_8_def, Inv1968_2_9_def
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>17. IndInv /\ Next => CandSep'
    BY DEF Next, NewRequest, ServerProcessRequest, DbProcessRequest, ServerProcessDbResponse, ReceiveResponse
<1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17
         DEF IndInv, IndAuto


=============================================================================
\* Modification History
\* Last modified Mon Dec 02 13:09:24 EST 2024 by idardik
\* Created Tue Nov 26 09:41:27 EST 2024 by idardik

