--------------------------------- MODULE D1 ---------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC, FiniteSets

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES db_request_sent, db_response_sent, t, Fluent12, Fluent11, Fluent14, Fluent13, Fluent16, Fluent15

vars == <<db_request_sent, db_response_sent, t, Fluent12, Fluent11, Fluent14, Fluent13, Fluent16, Fluent15>>

CandSep ==
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


\* Endive output

Inv224_1_0_def == \A VARID \in DbRequestId : \A VARP \in Response : \E VARR2 \in Request : (Fluent12[VARR2][VARID]) \/ (~(Fluent15[VARID][VARP]))
Inv191_1_1_def == \A VARID \in DbRequestId : \A VARR \in Request : (Fluent11[VARID][VARR]) \/ (~(<<VARID,VARR>> \in db_request_sent))
Inv159_1_2_def == \A VARID \in DbRequestId : \E VARR2 \in Request : (Fluent11[VARID][VARR2]) \/ ((NoneWithId(VARID)))
Inv497_1_3_def == \A VARID \in DbRequestId : \A VARR \in Request : ~(Fluent11[VARID][VARR]) \/ (~(NoneWithId(VARID)))
Inv302_1_0_def == \A VARI \in Node : \A VARID \in DbRequestId : (Fluent14[VARID][VARI]) \/ (~(<<VARID,VARI>> \in t))
Inv343_1_1_def == \A VARID \in DbRequestId : \A VARP \in Response : (Fluent15[VARID][VARP]) \/ (~(<<VARID,VARP>> \in db_response_sent))

\* The inductive invariant candidate.
IndAuto ==
  /\ CandSep
  /\ Inv224_1_0_def
  /\ Inv191_1_1_def
  /\ Inv159_1_2_def
  /\ Inv497_1_3_def
  /\ Inv302_1_0_def
  /\ Inv343_1_1_def

IndInv == TypeOK /\ IndAuto
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
PROOF BY RequestNonZero DEF Init, IndInv, TypeOK, IndAuto, CandSep, NoneWithId,
    Inv224_1_0_def, Inv191_1_1_def, Inv159_1_2_def, Inv497_1_3_def, Inv302_1_0_def, Inv343_1_1_def
(*<1>. SUFFICES ASSUME Init PROVE IndInv
     OBVIOUS
<1>1. TypeOK BY DEF Init, TypeOK
<1>2. CandSep BY RequestNonZero DEF Init, CandSep
<1>3. Inv224_1_0_def BY RequestNonZero DEF Init, Inv224_1_0_def
<1>4. Inv191_1_1_def BY DEF Init, Inv191_1_1_def
<1>5. Inv159_1_2_def BY RequestNonZero DEF Init, Inv159_1_2_def, NoneWithId
<1>6. Inv497_1_3_def BY DEF Init, Inv497_1_3_def
<1>7. Inv302_1_0_def BY DEF Init, Inv302_1_0_def
<1>8. Inv343_1_1_def BY DEF Init, Inv343_1_1_def
<1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8 DEF IndInv, IndAuto
*)


THEOREM IndInv /\ Next => IndInv'
PROOF
<1>1. IndInv /\ Next => TypeOK'
    <2>1. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => TypeOK'
        BY DEF IndInv, TypeOK, ServerProcessRequest
    <2>2. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => TypeOK'
        BY DEF IndInv, TypeOK, DbProcessRequest
    <2>3. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => TypeOK'
        BY DEF IndInv, TypeOK, ServerProcessDbResponse
    <2>4. QED BY <2>1, <2>2, <2>3 DEF IndInv, Next
<1>2. IndInv /\ Next => CandSep'
    <2>1. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => CandSep'
        BY RequestNonZero DEF IndInv, TypeOK, ServerProcessRequest, NoneWithId,
            IndAuto, CandSep, Inv224_1_0_def, Inv191_1_1_def, Inv159_1_2_def, Inv497_1_3_def, Inv302_1_0_def, Inv343_1_1_def
    <2>2. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => CandSep'
        BY RequestNonZero DEF IndInv, TypeOK, DbProcessRequest,
            IndAuto, CandSep, Inv224_1_0_def, Inv191_1_1_def, Inv159_1_2_def, Inv497_1_3_def, Inv302_1_0_def, Inv343_1_1_def
    <2>3. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => CandSep'
        BY DEF IndInv, TypeOK, ServerProcessDbResponse,
            IndAuto, CandSep, Inv224_1_0_def, Inv191_1_1_def, Inv159_1_2_def, Inv497_1_3_def, Inv302_1_0_def, Inv343_1_1_def
    <2>4. QED BY <2>1, <2>2, <2>3 DEF IndInv, Next
<1>3. IndInv /\ Next => Inv224_1_0_def'
    <2>1. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Inv224_1_0_def'
        BY RequestNonZero DEF IndInv, TypeOK, ServerProcessRequest, NoneWithId,
            IndAuto, CandSep, Inv224_1_0_def, Inv191_1_1_def, Inv159_1_2_def, Inv497_1_3_def, Inv302_1_0_def, Inv343_1_1_def
    <2>2. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Inv224_1_0_def'
        BY RequestNonZero DEF IndInv, TypeOK, DbProcessRequest,
            IndAuto, CandSep, Inv224_1_0_def, Inv191_1_1_def, Inv159_1_2_def, Inv497_1_3_def, Inv302_1_0_def, Inv343_1_1_def
    <2>3. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Inv224_1_0_def'
        BY DEF IndInv, TypeOK, ServerProcessDbResponse,
            IndAuto, CandSep, Inv224_1_0_def, Inv191_1_1_def, Inv159_1_2_def, Inv497_1_3_def, Inv302_1_0_def, Inv343_1_1_def
    <2>4. QED BY <2>1, <2>2, <2>3 DEF IndInv, Next
<1>4. IndInv /\ Next => Inv191_1_1_def'
    <2>1. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Inv191_1_1_def'
        <3>. SUFFICES ASSUME IndInv, (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
             PROVE Inv191_1_1_def' OBVIOUS
        <3>. PICK n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i) OBVIOUS
        <3>. QED BY DEF ServerProcessRequest, IndInv, IndAuto, TypeOK, Inv191_1_1_def
    <2>2. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Inv191_1_1_def'
        BY RequestNonZero DEF IndInv, TypeOK, DbProcessRequest,
            IndAuto, CandSep, Inv224_1_0_def, Inv191_1_1_def, Inv159_1_2_def, Inv497_1_3_def, Inv302_1_0_def, Inv343_1_1_def
    <2>3. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Inv191_1_1_def'
        BY DEF IndInv, TypeOK, ServerProcessDbResponse,
            IndAuto, CandSep, Inv224_1_0_def, Inv191_1_1_def, Inv159_1_2_def, Inv497_1_3_def, Inv302_1_0_def, Inv343_1_1_def
    <2>4. QED BY <2>1, <2>2, <2>3 DEF IndInv, Next
<1>5. IndInv /\ Next => Inv159_1_2_def'
    <2>1. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Inv159_1_2_def'
        BY RequestNonZero DEF IndInv, TypeOK, ServerProcessRequest, NoneWithId,
            IndAuto, CandSep, Inv224_1_0_def, Inv191_1_1_def, Inv159_1_2_def, Inv497_1_3_def, Inv302_1_0_def, Inv343_1_1_def
    <2>2. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Inv159_1_2_def'
        <3>. SUFFICES ASSUME IndInv, \E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)
             PROVE Inv159_1_2_def' OBVIOUS
        <3>. PICK r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p) OBVIOUS
        <3>. QED BY DEF DbProcessRequest, NoneWithId, IndInv, IndAuto, TypeOK, Inv159_1_2_def
    <2>3. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Inv159_1_2_def'
        <3>. SUFFICES ASSUME IndInv, \E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)
             PROVE Inv159_1_2_def' OBVIOUS
        <3>. PICK n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p) OBVIOUS
        <3>. QED BY DEF ServerProcessDbResponse, NoneWithId, IndInv, IndAuto, TypeOK, Inv159_1_2_def
    <2>4. QED BY <2>1, <2>2, <2>3 DEF IndInv, Next
<1>6. IndInv /\ Next => Inv497_1_3_def'
    <2>1. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Inv497_1_3_def'
        <3>. SUFFICES ASSUME IndInv, (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
             PROVE Inv497_1_3_def' OBVIOUS
        <3>. PICK n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i) OBVIOUS
        <3>. QED BY DEF ServerProcessRequest, NoneWithId, IndInv, IndAuto, TypeOK, Inv497_1_3_def
    <2>2. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Inv497_1_3_def'
        <3>. SUFFICES ASSUME IndInv, (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
             PROVE Inv497_1_3_def' OBVIOUS
        <3>. PICK r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p) OBVIOUS
        <3>. QED BY DEF DbProcessRequest, NoneWithId, IndInv, IndAuto, TypeOK, Inv497_1_3_def
    <2>3. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Inv497_1_3_def'
        <3>. SUFFICES ASSUME IndInv, (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p))
             PROVE Inv497_1_3_def' OBVIOUS
        <3>. PICK n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p) OBVIOUS
        <3>. QED BY DEF ServerProcessDbResponse, NoneWithId, IndInv, IndAuto, TypeOK, Inv497_1_3_def
    <2>4. QED BY <2>1, <2>2, <2>3 DEF IndInv, Next
<1>7. IndInv /\ Next => Inv302_1_0_def'
    <2>1. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Inv302_1_0_def'
        <3>. SUFFICES ASSUME IndInv, (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
             PROVE Inv302_1_0_def' OBVIOUS
        <3>. PICK n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i) OBVIOUS
        <3>. QED BY DEF ServerProcessRequest, NoneWithId, IndInv, IndAuto, TypeOK, Inv302_1_0_def
    <2>2. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Inv302_1_0_def'
        BY RequestNonZero DEF IndInv, TypeOK, DbProcessRequest,
            IndAuto, CandSep, Inv224_1_0_def, Inv191_1_1_def, Inv159_1_2_def, Inv497_1_3_def, Inv302_1_0_def, Inv343_1_1_def
    <2>3. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Inv302_1_0_def'
        BY RequestNonZero DEF IndInv, TypeOK, ServerProcessDbResponse,
            IndAuto, CandSep, Inv224_1_0_def, Inv191_1_1_def, Inv159_1_2_def, Inv497_1_3_def, Inv302_1_0_def, Inv343_1_1_def
    <2>4. QED BY <2>1, <2>2, <2>3 DEF IndInv, Next
<1>8. IndInv /\ Next => Inv343_1_1_def'
    <2>1. IndInv /\ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)) => Inv343_1_1_def'
        BY RequestNonZero DEF IndInv, TypeOK, ServerProcessRequest, NoneWithId,
            IndAuto, CandSep, Inv224_1_0_def, Inv191_1_1_def, Inv159_1_2_def, Inv497_1_3_def, Inv302_1_0_def, Inv343_1_1_def
    <2>2. IndInv /\ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)) => Inv343_1_1_def'
        <3>. SUFFICES ASSUME IndInv, (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
             PROVE Inv343_1_1_def' OBVIOUS
        <3>. PICK r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p) OBVIOUS
        <3>. QED BY DEF DbProcessRequest, NoneWithId, IndInv, IndAuto, TypeOK, Inv343_1_1_def
    <2>3. IndInv /\ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)) => Inv343_1_1_def'
        BY RequestNonZero DEF IndInv, TypeOK, ServerProcessDbResponse,
            IndAuto, CandSep, Inv224_1_0_def, Inv191_1_1_def, Inv159_1_2_def, Inv497_1_3_def, Inv302_1_0_def, Inv343_1_1_def
    <2>4. QED BY <2>1, <2>2, <2>3 DEF IndInv, Next
<1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8 DEF IndInv, IndAuto



=============================================================================
\* Modification History
\* Last modified Fri Nov 29 08:58:25 EST 2024 by idardik
\* Created Tue Nov 26 09:50:38 EST 2024 by idardik

