------------------------------ MODULE C1Proof ------------------------------
EXTENDS C1, TLAPS

THEOREM IndInv /\ Next => IndInv'
PROOF
<1>. SUFFICES ASSUME IndInv, Next
     PROVE IndInv'
     OBVIOUS
<1>1. TypeOK'
    <2>1. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : reshard(n, m, k, v, s)
        BY <2>1, Z3T(30) DEF IndInv, TypeOK, reshard
    <2>2. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : recv_transfer_msg(n, m, k, v, s)
        BY <2>2, Z3T(30) DEF IndInv, TypeOK, recv_transfer_msg
    <2>3. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : put(n, k, v)
        BY <2>3 DEF IndInv, TypeOK, put
    <2>. QED BY <2>1, <2>2, <2>3 DEF Next
<1>2. Safety'
    <2>1. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : reshard(n, m, k, v, s)
        BY <2>1, Z3T(30) DEF IndInv, TypeOK, reshard, Safety, Inv1, Inv2, Inv3, Inv4
    <2>2. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : recv_transfer_msg(n, m, k, v, s)
        BY <2>2, Z3T(120), <1>1 DEF IndInv, TypeOK, recv_transfer_msg, Safety, Inv1, Inv2, Inv3, Inv4, CandSep
    <2>3. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : put(n, k, v)
        BY <2>3, Z3T(30) DEF IndInv, TypeOK, put, Safety, Inv1, Inv2, Inv3, Inv4
    <2>. QED BY <2>1, <2>2, <2>3 DEF Next
<1>3. Inv1'
    <2>1. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : reshard(n, m, k, v, s)
        BY <2>1, Z3T(30) DEF IndInv, TypeOK, reshard, Safety, Inv1, Inv2, Inv3, Inv4
    <2>2. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : recv_transfer_msg(n, m, k, v, s)
        BY <2>2, Z3T(120), <1>1 DEF IndInv, TypeOK, recv_transfer_msg, Safety, Inv1, Inv2, Inv3, Inv4, CandSep
    <2>3. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : put(n, k, v)
        BY <2>3 DEF IndInv, TypeOK, put, Safety, Inv1, Inv2, Inv3, Inv4
    <2>. QED BY <2>1, <2>2, <2>3 DEF Next
<1>4. Inv2'
    <2>1. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : reshard(n, m, k, v, s)
        BY <2>1, Z3T(30) DEF IndInv, TypeOK, reshard, Safety, Inv1, Inv2, Inv3, Inv4
    <2>2. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : recv_transfer_msg(n, m, k, v, s)
        BY <2>2, Z3T(30) DEF IndInv, TypeOK, recv_transfer_msg, Safety, Inv1, Inv2, Inv3, Inv4
    <2>3. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : put(n, k, v)
        BY <2>3 DEF IndInv, TypeOK, put, Safety, Inv1, Inv2, Inv3, Inv4
    <2>. QED BY <2>1, <2>2, <2>3 DEF Next
<1>5. Inv3'
    <2>1. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : reshard(n, m, k, v, s)
        BY <2>1, Z3T(600), <1>1 DEF IndInv, TypeOK, reshard, Safety, Inv1, Inv2, Inv3, Inv4, CandSep
    <2>2. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : recv_transfer_msg(n, m, k, v, s)
        BY <2>2, Z3T(600), <1>1 DEF IndInv, TypeOK, recv_transfer_msg, Safety, Inv1, Inv2, Inv3, Inv4, CandSep
    <2>3. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : put(n, k, v)
        BY <2>3, Z3T(600), <1>1 DEF IndInv, TypeOK, put, Safety, Inv1, Inv2, Inv3, Inv4, CandSep
    <2>. QED BY <2>1, <2>2, <2>3 DEF Next
<1>6. Inv4'
    <2>1. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : reshard(n, m, k, v, s)
        BY <2>1, Z3T(60) DEF IndInv, TypeOK, reshard, Safety, Inv1, Inv2, Inv3, Inv4
    <2>2. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : recv_transfer_msg(n, m, k, v, s)
        BY <2>2, Z3T(120), <1>1 DEF IndInv, TypeOK, recv_transfer_msg, Safety, Inv1, Inv2, Inv3, Inv4, CandSep
    <2>3. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : put(n, k, v)
        BY <2>3, Z3T(30) DEF IndInv, TypeOK, put, Safety, Inv1, Inv2, Inv3, Inv4
    <2>. QED BY <2>1, <2>2, <2>3 DEF Next
<1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF IndInv

THEOREM Init => IndInv
BY DEF Init, IndInv, TypeOK, Safety, Inv1, Inv2, Inv3, Inv4

=============================================================================
