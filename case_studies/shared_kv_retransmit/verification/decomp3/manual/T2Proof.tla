------------------------------ MODULE T2Proof ------------------------------
EXTENDS T2, TLAPS

LEMMA UnchUnacked ==
ASSUME NEW N1 \in Node, NEW N2 \in Node, NEW K \in Key, NEW V \in Value, NEW S \in Seqnum,
       NEW n1 \in Node, NEW n2 \in Node, NEW k \in Key, NEW v \in Value, NEW s \in Seqnum,
       unacked' = [unacked EXCEPT![n1][n2][k][v][s] = TRUE],
       S#s
PROVE  unacked'[N1][N2][K][V][S] = unacked[N1][N2][K][V][S]
OBVIOUS

LEMMA UnchRectr1 ==
ASSUME NEW N1 \in Node, NEW N2 \in Node, NEW K \in Key, NEW V \in Value, NEW S \in Seqnum,
       NEW n1 \in Node, NEW n2 \in Node, NEW k \in Key, NEW v \in Value, NEW s \in Seqnum,
       rectr1' = [rectr1 EXCEPT![n1][n2][k][v][s] = FALSE],
       S#s
PROVE  rectr1'[N1][N2][K][V][S] = rectr1[N1][N2][K][V][S]
OBVIOUS

THEOREM IndInv /\ Next => IndInv'
PROOF
<1>. SUFFICES ASSUME IndInv, Next
     PROVE IndInv'
     OBVIOUS
<1>1. TypeOK'
    <2>1. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : reshard(n, m, k, v, s)
        BY <2>1, Z3T(600) DEF IndInv, TypeOK, reshard
    <2>2. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : retransmit(n, m, k, v, s)
        BY <2>2, Z3T(600) DEF IndInv, TypeOK, retransmit
    <2>3. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : send_ack(n, m, k, v, s)
        BY <2>3, Z3T(600) DEF IndInv, TypeOK, send_ack
    <2>4. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : drop_ack_msg(n, m, s)
        BY <2>4, Z3T(600) DEF IndInv, TypeOK, drop_ack_msg
    <2>5. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : recv_ack_msg(n, m, s)
        BY <2>5, Z3T(600) DEF IndInv, TypeOK, recv_ack_msg
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>2. Safety'
    <2>1. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : reshard(n, m, k, v, s)
        BY <2>1, Z3T(600) DEF IndInv, TypeOK, reshard, Safety, Inv1
    <2>2. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : retransmit(n, m, k, v, s)
        BY <2>2, Z3T(600) DEF IndInv, TypeOK, retransmit, Safety, Inv1
    <2>3. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : send_ack(n, m, k, v, s)
        BY <2>3, Z3T(600) DEF IndInv, TypeOK, send_ack, Safety, Inv1
    <2>4. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : drop_ack_msg(n, m, s)
        BY <2>4, Z3T(600) DEF IndInv, TypeOK, drop_ack_msg, Safety, Inv1
    <2>5. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : recv_ack_msg(n, m, s)
        BY <2>5, Z3T(600) DEF IndInv, TypeOK, recv_ack_msg, Safety, Inv1
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>3. Inv1'
    <2>1. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : reshard(n, m, k, v, s)
        <3>1. PICK n,m \in Node, k \in Key, v \in Value, s \in Seqnum : reshard(n, m, k, v, s) BY <2>1
        <3>2. SUFFICES ASSUME NEW N1 \in Node, NEW  N2 \in Node, NEW K \in Key, NEW V \in Value, NEW S \in Seqnum, 
                             unacked'[N1][N2][K][V][S]
             PROVE ~rectr1'[N1][N2][K][V][S]
             BY DEF Inv1
        <3>4. CASE N1=n /\ N2=m /\ K=k /\ V=v /\ S=s
            BY <3>1, <3>2, <3>4, Z3T(600) DEF IndInv, TypeOK, reshard, Safety, Inv1
        <3>5. CASE N1#n BY <3>1, <3>2, <3>5, Z3T(600) DEF IndInv, TypeOK, reshard, Safety, Inv1
        <3>6. CASE N2#m BY <3>1, <3>2, <3>6, Z3T(600) DEF IndInv, TypeOK, reshard, Safety, Inv1
        <3>7. CASE K#k BY <3>1, <3>2, <3>7, Z3T(600) DEF IndInv, TypeOK, reshard, Safety, Inv1
        <3>8. CASE V#v BY <3>1, <3>2, <3>8, Z3T(600) DEF IndInv, TypeOK, reshard, Safety, Inv1
        <3>9. CASE S#s
            <4>1. unacked'[N1][N2][K][V][S] = unacked[N1][N2][K][V][S]
                BY <1>1, <3>1, <3>2, <3>9, UnchUnacked DEF IndInv, TypeOK, reshard
            <4>2. rectr1'[N1][N2][K][V][S] = rectr1[N1][N2][K][V][S]
                BY <1>1, <3>1, <3>2, <3>9, UnchRectr1 DEF IndInv, TypeOK, reshard
            <4>. QED
                BY <3>1, <3>2, <3>9, <4>1, <4>2 DEF IndInv, TypeOK, reshard, Safety, Inv1
        <3>. QED BY <3>4, <3>5, <3>6, <3>7, <3>8, <3>9
    <2>2. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : retransmit(n, m, k, v, s)
        BY <2>2, Z3T(600) DEF IndInv, TypeOK, retransmit, Safety, Inv1
    <2>3. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : send_ack(n, m, k, v, s)
        BY <2>3, Z3T(600) DEF IndInv, TypeOK, send_ack, Safety, Inv1
    <2>4. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : drop_ack_msg(n, m, s)
        BY <2>4, Z3T(600) DEF IndInv, TypeOK, drop_ack_msg, Safety, Inv1
    <2>5. CASE \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum : recv_ack_msg(n, m, s)
        BY <2>5, Z3T(600) DEF IndInv, TypeOK, recv_ack_msg, Safety, Inv1
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>. QED BY <1>1, <1>2, <1>3 DEF IndInv

THEOREM Init => IndInv
BY DEF Init, IndInv, TypeOK, Safety, Inv1

=============================================================================
