---- MODULE C2 ----

CONSTANTS Key, Node, Value, Seqnum

VARIABLES transfer_msg, seqnum_sent, seqnum_recvd, ctr1, ctr2, rectr1, rectr2

vars == <<transfer_msg, seqnum_sent, seqnum_recvd, ctr1, ctr2, rectr1, rectr2>>

Safety == \A n \in Node : \A m \in Node : \A k \in Key : \A v \in Value : \A s \in Seqnum : ~ctr2[n][m][k][v][s]

CandSep ==
/\ \A n \in Node : \A m \in Node : \A k \in Key : \A v \in Value : \A s \in Seqnum : ~rectr2[n][m][k][v][s]


Init ==
    /\ transfer_msg = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
    /\ seqnum_sent = [n \in Node |-> [s \in Seqnum |-> FALSE]]
    /\ seqnum_recvd = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
    /\ ctr1 = [n \in Node |-> [m \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> TRUE]]]]]
    /\ ctr2 = [n \in Node |-> [m \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
    /\ rectr1 = [n \in Node |-> [m \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> TRUE]]]]]
    /\ rectr2 = [n \in Node |-> [m \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]

reshard(n_old, n_new, k, v, s) ==
  /\ ~seqnum_sent[n_old][s]
  /\ seqnum_sent' = [seqnum_sent EXCEPT![n_old][s] = TRUE]
  /\ transfer_msg' = [transfer_msg EXCEPT![n_old][n_new][k][v][s] = TRUE]
  /\ UNCHANGED<<seqnum_recvd>>
  /\ ctr1' = [ctr1 EXCEPT![n_old][n_new][k][v][s] = FALSE]
  /\ ctr2' = [ctr2 EXCEPT![n_old][n_new][k][v][s] = FALSE]
  /\ rectr1' = [rectr1 EXCEPT![n_old][n_new][k][v][s] = FALSE]
  /\ rectr2' = [rectr2 EXCEPT![n_old][n_new][k][v][s] = FALSE]
  /\ CandSep'

drop_transfer_msg(src, dst, k, v, s) ==
  /\ transfer_msg[src][dst][k][v][s]
  /\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = FALSE]
  /\ UNCHANGED<<seqnum_sent, seqnum_recvd>>
  /\ UNCHANGED<<ctr1, ctr2>>
  /\ UNCHANGED<<rectr1,rectr2>>
  /\ CandSep'

retransmit(src, dst, k, v, s) ==
  /\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = TRUE]
  /\ UNCHANGED<<seqnum_sent, seqnum_recvd>>
  /\ UNCHANGED<<ctr1, ctr2>>
  /\ rectr2' = [rectr2 EXCEPT![src][dst][k][v][s] = rectr1[src][dst][k][v][s]]
  /\ UNCHANGED<<rectr1>>
  /\ CandSep'

recv_transfer_msg(src, n, k, v, s) ==
  /\ transfer_msg[src][n][k][v][s]
  /\ ~seqnum_recvd[n][src][s]
  /\ seqnum_recvd' = [seqnum_recvd EXCEPT![n][src][s] = TRUE]
  /\ UNCHANGED<<transfer_msg, seqnum_sent>>
  /\ ctr1' = [ctr1 EXCEPT![src][n][k][v][s] = TRUE]
  /\ ctr2' = [ctr2 EXCEPT![src][n][k][v][s] = ctr1[src][n][k][v][s]]
  /\ UNCHANGED<<rectr1,rectr2>>
  /\ CandSep'

send_ack(src, n, k, v, s) ==
  /\ transfer_msg[src][n][k][v][s]
  /\ seqnum_recvd[n][src][s]
  /\ UNCHANGED<<transfer_msg, seqnum_sent, seqnum_recvd>>
  /\ UNCHANGED<<ctr1, ctr2>>
  /\ UNCHANGED<<rectr1,rectr2>>
  /\ CandSep'

Next ==
    \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum :
        \/ reshard(n, m, k, v, s)
        \/ drop_transfer_msg(n, m, k, v, s)
        \/ retransmit(n, m, k, v, s)
        \/ recv_transfer_msg(n, m, k, v, s)
        \/ send_ack(n, m, k, v, s)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ transfer_msg \in [Node -> [Node -> [Key -> [Value -> [Seqnum -> BOOLEAN]]]]]
  /\ seqnum_sent \in [Node -> [Seqnum -> BOOLEAN]]
  /\ seqnum_recvd \in [Node -> [Node -> [Seqnum -> BOOLEAN]]]
  /\ ctr1 \in [Node -> [Node -> [Key -> [Value -> [Seqnum -> BOOLEAN]]]]]
  /\ ctr2 \in [Node -> [Node -> [Key -> [Value -> [Seqnum -> BOOLEAN]]]]]
  /\ rectr1 \in [Node -> [Node -> [Key -> [Value -> [Seqnum -> BOOLEAN]]]]]
  /\ rectr2 \in [Node -> [Node -> [Key -> [Value -> [Seqnum -> BOOLEAN]]]]]

Inv1 ==
    \A N1,N2 \in Node : \A K \in Key : \A V \in Value : \A S \in Seqnum :
        (transfer_msg[N1][N2][K][V][S] /\ ~seqnum_recvd[N2][N1][S]) => ~ctr1[N1][N2][K][V][S]

Inv2 ==
    \A N1,N2 \in Node : \A K \in Key : \A V \in Value : \A S \in Seqnum :
        \* an internal message is currently in transit => an external request is being serviced
        (~rectr1[N1][N2][K][V][S] /\ ~seqnum_recvd[N2][N1][S]) => ~ctr1[N1][N2][K][V][S]

IndInv ==
  /\ TypeOK
  /\ Safety
  /\ Inv1
  /\ Inv2

IISpec == IndInv /\ [][Next]_vars

======
