---- MODULE T1_hist ----

CONSTANTS Key, Node, Value, Seqnum

VARIABLES unacked, transfer_msg, ack_msg, seqnum_sent, seqnum_recvd, ctr1, ctr2

vars == <<unacked, transfer_msg, ack_msg, seqnum_sent, seqnum_recvd, ctr1, ctr2>>

CandSep == \A n \in Node : \A m \in Node : \A k \in Key : \A v \in Value : \A s \in Seqnum : ~ctr2[n][m][k][v][s]


Init ==
    /\ transfer_msg = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
    /\ unacked = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
    /\ ack_msg = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
    /\ seqnum_sent = [n \in Node |-> [s \in Seqnum |-> FALSE]]
    /\ seqnum_recvd = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
    /\ ctr1 = [n \in Node |-> [m \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> TRUE]]]]]
    /\ ctr2 = [n \in Node |-> [m \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]

reshard(n_old, n_new, k, v, s) ==
  /\ ~seqnum_sent[n_old][s]
  /\ seqnum_sent' = [seqnum_sent EXCEPT![n_old][s] = TRUE]
  /\ transfer_msg' = [transfer_msg EXCEPT![n_old][n_new][k][v][s] = TRUE]
  /\ unacked' = [unacked EXCEPT![n_old][n_new][k][v][s] = TRUE]
  /\ UNCHANGED<<ack_msg, seqnum_recvd>>
  /\ ctr1' = [ctr1 EXCEPT![n_old][n_new][k][v][s] = FALSE]
  /\ ctr2' = [ctr2 EXCEPT![n_old][n_new][k][v][s] = FALSE]

drop_transfer_msg(src, dst, k, v, s) ==
  /\ transfer_msg[src][dst][k][v][s]
  /\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = FALSE]
  /\ UNCHANGED<<unacked, ack_msg, seqnum_sent, seqnum_recvd>>
  /\ UNCHANGED<<ctr1, ctr2>>

retransmit(src, dst, k, v, s) ==
  /\ unacked[src][dst][k][v][s]
  /\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = TRUE]
  /\ UNCHANGED<<unacked, ack_msg, seqnum_sent, seqnum_recvd>>
  /\ UNCHANGED<<ctr1, ctr2>>

recv_transfer_msg(src, n, k, v, s) ==
  /\ transfer_msg[src][n][k][v][s]
  /\ ~seqnum_recvd[n][src][s]
  /\ seqnum_recvd' = [seqnum_recvd EXCEPT![n][src][s] = TRUE]
  /\ UNCHANGED<<unacked, transfer_msg, ack_msg, seqnum_sent>>
  /\ ctr1' = [ctr1 EXCEPT![src][n][k][v][s] = TRUE]
  /\ ctr2' = [ctr2 EXCEPT![src][n][k][v][s] = ctr1[src][n][k][v][s]]

send_ack(src, n, k, v, s) ==
  /\ transfer_msg[src][n][k][v][s]
  /\ seqnum_recvd[n][src][s]
  /\ ack_msg' = [ack_msg EXCEPT![src][n][s] = TRUE]
  /\ UNCHANGED<<unacked, transfer_msg, seqnum_sent, seqnum_recvd>>
  /\ UNCHANGED<<ctr1, ctr2>>

drop_ack_msg(src, dst, s) ==
  /\ ack_msg[src][dst][s]
  /\ ack_msg' = [ack_msg EXCEPT![src][dst][s] = FALSE]
  /\ UNCHANGED<<unacked, transfer_msg, seqnum_sent, seqnum_recvd>>
  /\ UNCHANGED<<ctr1, ctr2>>

recv_ack_msg(src, dst, s) ==
  /\ ack_msg[src][dst][s]
  /\ unacked' = [N1 \in Node |-> [N2 \in Node |-> [K \in Key |-> [V \in Value |-> [S \in Seqnum |->
        IF (N1=src /\ N2=dst /\ S=s) THEN FALSE ELSE unacked[N1][N2][K][V][S]]]]]]
  /\ UNCHANGED<<transfer_msg, ack_msg, seqnum_sent, seqnum_recvd>>
  /\ UNCHANGED<<ctr1, ctr2>>

Next ==
    \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum :
        \/ reshard(n, m, k, v, s)
        \/ drop_transfer_msg(n, m, k, v, s)
        \/ retransmit(n, m, k, v, s)
        \/ recv_transfer_msg(n, m, k, v, s)
        \/ send_ack(n, m, k, v, s)
        \/ drop_ack_msg(n, m, s)
        \/ recv_ack_msg(n, m, s)

Spec == Init /\ [][Next]_vars

======
