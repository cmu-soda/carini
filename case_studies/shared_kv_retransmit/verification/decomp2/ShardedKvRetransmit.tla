---- MODULE ShardedKvRetransmit ----

CONSTANTS Key, Node, Value, Seqnum

VARIABLES table, unacked, owner, transfer_msg, ack_msg, seqnum_sent, seqnum_recvd

vars == <<table, unacked, owner, transfer_msg, ack_msg, seqnum_sent, seqnum_recvd>>


Init ==
    /\ table = [n \in Node |-> [k \in Key |-> [v \in Value |-> FALSE]]]
    /\ transfer_msg = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
    /\ owner \in [Node -> [Key -> BOOLEAN]]
    /\ \A N1,N2 \in Node : \A K \in Key : (owner[N1][K] /\ owner[N2][K]) => (N1 = N2)

    /\ unacked = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
    /\ ack_msg = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
    /\ seqnum_sent = [n \in Node |-> [s \in Seqnum |-> FALSE]]
    /\ seqnum_recvd = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]

reshard(n_old, n_new, k, v, s) ==
  /\ table[n_old][k][v]
  /\ ~seqnum_sent[n_old][s]
  /\ seqnum_sent' = [seqnum_sent EXCEPT![n_old][s] = TRUE]
  /\ table' = [table EXCEPT![n_old][k][v] = FALSE]
  /\ owner' = [owner EXCEPT![n_old][k] = FALSE]
  /\ transfer_msg' = [transfer_msg EXCEPT![n_old][n_new][k][v][s] = TRUE]
  /\ unacked' = [unacked EXCEPT![n_old][n_new][k][v][s] = TRUE]
  /\ UNCHANGED<<ack_msg, seqnum_recvd>>

drop_transfer_msg(src, dst, k, v, s) ==
  /\ transfer_msg[src][dst][k][v][s]
  /\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = FALSE]
  /\ UNCHANGED<<table, unacked, owner, ack_msg, seqnum_sent, seqnum_recvd>>

retransmit(src, dst, k, v, s) ==
  /\ unacked[src][dst][k][v][s]
  /\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = TRUE]
  /\ UNCHANGED<<table, unacked, owner, ack_msg, seqnum_sent, seqnum_recvd>>

recv_transfer_msg(src, n, k, v, s) ==
  /\ transfer_msg[src][n][k][v][s]
  /\ ~seqnum_recvd[n][src][s]
  /\ seqnum_recvd' = [seqnum_recvd EXCEPT![n][src][s] = TRUE]
  /\ table' = [table EXCEPT![n][k][v] = TRUE]
  /\ owner' = [owner EXCEPT![n][k] = TRUE]
  /\ UNCHANGED<<unacked, transfer_msg, ack_msg, seqnum_sent>>

send_ack(src, n, k, v, s) ==
  /\ transfer_msg[src][n][k][v][s]
  /\ seqnum_recvd[n][src][s]
  /\ ack_msg' = [ack_msg EXCEPT![src][n][s] = TRUE]
  /\ UNCHANGED<<table, unacked, owner, transfer_msg, seqnum_sent, seqnum_recvd>>

drop_ack_msg(src, dst, s) ==
  /\ ack_msg[src][dst][s]
  /\ ack_msg' = [ack_msg EXCEPT![src][dst][s] = FALSE]
  /\ UNCHANGED<<table, unacked, owner, transfer_msg, seqnum_sent, seqnum_recvd>>

recv_ack_msg(src, dst, s) ==
  /\ ack_msg[src][dst][s]
  /\ unacked' = [N1 \in Node |-> [N2 \in Node |-> [K \in Key |-> [V \in Value |-> [S \in Seqnum |->
        IF (N1=src /\ N2=dst /\ S=s) THEN FALSE ELSE unacked[N1][N2][K][V][S]]]]]]
  /\ UNCHANGED<<table, owner, transfer_msg, ack_msg, seqnum_sent, seqnum_recvd>>

put(n, k, v) ==
  /\ owner[n][k]
  /\ table' = [table EXCEPT![n][k] = [V \in Value |-> (V=v)]]
  /\ UNCHANGED<<unacked, owner, transfer_msg, ack_msg, seqnum_sent, seqnum_recvd>>

Next ==
    \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum :
        \/ reshard(n, m, k, v, s)
        \/ drop_transfer_msg(n, m, k, v, s)
        \/ retransmit(n, m, k, v, s)
        \/ recv_transfer_msg(n, m, k, v, s)
        \/ send_ack(n, m, k, v, s)
        \/ drop_ack_msg(n, m, s)
        \/ recv_ack_msg(n, m, s)
        \/ put(n, k, v)

Spec == Init /\ [][Next]_vars

\*safety [keys_unique] table(N1, K, V1) & table(N2, K, V2) -> N1 = N2 & V1 = V2
Safety ==
    \A N1,N2 \in Node : \A K \in Key : \A V1,V2 \in Value :
        (table[N1][K][V1] /\ table[N2][K][V2]) => (N1 = N2 /\ V1 = V2)

======
