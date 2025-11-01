---- MODULE C2 ----

CONSTANTS Key, Node, Value, Seqnum

VARIABLES transfer_msg, seqnum_sent, seqnum_recvd

vars == <<transfer_msg, seqnum_sent, seqnum_recvd>>


Init ==
    /\ transfer_msg = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
    /\ seqnum_sent = [n \in Node |-> [s \in Seqnum |-> FALSE]]
    /\ seqnum_recvd = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]

reshard(n_old, n_new, k, v, s) ==
  /\ ~seqnum_sent[n_old][s]
  /\ seqnum_sent' = [seqnum_sent EXCEPT![n_old][s] = TRUE]
  /\ transfer_msg' = [transfer_msg EXCEPT![n_old][n_new][k][v][s] = TRUE]
  /\ UNCHANGED<<seqnum_recvd>>

drop_transfer_msg(src, dst, k, v, s) ==
  /\ transfer_msg[src][dst][k][v][s]
  /\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = FALSE]
  /\ UNCHANGED<<seqnum_sent, seqnum_recvd>>

retransmit(src, dst, k, v, s) ==
  /\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = TRUE]
  /\ UNCHANGED<<seqnum_sent, seqnum_recvd>>

recv_transfer_msg(src, n, k, v, s) ==
  /\ transfer_msg[src][n][k][v][s]
  /\ ~seqnum_recvd[n][src][s]
  /\ seqnum_recvd' = [seqnum_recvd EXCEPT![n][src][s] = TRUE]
  /\ UNCHANGED<<transfer_msg, seqnum_sent>>

send_ack(src, n, k, v, s) ==
  /\ transfer_msg[src][n][k][v][s]
  /\ seqnum_recvd[n][src][s]
  /\ UNCHANGED<<transfer_msg, seqnum_sent, seqnum_recvd>>

Next ==
    \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum :
        \/ reshard(n, m, k, v, s)
        \/ drop_transfer_msg(n, m, k, v, s)
        \/ retransmit(n, m, k, v, s)
        \/ recv_transfer_msg(n, m, k, v, s)
        \/ send_ack(n, m, k, v, s)

Spec == Init /\ [][Next]_vars

======
