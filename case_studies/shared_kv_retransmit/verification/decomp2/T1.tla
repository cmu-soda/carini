---- MODULE T1 ----

CONSTANTS Key, Node, Value, Seqnum

VARIABLES ack_msg, seqnum_sent, seqnum_recvd

vars == <<ack_msg, seqnum_sent, seqnum_recvd>>


Init ==
    /\ ack_msg = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
    /\ seqnum_sent = [n \in Node |-> [s \in Seqnum |-> FALSE]]
    /\ seqnum_recvd = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]

reshard(n_old, n_new, k, v, s) ==
  /\ ~seqnum_sent[n_old][s]
  /\ seqnum_sent' = [seqnum_sent EXCEPT![n_old][s] = TRUE]
  /\ UNCHANGED<<ack_msg, seqnum_recvd>>

recv_transfer_msg(src, n, k, v, s) ==
  /\ ~seqnum_recvd[n][src][s]
  /\ seqnum_recvd' = [seqnum_recvd EXCEPT![n][src][s] = TRUE]
  /\ UNCHANGED<<ack_msg, seqnum_sent>>

send_ack(src, n, k, v, s) ==
  /\ seqnum_recvd[n][src][s]
  /\ ack_msg' = [ack_msg EXCEPT![src][n][s] = TRUE]
  /\ UNCHANGED<<seqnum_sent, seqnum_recvd>>

drop_ack_msg(src, dst, s) ==
  /\ ack_msg[src][dst][s]
  /\ ack_msg' = [ack_msg EXCEPT![src][dst][s] = FALSE]
  /\ UNCHANGED<<seqnum_sent, seqnum_recvd>>

recv_ack_msg(src, dst, s) ==
  /\ ack_msg[src][dst][s]
  /\ UNCHANGED<<ack_msg, seqnum_sent, seqnum_recvd>>

Next ==
    \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum :
        \/ reshard(n, m, k, v, s)
        \*\/ drop_transfer_msg(n, m, k, v, s)
        \*\/ retransmit(n, m, k, v, s)
        \/ recv_transfer_msg(n, m, k, v, s)
        \/ send_ack(n, m, k, v, s)
        \/ drop_ack_msg(n, m, s)
        \/ recv_ack_msg(n, m, s)
        \*\/ put(n, k, v)

Spec == Init /\ [][Next]_vars

======
