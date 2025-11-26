---- MODULE T2 ----
EXTENDS Naturals

CONSTANTS Key, Node, Value, Seqnum

VARIABLES unacked, ack_msg

vars == <<unacked, ack_msg>>


Init ==
  /\ unacked = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
  /\ ack_msg = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]

reshard(n_old, n_new, k, v, s) ==
  /\ unacked' = [unacked EXCEPT![n_old][n_new][k][v][s] = TRUE]
  /\ UNCHANGED<<ack_msg>>

retransmit(src, dst, k, v, s) ==
  /\ unacked[src][dst][k][v][s]
  /\ UNCHANGED<<unacked, ack_msg>>

send_ack(src, n, k, v, s) ==
  /\ ack_msg' = [ack_msg EXCEPT![src][n][s] = TRUE]
  /\ UNCHANGED<<unacked>>

drop_ack_msg(src, dst, s) ==
  /\ ack_msg[src][dst][s]
  /\ ack_msg' = [ack_msg EXCEPT![src][dst][s] = FALSE]
  /\ UNCHANGED<<unacked>>

recv_ack_msg(src, dst, s) ==
  /\ ack_msg[src][dst][s]
  /\ unacked' = [N1 \in Node |-> [N2 \in Node |-> [K \in Key |-> [V \in Value |-> [S \in Seqnum |->
        IF (N1=src /\ N2=dst /\ S=s) THEN FALSE ELSE unacked[N1][N2][K][V][S]]]]]]
  /\ UNCHANGED<<ack_msg>>

Next ==
    \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum :
        \/ reshard(n, m, k, v, s)
        \/ retransmit(n, m, k, v, s)
        \/ send_ack(n, m, k, v, s)
        \/ drop_ack_msg(n, m, s)
        \/ recv_ack_msg(n, m, s)

Spec == Init /\ [][Next]_vars

======
