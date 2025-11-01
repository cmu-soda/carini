---- MODULE T2_hist ----

CONSTANTS Key, Node, Value, Seqnum

VARIABLES unacked, ack_msg, rectr1, rectr2

vars == <<unacked, ack_msg, rectr1, rectr2>>

CandSep ==
/\ \A n \in Node : \A m \in Node : \A k \in Key : \A v \in Value : \A s \in Seqnum : ~rectr2[n][m][k][v][s]


Init ==
    /\ unacked = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
    /\ ack_msg = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
    /\ rectr1 = [n \in Node |-> [m \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> TRUE]]]]]
    /\ rectr2 = [n \in Node |-> [m \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]

reshard(n_old, n_new, k, v, s) ==
  /\ unacked' = [unacked EXCEPT![n_old][n_new][k][v][s] = TRUE]
  /\ UNCHANGED<<ack_msg>>
  /\ rectr1' = [rectr1 EXCEPT![n_old][n_new][k][v][s] = FALSE]
  /\ rectr2' = [rectr2 EXCEPT![n_old][n_new][k][v][s] = FALSE]

retransmit(src, dst, k, v, s) ==
  /\ unacked[src][dst][k][v][s]
  /\ UNCHANGED<<unacked, ack_msg>>
  /\ rectr2' = [rectr2 EXCEPT![src][dst][k][v][s] = rectr1[src][dst][k][v][s]]
  /\ UNCHANGED<<rectr1>>

send_ack(src, n, k, v, s) ==
  /\ ack_msg' = [ack_msg EXCEPT![src][n][s] = TRUE]
  /\ UNCHANGED<<unacked>>
  /\ UNCHANGED<<rectr1,rectr2>>

drop_ack_msg(src, dst, s) ==
  /\ ack_msg[src][dst][s]
  /\ ack_msg' = [ack_msg EXCEPT![src][dst][s] = FALSE]
  /\ UNCHANGED<<unacked>>
  /\ UNCHANGED<<rectr1,rectr2>>

recv_ack_msg(src, dst, s) ==
  /\ ack_msg[src][dst][s]
  /\ unacked' = [N1 \in Node |-> [N2 \in Node |-> [K \in Key |-> [V \in Value |-> [S \in Seqnum |->
        IF (N1=src /\ N2=dst /\ S=s) THEN FALSE ELSE unacked[N1][N2][K][V][S]]]]]]
  /\ UNCHANGED<<ack_msg>>
  /\ UNCHANGED<<rectr1,rectr2>>

Next ==
    \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum :
        \/ reshard(n, m, k, v, s)
        \/ retransmit(n, m, k, v, s)
        \/ send_ack(n, m, k, v, s)
        \/ drop_ack_msg(n, m, s)
        \/ recv_ack_msg(n, m, s)

Spec == Init /\ [][Next]_vars

======
