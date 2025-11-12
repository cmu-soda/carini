---- MODULE ShardedKvRetransmit ----

CONSTANTS Key, Node, Value, Seqnum

\*mutable relation table(node, key, value)
\*mutable relation unacked(node, node, key, value, seqnum)
\*mutable relation owner(node, key)
\*mutable relation transfer_msg(node, node, key, value, seqnum)
\*mutable relation ack_msg(node, node, seqnum)
\*mutable relation seqnum_sent(node, seqnum)
\*mutable relation seqnum_recvd(node, node, seqnum)
VARIABLES table, unacked, owner, transfer_msg, ack_msg, seqnum_sent, seqnum_recvd

vars == <<table, unacked, owner, transfer_msg, ack_msg, seqnum_sent, seqnum_recvd>>


Init ==
    \*init !table(N, K, V)
    /\ table = [n \in Node |-> [k \in Key |-> [v \in Value |-> FALSE]]]
    \*init !transfer_msg(SRC, DST, K, V, S)
    /\ transfer_msg = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
    \*init owner(N1, K) & owner(N2, K) -> N1 = N2
    /\ owner \in [Node -> [Key -> BOOLEAN]]
    /\ \A N1,N2 \in Node : \A K \in Key : (owner[N1][K] /\ owner[N2][K]) => (N1 = N2)

    \*init !unacked(SRC, DST, K, V, S)
    /\ unacked = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
    \*init !ack_msg(SRC, DST, S)
    /\ ack_msg = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
    \*init !seqnum_sent(N, S)
    /\ seqnum_sent = [n \in Node |-> [s \in Seqnum |-> FALSE]]
    \*init !seqnum_recvd(N, SENDER, S)
    /\ seqnum_recvd = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]

\*transition reshard(n_old: node, n_new: node, k: key, v: value, s: seqnum)
reshard(n_old, n_new, k, v, s) ==
  \*table(n_old, k, v) &
  /\ table[n_old][k][v]

  \*!seqnum_sent(n_old, s) &
  /\ ~seqnum_sent[n_old][s]

  \*(new(seqnum_sent(N, S)) <-> seqnum_sent(N, S) | N = n_old & S = s) &
  /\ seqnum_sent' = [seqnum_sent EXCEPT![n_old][s] = TRUE]

  \*(new(table(N, K, V)) <-> table(N, K, V) & !(N = n_old & K = k & V = v)) &
  /\ table' = [table EXCEPT![n_old][k][v] = FALSE]

  \*(new(owner(N, K)) <-> owner(N, K) & !(N = n_old & K = k)) &
  /\ owner' = [owner EXCEPT![n_old][k] = FALSE]

  \*(new(transfer_msg(N1, N2, K, V, S)) <-> transfer_msg(N1, N2, K, V, S) | N1 = n_old & N2 = n_new & K = k & V = v & S = s) &
  /\ transfer_msg' = [transfer_msg EXCEPT![n_old][n_new][k][v][s] = TRUE]

  \*(new(unacked(N1, N2, K, V, S)) <-> unacked(N1, N2, K, V, S) | N1 = n_old & N2 = n_new & K = k & V = v & S = s)
  /\ unacked' = [unacked EXCEPT![n_old][n_new][k][v][s] = TRUE]

  \*modifies table, owner, seqnum_sent, transfer_msg, unacked
  /\ UNCHANGED<<ack_msg, seqnum_recvd>>

\*transition drop_transfer_msg(src: node, dst: node, k: key, v: value, s: seqnum)
drop_transfer_msg(src, dst, k, v, s) ==
  \*transfer_msg(src, dst, k, v, s) &
  /\ transfer_msg[src][dst][k][v][s]

  \*(new(transfer_msg(N1, N2, K, V, S)) <-> transfer_msg(N1, N2, K, V, S) & !(N1 = src & N2 = dst & K = k & V = v & S = s))
  /\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = FALSE]

  \*modifies transfer_msg
  /\ UNCHANGED<<table, unacked, owner, ack_msg, seqnum_sent, seqnum_recvd>>

\*transition retransmit(src: node, dst: node, k: key, v: value, s: seqnum)
retransmit(src, dst, k, v, s) ==
  \*unacked(src, dst, k, v, s) &
  /\ unacked[src][dst][k][v][s]

  \*(new(transfer_msg(N1, N2, K, V, S)) <-> transfer_msg(N1, N2, K, V, S) | N1 = src & N2 = dst & K = k & V = v & S = s)
  /\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = TRUE]

  \*modifies transfer_msg
  /\ UNCHANGED<<table, unacked, owner, ack_msg, seqnum_sent, seqnum_recvd>>

\*transition recv_transfer_msg(src: node, n: node, k: key, v: value, s: seqnum)
recv_transfer_msg(src, n, k, v, s) ==
  \*transfer_msg(src, n, k, v, s) &
  /\ transfer_msg[src][n][k][v][s]

  \*!seqnum_recvd(n, src, s) &
  /\ ~seqnum_recvd[n][src][s]

  \*(new(seqnum_recvd(N1, N2, S)) <-> seqnum_recvd(N1, N2, S) | N1 = n & N2 = src & S = s) &
  /\ seqnum_recvd' = [seqnum_recvd EXCEPT![n][src][s] = TRUE]

  \*(new(table(N, K, V)) <-> table(N, K, V) | (N = n & K = k & V = v)) &
  /\ table' = [table EXCEPT![n][k][v] = TRUE]

  \*(new(owner(N, K)) <-> owner(N, K) | N = n & K = k)
  /\ owner' = [owner EXCEPT![n][k] = TRUE]

  \*modifies seqnum_recvd, table, owner
  /\ UNCHANGED<<unacked, transfer_msg, ack_msg, seqnum_sent>>

\*transition send_ack(src: node, n: node, k: key, v: value, s: seqnum)
send_ack(src, n, k, v, s) ==
  \*transfer_msg(src, n, k, v, s) &
  /\ transfer_msg[src][n][k][v][s]

  \*seqnum_recvd(n, src, s) &
  /\ seqnum_recvd[n][src][s]

  \*(new(ack_msg(N1, N2, S)) <-> ack_msg(N1, N2, S) | N1 = src & N2 = n & S = s)
  /\ ack_msg' = [ack_msg EXCEPT![src][n][s] = TRUE]

  \*modifies ack_msg
  /\ UNCHANGED<<table, unacked, owner, transfer_msg, seqnum_sent, seqnum_recvd>>

\*transition drop_ack_msg(src: node, dst:node, s: seqnum)
drop_ack_msg(src, dst, s) ==
  \*ack_msg(src, dst, s) &
  /\ ack_msg[src][dst][s]

  \*(new(ack_msg(N1, N2, S)) <-> ack_msg(N1, N2, S) & !(N1 = src & N2 = dst & S = s))
  /\ ack_msg' = [ack_msg EXCEPT![src][dst][s] = FALSE]

  \*modifies ack_msg
  /\ UNCHANGED<<table, unacked, owner, transfer_msg, seqnum_sent, seqnum_recvd>>

\*transition recv_ack_msg(src: node, dst: node, s: seqnum)
recv_ack_msg(src, dst, s) ==
  \*ack_msg(src, dst, s) &
  /\ ack_msg[src][dst][s]

  \*(!(N1 = src & N2 = dst & S = s) -> (new(unacked(N1, N2, K, V, S)) <-> unacked(N1, N2, K, V, S))) &
  \*(!new(unacked(src, dst, K, V, s)))
  /\ unacked' = [N1 \in Node |-> [N2 \in Node |-> [K \in Key |-> [V \in Value |-> [S \in Seqnum |->
        IF (N1=src /\ N2=dst /\ S=s) THEN FALSE ELSE unacked[N1][N2][K][V][S]]]]]]

  \*modifies unacked
  /\ UNCHANGED<<table, owner, transfer_msg, ack_msg, seqnum_sent, seqnum_recvd>>

\*transition put(n: node, k: key, v: value)
put(n, k, v) ==
  \*owner(n, k) &
  /\ owner[n][k]

  \*(!(N = n & K = k) -> (new(table(N, K, V)) <-> table(N, K, V))) &
  \*(new(table(n, k, V)) <-> V = v)
  /\ table' = [table EXCEPT![n][k] = [V \in Value |-> (V=v)]]

  \*modifies table
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
