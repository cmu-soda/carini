--------------------------- MODULE T1_hist ---------------------------


CONSTANTS Key, Node, Value, Seqnum

VARIABLES seqnum_sent, ack_msg, Fluent4_15, seqnum_recvd, unacked, Fluent1_59, Fluent3_15, Fluent2_59

vars == <<seqnum_sent, ack_msg, Fluent4_15, seqnum_recvd, unacked, Fluent1_59, Fluent3_15, Fluent2_59>>

CandSep ==
/\ \A var0 \in Node : (Fluent2_59[var0]) => (Fluent1_59[var0])
/\ \A var0 \in Value : (Fluent3_15[var0]) => (Fluent4_15[var0])

Init ==
/\ unacked = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
/\ ack_msg = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ seqnum_sent = [n \in Node |-> [s \in Seqnum |-> FALSE]]
/\ seqnum_recvd = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ Fluent4_15 = [ x0 \in Value |-> FALSE]
/\ Fluent1_59 = [ x0 \in Node |-> FALSE]
/\ Fluent3_15 = [ x0 \in Value |-> FALSE]
/\ Fluent2_59 = [ x0 \in Node |-> FALSE]

reshard(n_old,n_new,k,v,s) ==
/\ ~(seqnum_sent[n_old][s])
/\ seqnum_sent' = [seqnum_sent EXCEPT![n_old][s] = TRUE]
/\ unacked' = [unacked EXCEPT![n_old][n_new][k][v][s] = TRUE]
/\ UNCHANGED <<ack_msg,seqnum_recvd>>
/\ Fluent4_15' = [Fluent4_15 EXCEPT ![v] = TRUE]
/\ Fluent1_59' = [Fluent1_59 EXCEPT ![n_old] = TRUE]
/\ UNCHANGED<<Fluent3_15, Fluent2_59>>

retransmit(src,dst,k,v,s) ==
/\ unacked[src][dst][k][v][s]
/\ UNCHANGED <<unacked,ack_msg,seqnum_sent,seqnum_recvd>>
/\ Fluent3_15' = [Fluent3_15 EXCEPT ![v] = TRUE]
/\ Fluent2_59' = [Fluent2_59 EXCEPT ![src] = TRUE]
/\ UNCHANGED<<Fluent4_15, Fluent1_59>>

recv_transfer_msg(src,n,k,v,s) ==
/\ ~(seqnum_recvd[n][src][s])
/\ seqnum_recvd' = [seqnum_recvd EXCEPT![n][src][s] = TRUE]
/\ UNCHANGED <<unacked,ack_msg,seqnum_sent>>
/\ UNCHANGED<<Fluent4_15, Fluent1_59, Fluent3_15, Fluent2_59>>

send_ack(src,n,k,v,s) ==
/\ seqnum_recvd[n][src][s]
/\ ack_msg' = [ack_msg EXCEPT![src][n][s] = TRUE]
/\ UNCHANGED <<unacked,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED<<Fluent4_15, Fluent1_59, Fluent3_15, Fluent2_59>>

drop_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ ack_msg' = [ack_msg EXCEPT![src][dst][s] = FALSE]
/\ UNCHANGED <<unacked,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED<<Fluent4_15, Fluent1_59, Fluent3_15, Fluent2_59>>

recv_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ unacked' = [N1 \in Node |-> [N2 \in Node |-> [K \in Key |-> [V \in Value |-> [S \in Seqnum |-> IF ((N1 = src /\ N2 = dst) /\ S = s) THEN FALSE ELSE unacked[N1][N2][K][V][S]]]]]]
/\ UNCHANGED <<ack_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED<<Fluent4_15, Fluent1_59, Fluent3_15, Fluent2_59>>

Next ==
\E n,m \in Node :
\E k \in Key :
\E v \in Value :
\E s \in Seqnum :
\/ reshard(n,m,k,v,s)
\/ retransmit(n,m,k,v,s)
\/ recv_transfer_msg(n,m,k,v,s)
\/ send_ack(n,m,k,v,s)
\/ drop_ack_msg(n,m,s)
\/ recv_ack_msg(n,m,s)

Spec == (Init /\ [][Next]_vars)
=============================================================================
