--------------------------- MODULE T1_hist ---------------------------
EXTENDS Naturals

CONSTANTS Key, Node, Value, Seqnum

VARIABLES Fluent23_18, Fluent24_18, Fluent13_42, Fluent14_42, seqnum_sent, ack_msg, seqnum_recvd, unacked, transfer_msg

vars == <<Fluent23_18, Fluent24_18, Fluent13_42, Fluent14_42, seqnum_sent, ack_msg, seqnum_recvd, unacked, transfer_msg>>

CandSep ==
/\ \A var0 \in Key : \A var1 \in Seqnum : \A var2 \in Node : (Fluent23_18[var1][var0][var2]) => (Fluent24_18[var1][var0][var2])
/\ \A var0 \in Seqnum : \A var1 \in Node : (Fluent13_42[var0][var1]) => (~(Fluent14_42[var0][var1]))

Init ==
/\ transfer_msg = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
/\ unacked = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
/\ ack_msg = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ seqnum_sent = [n \in Node |-> [s \in Seqnum |-> FALSE]]
/\ seqnum_recvd = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ Fluent23_18 = [ x0 \in Seqnum |-> [ x1 \in Key |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent24_18 = [ x0 \in Seqnum |-> [ x1 \in Key |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent13_42 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]
/\ Fluent14_42 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]

reshard(n_old,n_new,k,v,s) ==
/\ ~(seqnum_sent[n_old][s])
/\ seqnum_sent' = [seqnum_sent EXCEPT![n_old][s] = TRUE]
/\ transfer_msg' = [transfer_msg EXCEPT![n_old][n_new][k][v][s] = TRUE]
/\ unacked' = [unacked EXCEPT![n_old][n_new][k][v][s] = TRUE]
/\ UNCHANGED <<ack_msg,seqnum_recvd>>
/\ Fluent24_18' = [Fluent24_18 EXCEPT ![s][k][n_old] = TRUE]
/\ UNCHANGED<<Fluent23_18, Fluent13_42, Fluent14_42>>

drop_transfer_msg(src,dst,k,v,s) ==
/\ transfer_msg[src][dst][k][v][s]
/\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = FALSE]
/\ UNCHANGED <<unacked,ack_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED<<Fluent23_18, Fluent24_18, Fluent13_42, Fluent14_42>>

retransmit(src,dst,k,v,s) ==
/\ unacked[src][dst][k][v][s]
/\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = TRUE]
/\ UNCHANGED <<unacked,ack_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED<<Fluent23_18, Fluent24_18, Fluent13_42, Fluent14_42>>

recv_transfer_msg(src,n,k,v,s) ==
/\ transfer_msg[src][n][k][v][s]
/\ ~(seqnum_recvd[n][src][s])
/\ seqnum_recvd' = [seqnum_recvd EXCEPT![n][src][s] = TRUE]
/\ UNCHANGED <<unacked,transfer_msg,ack_msg,seqnum_sent>>
/\ Fluent23_18' = [Fluent23_18 EXCEPT ![s][k][src] = TRUE]
/\ Fluent13_42' = [Fluent13_42 EXCEPT ![s][src] = Fluent14_42[s][src]]
/\ Fluent14_42' = [Fluent14_42 EXCEPT ![s][src] = TRUE]
/\ UNCHANGED<<Fluent24_18>>

send_ack(src,n,k,v,s) ==
/\ transfer_msg[src][n][k][v][s]
/\ seqnum_recvd[n][src][s]
/\ ack_msg' = [ack_msg EXCEPT![src][n][s] = TRUE]
/\ UNCHANGED <<unacked,transfer_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED<<Fluent23_18, Fluent24_18, Fluent13_42, Fluent14_42>>

drop_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ ack_msg' = [ack_msg EXCEPT![src][dst][s] = FALSE]
/\ UNCHANGED <<unacked,transfer_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED<<Fluent23_18, Fluent24_18, Fluent13_42, Fluent14_42>>

recv_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ unacked' = [N1 \in Node |-> [N2 \in Node |-> [K \in Key |-> [V \in Value |-> [S \in Seqnum |-> IF ((N1 = src /\ N2 = dst) /\ S = s) THEN FALSE ELSE unacked[N1][N2][K][V][S]]]]]]
/\ UNCHANGED <<transfer_msg,ack_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED<<Fluent23_18, Fluent24_18, Fluent13_42, Fluent14_42>>

Next ==
\E n,m \in Node :
\E k \in Key :
\E v \in Value :
\E s \in Seqnum :
\/ reshard(n,m,k,v,s)
\/ drop_transfer_msg(n,m,k,v,s)
\/ retransmit(n,m,k,v,s)
\/ recv_transfer_msg(n,m,k,v,s)
\/ send_ack(n,m,k,v,s)
\/ drop_ack_msg(n,m,s)
\/ recv_ack_msg(n,m,s)

Spec == (Init /\ [][Next]_vars)
=============================================================================
