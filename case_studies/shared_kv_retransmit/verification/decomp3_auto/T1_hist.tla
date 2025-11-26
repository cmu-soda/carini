--------------------------- MODULE T1_hist ---------------------------
EXTENDS Naturals

CONSTANTS Key, Node, Value, Seqnum

VARIABLES Fluent52_20, Fluent51_20, Fluent20_38, seqnum_sent, ack_msg, seqnum_recvd, unacked, transfer_msg, Fluent19_38

vars == <<Fluent52_20, Fluent51_20, Fluent20_38, seqnum_sent, ack_msg, seqnum_recvd, unacked, transfer_msg, Fluent19_38>>

CandSep ==
/\ \A var0 \in Seqnum : \A var1 \in Node : (Fluent20_38[var0][var1]) => (~(Fluent19_38[var0][var1]))
/\ \A var0 \in Seqnum : \A var1 \in Key : \A var2 \in Node : (Fluent51_20[var0][var2][var1]) => (Fluent52_20[var0][var2][var1])

Init ==
/\ transfer_msg = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
/\ unacked = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
/\ ack_msg = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ seqnum_sent = [n \in Node |-> [s \in Seqnum |-> FALSE]]
/\ seqnum_recvd = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ Fluent52_20 = [ x0 \in Seqnum |-> [ x1 \in Node |-> [ x2 \in Key |-> FALSE]]]
/\ Fluent51_20 = [ x0 \in Seqnum |-> [ x1 \in Node |-> [ x2 \in Key |-> FALSE]]]
/\ Fluent20_38 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]
/\ Fluent19_38 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]

reshard(n_old,n_new,k,v,s) ==
/\ ~(seqnum_sent[n_old][s])
/\ seqnum_sent' = [seqnum_sent EXCEPT![n_old][s] = TRUE]
/\ transfer_msg' = [transfer_msg EXCEPT![n_old][n_new][k][v][s] = TRUE]
/\ unacked' = [unacked EXCEPT![n_old][n_new][k][v][s] = TRUE]
/\ UNCHANGED <<ack_msg,seqnum_recvd>>
/\ Fluent52_20' = [Fluent52_20 EXCEPT ![s][n_old][k] = TRUE]
/\ UNCHANGED<<Fluent51_20, Fluent20_38, Fluent19_38>>

drop_transfer_msg(src,dst,k,v,s) ==
/\ transfer_msg[src][dst][k][v][s]
/\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = FALSE]
/\ UNCHANGED <<unacked,ack_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED<<Fluent52_20, Fluent51_20, Fluent20_38, Fluent19_38>>

retransmit(src,dst,k,v,s) ==
/\ unacked[src][dst][k][v][s]
/\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = TRUE]
/\ UNCHANGED <<unacked,ack_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED<<Fluent52_20, Fluent51_20, Fluent20_38, Fluent19_38>>

recv_transfer_msg(src,n,k,v,s) ==
/\ transfer_msg[src][n][k][v][s]
/\ ~(seqnum_recvd[n][src][s])
/\ seqnum_recvd' = [seqnum_recvd EXCEPT![n][src][s] = TRUE]
/\ UNCHANGED <<unacked,transfer_msg,ack_msg,seqnum_sent>>
/\ Fluent51_20' = [Fluent51_20 EXCEPT ![s][src][k] = TRUE]
/\ Fluent20_38' = [Fluent20_38 EXCEPT ![s][src] = TRUE]
/\ Fluent19_38' = [Fluent19_38 EXCEPT ![s][src] = Fluent20_38[s][src]]
/\ UNCHANGED<<Fluent52_20>>

send_ack(src,n,k,v,s) ==
/\ transfer_msg[src][n][k][v][s]
/\ seqnum_recvd[n][src][s]
/\ ack_msg' = [ack_msg EXCEPT![src][n][s] = TRUE]
/\ UNCHANGED <<unacked,transfer_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED<<Fluent52_20, Fluent51_20, Fluent20_38, Fluent19_38>>

drop_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ ack_msg' = [ack_msg EXCEPT![src][dst][s] = FALSE]
/\ UNCHANGED <<unacked,transfer_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED<<Fluent52_20, Fluent51_20, Fluent20_38, Fluent19_38>>

recv_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ unacked' = [N1 \in Node |-> [N2 \in Node |-> [K \in Key |-> [V \in Value |-> [S \in Seqnum |-> IF ((N1 = src /\ N2 = dst) /\ S = s) THEN FALSE ELSE unacked[N1][N2][K][V][S]]]]]]
/\ UNCHANGED <<transfer_msg,ack_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED<<Fluent52_20, Fluent51_20, Fluent20_38, Fluent19_38>>

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
