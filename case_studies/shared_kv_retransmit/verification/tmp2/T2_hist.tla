--------------------------- MODULE T2_hist ---------------------------
EXTENDS Naturals

CONSTANTS Key, Node, Value, Seqnum

VARIABLES Fluent124_46, Fluent20_37, Fluent21_37, Fluent113_12, Fluent125_46, Fluent114_12, ack_msg, unacked, Fluent67_18, Fluent66_18

vars == <<Fluent124_46, Fluent20_37, Fluent21_37, Fluent113_12, Fluent125_46, Fluent114_12, ack_msg, unacked, Fluent67_18, Fluent66_18>>

CandSep ==
/\ \A var0 \in Key : \A var1 \in Node : \A var2 \in Seqnum : (Fluent114_12[var0][var1][var2]) => (Fluent113_12[var0][var1][var2])
/\ \A var0 \in Node : \A var1 \in Node : \A var2 \in Seqnum : (Fluent124_46[var0][var1][var2]) => (Fluent125_46[var0][var1][var2])

Init ==
/\ unacked = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
/\ ack_msg = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ Fluent124_46 = [ x0 \in Node |-> [ x1 \in Node |-> [ x2 \in Seqnum |-> FALSE]]]
/\ Fluent113_12 = [ x0 \in Key |-> [ x1 \in Node |-> [ x2 \in Seqnum |-> FALSE]]]
/\ Fluent125_46 = [ x0 \in Node |-> [ x1 \in Node |-> [ x2 \in Seqnum |-> FALSE]]]
/\ Fluent114_12 = [ x0 \in Key |-> [ x1 \in Node |-> [ x2 \in Seqnum |-> FALSE]]]
/\ Fluent20_37 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]
/\ Fluent21_37 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]
/\ Fluent67_18 = [ x0 \in Key |-> [ x1 \in Seqnum |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent66_18 = [ x0 \in Key |-> [ x1 \in Seqnum |-> [ x2 \in Node |-> FALSE]]]

reshard(n_old,n_new,k,v,s) ==
/\ unacked' = [unacked EXCEPT![n_old][n_new][k][v][s] = TRUE]
/\ UNCHANGED <<ack_msg>>
/\ Fluent113_12' = [Fluent113_12 EXCEPT ![k][n_old][s] = TRUE]
/\ Fluent125_46' = [Fluent125_46 EXCEPT ![n_new][n_old][s] = TRUE]
/\ UNCHANGED<<Fluent124_46, Fluent114_12>>
/\ Fluent67_18' = [Fluent67_18 EXCEPT ![k][s][n_old] = TRUE]
/\ UNCHANGED<<Fluent20_37, Fluent21_37, Fluent66_18>>

retransmit(src,dst,k,v,s) ==
/\ unacked[src][dst][k][v][s]
/\ UNCHANGED <<unacked,ack_msg>>
/\ Fluent124_46' = [Fluent124_46 EXCEPT ![dst][src][s] = TRUE]
/\ Fluent114_12' = [Fluent114_12 EXCEPT ![k][src][s] = TRUE]
/\ UNCHANGED<<Fluent113_12, Fluent125_46>>
/\ UNCHANGED<<Fluent20_37, Fluent21_37, Fluent67_18, Fluent66_18>>

send_ack(src,n,k,v,s) ==
/\ ack_msg' = [ack_msg EXCEPT![src][n][s] = TRUE]
/\ UNCHANGED <<unacked>>
/\ UNCHANGED<<Fluent124_46, Fluent113_12, Fluent125_46, Fluent114_12>>
/\ UNCHANGED<<Fluent20_37, Fluent21_37, Fluent67_18, Fluent66_18>>

drop_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ ack_msg' = [ack_msg EXCEPT![src][dst][s] = FALSE]
/\ UNCHANGED <<unacked>>
/\ UNCHANGED<<Fluent124_46, Fluent113_12, Fluent125_46, Fluent114_12>>
/\ UNCHANGED<<Fluent20_37, Fluent21_37, Fluent67_18, Fluent66_18>>

recv_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ unacked' = [N1 \in Node |-> [N2 \in Node |-> [K \in Key |-> [V \in Value |-> [S \in Seqnum |-> IF ((N1 = src /\ N2 = dst) /\ S = s) THEN FALSE ELSE unacked[N1][N2][K][V][S]]]]]]
/\ UNCHANGED <<ack_msg>>
/\ UNCHANGED<<Fluent124_46, Fluent113_12, Fluent125_46, Fluent114_12>>
/\ UNCHANGED<<Fluent20_37, Fluent21_37, Fluent67_18, Fluent66_18>>

Next ==
\E n,m \in Node :
\E k \in Key :
\E v \in Value :
\E s \in Seqnum :
\/ reshard(n,m,k,v,s)
\/ retransmit(n,m,k,v,s)
\/ send_ack(n,m,k,v,s)
\/ drop_ack_msg(n,m,s)
\/ recv_ack_msg(n,m,s)

Spec == (Init /\ [][Next]_vars)
=============================================================================
