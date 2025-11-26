--------------------------- MODULE T2_hist ---------------------------
EXTENDS Naturals

CONSTANTS Key, Node, Value, Seqnum

VARIABLES Fluent52_20, Fluent51_20, Fluent20_38, ack_msg, Fluent95_10, Fluent94_10, Fluent107_45, unacked, Fluent108_45, Fluent19_38

vars == <<Fluent52_20, Fluent51_20, Fluent20_38, ack_msg, Fluent95_10, Fluent94_10, Fluent107_45, unacked, Fluent108_45, Fluent19_38>>

CandSep ==
/\ \A var0 \in Seqnum : \A var1 \in Node : \A var2 \in Key : (Fluent94_10[var1][var2][var0]) => (Fluent95_10[var1][var2][var0])
/\ \A var0 \in Seqnum : \A var1 \in Node : \A var2 \in Node : (Fluent108_45[var0][var1][var2]) => (Fluent107_45[var0][var1][var2])

Init ==
/\ unacked = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
/\ ack_msg = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ Fluent95_10 = [ x0 \in Node |-> [ x1 \in Key |-> [ x2 \in Seqnum |-> FALSE]]]
/\ Fluent94_10 = [ x0 \in Node |-> [ x1 \in Key |-> [ x2 \in Seqnum |-> FALSE]]]
/\ Fluent107_45 = [ x0 \in Seqnum |-> [ x1 \in Node |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent108_45 = [ x0 \in Seqnum |-> [ x1 \in Node |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent52_20 = [ x0 \in Seqnum |-> [ x1 \in Node |-> [ x2 \in Key |-> FALSE]]]
/\ Fluent51_20 = [ x0 \in Seqnum |-> [ x1 \in Node |-> [ x2 \in Key |-> FALSE]]]
/\ Fluent20_38 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]
/\ Fluent19_38 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]

reshard(n_old,n_new,k,v,s) ==
/\ unacked' = [unacked EXCEPT![n_old][n_new][k][v][s] = TRUE]
/\ UNCHANGED <<ack_msg>>
/\ Fluent95_10' = [Fluent95_10 EXCEPT ![n_old][k][s] = TRUE]
/\ Fluent107_45' = [Fluent107_45 EXCEPT ![s][n_new][n_old] = TRUE]
/\ UNCHANGED<<Fluent94_10, Fluent108_45>>
/\ Fluent52_20' = [Fluent52_20 EXCEPT ![s][n_old][k] = TRUE]
/\ UNCHANGED<<Fluent51_20, Fluent20_38, Fluent19_38>>

retransmit(src,dst,k,v,s) ==
/\ unacked[src][dst][k][v][s]
/\ UNCHANGED <<unacked,ack_msg>>
/\ Fluent94_10' = [Fluent94_10 EXCEPT ![src][k][s] = TRUE]
/\ Fluent108_45' = [Fluent108_45 EXCEPT ![s][dst][src] = TRUE]
/\ UNCHANGED<<Fluent95_10, Fluent107_45>>
/\ UNCHANGED<<Fluent52_20, Fluent51_20, Fluent20_38, Fluent19_38>>

send_ack(src,n,k,v,s) ==
/\ ack_msg' = [ack_msg EXCEPT![src][n][s] = TRUE]
/\ UNCHANGED <<unacked>>
/\ UNCHANGED<<Fluent95_10, Fluent94_10, Fluent107_45, Fluent108_45>>
/\ UNCHANGED<<Fluent52_20, Fluent51_20, Fluent20_38, Fluent19_38>>

drop_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ ack_msg' = [ack_msg EXCEPT![src][dst][s] = FALSE]
/\ UNCHANGED <<unacked>>
/\ UNCHANGED<<Fluent95_10, Fluent94_10, Fluent107_45, Fluent108_45>>
/\ UNCHANGED<<Fluent52_20, Fluent51_20, Fluent20_38, Fluent19_38>>

recv_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ unacked' = [N1 \in Node |-> [N2 \in Node |-> [K \in Key |-> [V \in Value |-> [S \in Seqnum |-> IF ((N1 = src /\ N2 = dst) /\ S = s) THEN FALSE ELSE unacked[N1][N2][K][V][S]]]]]]
/\ UNCHANGED <<ack_msg>>
/\ UNCHANGED<<Fluent95_10, Fluent94_10, Fluent107_45, Fluent108_45>>
/\ UNCHANGED<<Fluent52_20, Fluent51_20, Fluent20_38, Fluent19_38>>

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
