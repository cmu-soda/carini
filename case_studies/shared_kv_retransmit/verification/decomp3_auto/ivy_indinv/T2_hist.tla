--------------------------- MODULE T2_hist ---------------------------
EXTENDS Naturals

CONSTANTS Key, Node, Value, Seqnum

VARIABLES ack_msg, fluent95, fluent94, fluent107, unacked, fluent108

vars == <<ack_msg, fluent95, fluent94, fluent107, unacked, fluent108>>

Init ==
/\ unacked = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
/\ ack_msg = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ fluent95 = [ x0 \in Node |-> [ x1 \in Key |-> [ x2 \in Seqnum |-> FALSE]]]
/\ fluent94 = [ x0 \in Node |-> [ x1 \in Key |-> [ x2 \in Seqnum |-> FALSE]]]
/\ fluent107 = [ x0 \in Seqnum |-> [ x1 \in Node |-> [ x2 \in Node |-> FALSE]]]
/\ fluent108 = [ x0 \in Seqnum |-> [ x1 \in Node |-> [ x2 \in Node |-> FALSE]]]

reshard(n_old,n_new,k,v,s) ==
/\ unacked' = [unacked EXCEPT![n_old][n_new][k][v][s] = TRUE]
/\ UNCHANGED <<ack_msg>>
/\ fluent95' = [fluent95 EXCEPT ![n_old][k][s] = TRUE]
/\ fluent107' = [fluent107 EXCEPT ![s][n_new][n_old] = TRUE]
/\ UNCHANGED<<fluent94, fluent108>>

retransmit(src,dst,k,v,s) ==
/\ unacked[src][dst][k][v][s]
/\ UNCHANGED <<unacked,ack_msg>>
/\ fluent94' = [fluent94 EXCEPT ![src][k][s] = TRUE]
/\ fluent108' = [fluent108 EXCEPT ![s][dst][src] = TRUE]
/\ UNCHANGED<<fluent95, fluent107>>

send_ack(src,n,k,v,s) ==
/\ ack_msg' = [ack_msg EXCEPT![src][n][s] = TRUE]
/\ UNCHANGED <<unacked>>
/\ UNCHANGED<<fluent95, fluent94, fluent107, fluent108>>

drop_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ ack_msg' = [ack_msg EXCEPT![src][dst][s] = FALSE]
/\ UNCHANGED <<unacked>>
/\ UNCHANGED<<fluent95, fluent94, fluent107, fluent108>>

recv_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ unacked' = [N1 \in Node |-> [N2 \in Node |-> [K \in Key |-> [V \in Value |-> [S \in Seqnum |-> IF ((N1 = src /\ N2 = dst) /\ S = s) THEN FALSE ELSE unacked[N1][N2][K][V][S]]]]]]
/\ UNCHANGED <<ack_msg>>
/\ UNCHANGED<<fluent95, fluent94, fluent107, fluent108>>

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

Safety ==
/\ \A var0 \in Seqnum : \A var1 \in Node : \A var2 \in Key : (fluent94[var1][var2][var0]) => (fluent95[var1][var2][var0])
/\ \A var0 \in Seqnum : \A var1 \in Node : \A var2 \in Node : (fluent108[var0][var1][var2]) => (fluent107[var0][var1][var2])

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ unacked \in [Node -> [Node -> [Key -> [Value -> [Seqnum -> BOOLEAN]]]]]
/\ ack_msg \in [Node -> [Node -> [Seqnum -> BOOLEAN]]]
/\ fluent95 \in [Node -> [Key -> [Seqnum -> BOOLEAN]]]
/\ fluent94 \in [Node -> [Key -> [Seqnum -> BOOLEAN]]]
/\ fluent107 \in [Seqnum -> [Node -> [Node -> BOOLEAN]]]
/\ fluent108 \in [Seqnum -> [Node -> [Node -> BOOLEAN]]]

Inv1 == ~(\E key0 \in Key, node0 \in Node, node1 \in Node, seqnum0 \in Seqnum, value0 \in Value : ~fluent95[node0][key0][seqnum0] /\ unacked[node0][node1][key0][value0][seqnum0])
Inv2 == ~(\E N \in Node, K \in Key, S \in Seqnum, N1 \in Node, N2 \in Node : fluent94[N][K][S] /\ ~fluent95[N][K][S])
Inv3 == ~(\E key0 \in Key, node0 \in Node, node1 \in Node, seqnum0 \in Seqnum, value0 \in Value : ~fluent107[seqnum0][node1][node0] /\ unacked[node0][node1][key0][value0][seqnum0])
Inv4 == ~(\E N \in Node, K \in Key, S \in Seqnum, N1 \in Node, N2 \in Node : fluent108[S][N1][N2] /\ ~fluent107[S][N1][N2])

IndInv ==
    /\ TypeOK
    /\ Safety
    /\ Inv1
    /\ Inv2
    /\ Inv3
    /\ Inv4

IISpec == IndInv /\ [][Next]_vars
=============================================================================
