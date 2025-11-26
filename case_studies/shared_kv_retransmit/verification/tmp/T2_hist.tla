--------------------------- MODULE T2_hist ---------------------------
EXTENDS Naturals

CONSTANTS Key, Node, Value, Seqnum

VARIABLES Fluent23_18, Fluent24_18, Fluent13_42, Fluent14_42, ack_msg, unacked, Fluent54_28, Fluent55_28

vars == <<Fluent23_18, Fluent24_18, Fluent13_42, Fluent14_42, ack_msg, unacked, Fluent54_28, Fluent55_28>>

CandSep ==
\A var0 \in Value : \E var1 \in Seqnum : \A var2 \in Node : (Fluent54_28[var2][var0][var1]) => (Fluent55_28[var2][var0][var1])

Init ==
/\ unacked = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
/\ ack_msg = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ Fluent54_28 = [ x0 \in Node |-> [ x1 \in Value |-> [ x2 \in Seqnum |-> FALSE]]]
/\ Fluent55_28 = [ x0 \in Node |-> [ x1 \in Value |-> [ x2 \in Seqnum |-> FALSE]]]
/\ Fluent23_18 = [ x0 \in Seqnum |-> [ x1 \in Key |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent24_18 = [ x0 \in Seqnum |-> [ x1 \in Key |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent13_42 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]
/\ Fluent14_42 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]

reshard(n_old,n_new,k,v,s) ==
/\ unacked' = [unacked EXCEPT![n_old][n_new][k][v][s] = TRUE]
/\ UNCHANGED <<ack_msg>>
/\ Fluent54_28' = [Fluent54_28 EXCEPT ![n_old][v][s] = TRUE]
/\ Fluent55_28' = [Fluent55_28 EXCEPT ![n_new][v][s] = TRUE]
/\ UNCHANGED<<>>
/\ Fluent24_18' = [Fluent24_18 EXCEPT ![s][k][n_old] = TRUE]
/\ UNCHANGED<<Fluent23_18, Fluent13_42, Fluent14_42>>

retransmit(src,dst,k,v,s) ==
/\ unacked[src][dst][k][v][s]
/\ UNCHANGED <<unacked,ack_msg>>
/\ Fluent55_28' = [Fluent55_28 EXCEPT ![dst][v][s] = FALSE]
/\ UNCHANGED<<Fluent54_28>>
/\ UNCHANGED<<Fluent23_18, Fluent24_18, Fluent13_42, Fluent14_42>>

send_ack(src,n,k,v,s) ==
/\ ack_msg' = [ack_msg EXCEPT![src][n][s] = TRUE]
/\ UNCHANGED <<unacked>>
/\ UNCHANGED<<Fluent54_28, Fluent55_28>>
/\ UNCHANGED<<Fluent23_18, Fluent24_18, Fluent13_42, Fluent14_42>>

drop_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ ack_msg' = [ack_msg EXCEPT![src][dst][s] = FALSE]
/\ UNCHANGED <<unacked>>
/\ UNCHANGED<<Fluent54_28, Fluent55_28>>
/\ UNCHANGED<<Fluent23_18, Fluent24_18, Fluent13_42, Fluent14_42>>

recv_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ unacked' = [N1 \in Node |-> [N2 \in Node |-> [K \in Key |-> [V \in Value |-> [S \in Seqnum |-> IF ((N1 = src /\ N2 = dst) /\ S = s) THEN FALSE ELSE unacked[N1][N2][K][V][S]]]]]]
/\ UNCHANGED <<ack_msg>>
/\ UNCHANGED<<Fluent54_28, Fluent55_28>>
/\ UNCHANGED<<Fluent23_18, Fluent24_18, Fluent13_42, Fluent14_42>>

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
