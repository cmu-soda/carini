--------------------------- MODULE C2_hist ---------------------------
EXTENDS Naturals

CONSTANTS Key, Node, Value, Seqnum

VARIABLES Fluent52_20, Fluent51_20, Fluent20_38, seqnum_sent, Fluent95_10, Fluent94_10, seqnum_recvd, Fluent107_45, transfer_msg, Fluent108_45, Fluent19_38

vars == <<Fluent52_20, Fluent51_20, Fluent20_38, seqnum_sent, Fluent95_10, Fluent94_10, seqnum_recvd, Fluent107_45, transfer_msg, Fluent108_45, Fluent19_38>>

CandSep ==
/\ \A var0 \in Seqnum : \A var1 \in Node : \A var2 \in Key : (Fluent94_10[var1][var2][var0]) => (Fluent95_10[var1][var2][var0])
/\ \A var0 \in Seqnum : \A var1 \in Node : \A var2 \in Node : (Fluent108_45[var0][var1][var2]) => (Fluent107_45[var0][var1][var2])

Init ==
/\ transfer_msg = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
/\ seqnum_sent = [n \in Node |-> [s \in Seqnum |-> FALSE]]
/\ seqnum_recvd = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ Fluent95_10 = [ x0 \in Node |-> [ x1 \in Key |-> [ x2 \in Seqnum |-> FALSE]]]
/\ Fluent94_10 = [ x0 \in Node |-> [ x1 \in Key |-> [ x2 \in Seqnum |-> FALSE]]]
/\ Fluent107_45 = [ x0 \in Seqnum |-> [ x1 \in Node |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent108_45 = [ x0 \in Seqnum |-> [ x1 \in Node |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent52_20 = [ x0 \in Seqnum |-> [ x1 \in Node |-> [ x2 \in Key |-> FALSE]]]
/\ Fluent51_20 = [ x0 \in Seqnum |-> [ x1 \in Node |-> [ x2 \in Key |-> FALSE]]]
/\ Fluent20_38 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]
/\ Fluent19_38 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]

reshard(n_old,n_new,k,v,s) ==
/\ ~(seqnum_sent[n_old][s])
/\ seqnum_sent' = [seqnum_sent EXCEPT![n_old][s] = TRUE]
/\ transfer_msg' = [transfer_msg EXCEPT![n_old][n_new][k][v][s] = TRUE]
/\ UNCHANGED <<seqnum_recvd>>
/\ Fluent95_10' = [Fluent95_10 EXCEPT ![n_old][k][s] = TRUE]
/\ Fluent107_45' = [Fluent107_45 EXCEPT ![s][n_new][n_old] = TRUE]
/\ UNCHANGED<<Fluent94_10, Fluent108_45>>
/\ CandSep'
/\ Fluent52_20' = [Fluent52_20 EXCEPT ![s][n_old][k] = TRUE]
/\ UNCHANGED<<Fluent51_20, Fluent20_38, Fluent19_38>>
/\ CandSep'

drop_transfer_msg(src,dst,k,v,s) ==
/\ transfer_msg[src][dst][k][v][s]
/\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = FALSE]
/\ UNCHANGED <<seqnum_sent,seqnum_recvd>>
/\ UNCHANGED<<Fluent95_10, Fluent94_10, Fluent107_45, Fluent108_45>>
/\ CandSep'
/\ UNCHANGED<<Fluent52_20, Fluent51_20, Fluent20_38, Fluent19_38>>
/\ CandSep'

retransmit(src,dst,k,v,s) ==
/\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = TRUE]
/\ UNCHANGED <<seqnum_sent,seqnum_recvd>>
/\ Fluent94_10' = [Fluent94_10 EXCEPT ![src][k][s] = TRUE]
/\ Fluent108_45' = [Fluent108_45 EXCEPT ![s][dst][src] = TRUE]
/\ UNCHANGED<<Fluent95_10, Fluent107_45>>
/\ CandSep'
/\ UNCHANGED<<Fluent52_20, Fluent51_20, Fluent20_38, Fluent19_38>>
/\ CandSep'

recv_transfer_msg(src,n,k,v,s) ==
/\ transfer_msg[src][n][k][v][s]
/\ ~(seqnum_recvd[n][src][s])
/\ seqnum_recvd' = [seqnum_recvd EXCEPT![n][src][s] = TRUE]
/\ UNCHANGED <<transfer_msg,seqnum_sent>>
/\ UNCHANGED<<Fluent95_10, Fluent94_10, Fluent107_45, Fluent108_45>>
/\ CandSep'
/\ Fluent51_20' = [Fluent51_20 EXCEPT ![s][src][k] = TRUE]
/\ Fluent20_38' = [Fluent20_38 EXCEPT ![s][src] = TRUE]
/\ Fluent19_38' = [Fluent19_38 EXCEPT ![s][src] = Fluent20_38[s][src]]
/\ UNCHANGED<<Fluent52_20>>
/\ CandSep'

send_ack(src,n,k,v,s) ==
/\ transfer_msg[src][n][k][v][s]
/\ seqnum_recvd[n][src][s]
/\ UNCHANGED <<transfer_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED<<Fluent95_10, Fluent94_10, Fluent107_45, Fluent108_45>>
/\ CandSep'
/\ UNCHANGED<<Fluent52_20, Fluent51_20, Fluent20_38, Fluent19_38>>
/\ CandSep'

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

Spec == (Init /\ [][Next]_vars)

Safety ==
/\ \A var0 \in Seqnum : \A var1 \in Node : (Fluent20_38[var0][var1]) => (~(Fluent19_38[var0][var1]))
/\ \A var0 \in Seqnum : \A var1 \in Key : \A var2 \in Node : (Fluent51_20[var0][var2][var1]) => (Fluent52_20[var0][var2][var1])
=============================================================================
