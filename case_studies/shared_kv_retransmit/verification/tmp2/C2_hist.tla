--------------------------- MODULE C2_hist ---------------------------
EXTENDS Naturals

CONSTANTS Key, Node, Value, Seqnum

VARIABLES Fluent124_46, Fluent20_37, Fluent21_37, Fluent113_12, Fluent125_46, Fluent114_12, seqnum_sent, seqnum_recvd, transfer_msg, Fluent67_18, Fluent66_18

vars == <<Fluent124_46, Fluent20_37, Fluent21_37, Fluent113_12, Fluent125_46, Fluent114_12, seqnum_sent, seqnum_recvd, transfer_msg, Fluent67_18, Fluent66_18>>

CandSep ==
/\ \A var0 \in Key : \A var1 \in Node : \A var2 \in Seqnum : (Fluent114_12[var0][var1][var2]) => (Fluent113_12[var0][var1][var2])
/\ \A var0 \in Node : \A var1 \in Node : \A var2 \in Seqnum : (Fluent124_46[var0][var1][var2]) => (Fluent125_46[var0][var1][var2])

Init ==
/\ transfer_msg = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
/\ seqnum_sent = [n \in Node |-> [s \in Seqnum |-> FALSE]]
/\ seqnum_recvd = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ Fluent124_46 = [ x0 \in Node |-> [ x1 \in Node |-> [ x2 \in Seqnum |-> FALSE]]]
/\ Fluent113_12 = [ x0 \in Key |-> [ x1 \in Node |-> [ x2 \in Seqnum |-> FALSE]]]
/\ Fluent125_46 = [ x0 \in Node |-> [ x1 \in Node |-> [ x2 \in Seqnum |-> FALSE]]]
/\ Fluent114_12 = [ x0 \in Key |-> [ x1 \in Node |-> [ x2 \in Seqnum |-> FALSE]]]
/\ Fluent20_37 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]
/\ Fluent21_37 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]
/\ Fluent67_18 = [ x0 \in Key |-> [ x1 \in Seqnum |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent66_18 = [ x0 \in Key |-> [ x1 \in Seqnum |-> [ x2 \in Node |-> FALSE]]]

reshard(n_old,n_new,k,v,s) ==
/\ ~(seqnum_sent[n_old][s])
/\ seqnum_sent' = [seqnum_sent EXCEPT![n_old][s] = TRUE]
/\ transfer_msg' = [transfer_msg EXCEPT![n_old][n_new][k][v][s] = TRUE]
/\ UNCHANGED <<seqnum_recvd>>
/\ Fluent113_12' = [Fluent113_12 EXCEPT ![k][n_old][s] = TRUE]
/\ Fluent125_46' = [Fluent125_46 EXCEPT ![n_new][n_old][s] = TRUE]
/\ UNCHANGED<<Fluent124_46, Fluent114_12>>
/\ CandSep'
/\ Fluent67_18' = [Fluent67_18 EXCEPT ![k][s][n_old] = TRUE]
/\ UNCHANGED<<Fluent20_37, Fluent21_37, Fluent66_18>>
/\ CandSep'

drop_transfer_msg(src,dst,k,v,s) ==
/\ transfer_msg[src][dst][k][v][s]
/\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = FALSE]
/\ UNCHANGED <<seqnum_sent,seqnum_recvd>>
/\ UNCHANGED<<Fluent124_46, Fluent113_12, Fluent125_46, Fluent114_12>>
/\ CandSep'
/\ UNCHANGED<<Fluent20_37, Fluent21_37, Fluent67_18, Fluent66_18>>
/\ CandSep'

retransmit(src,dst,k,v,s) ==
/\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = TRUE]
/\ UNCHANGED <<seqnum_sent,seqnum_recvd>>
/\ Fluent124_46' = [Fluent124_46 EXCEPT ![dst][src][s] = TRUE]
/\ Fluent114_12' = [Fluent114_12 EXCEPT ![k][src][s] = TRUE]
/\ UNCHANGED<<Fluent113_12, Fluent125_46>>
/\ CandSep'
/\ UNCHANGED<<Fluent20_37, Fluent21_37, Fluent67_18, Fluent66_18>>
/\ CandSep'

recv_transfer_msg(src,n,k,v,s) ==
/\ transfer_msg[src][n][k][v][s]
/\ ~(seqnum_recvd[n][src][s])
/\ seqnum_recvd' = [seqnum_recvd EXCEPT![n][src][s] = TRUE]
/\ UNCHANGED <<transfer_msg,seqnum_sent>>
/\ UNCHANGED<<Fluent124_46, Fluent113_12, Fluent125_46, Fluent114_12>>
/\ CandSep'
/\ Fluent20_37' = [Fluent20_37 EXCEPT ![s][src] = Fluent21_37[s][src]]
/\ Fluent21_37' = [Fluent21_37 EXCEPT ![s][src] = TRUE]
/\ Fluent66_18' = [Fluent66_18 EXCEPT ![k][s][src] = TRUE]
/\ UNCHANGED<<Fluent67_18>>
/\ CandSep'

send_ack(src,n,k,v,s) ==
/\ transfer_msg[src][n][k][v][s]
/\ seqnum_recvd[n][src][s]
/\ UNCHANGED <<transfer_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED<<Fluent124_46, Fluent113_12, Fluent125_46, Fluent114_12>>
/\ CandSep'
/\ UNCHANGED<<Fluent20_37, Fluent21_37, Fluent67_18, Fluent66_18>>
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
/\ \A var0 \in Key : \A var1 \in Seqnum : \A var2 \in Node : (Fluent66_18[var0][var1][var2]) => (Fluent67_18[var0][var1][var2])
/\ \A var0 \in Node : \A var1 \in Seqnum : (Fluent20_37[var1][var0]) => (~(Fluent21_37[var1][var0]))
=============================================================================
