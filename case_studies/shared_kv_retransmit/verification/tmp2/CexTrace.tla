--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS Seqnum, n1, n2, k1, k2, Node, NUM2, k3, NUM1, Value, v1, v2, Key

VARIABLES Fluent20_37, Fluent21_37, Fluent76_4, err, Fluent77_4, seqnum_sent, seqnum_recvd, Fluent67_18, transfer_msg, Fluent66_18, cexTraceIdx

vars == <<Fluent20_37, Fluent21_37, Fluent76_4, err, Fluent77_4, seqnum_sent, seqnum_recvd, Fluent67_18, transfer_msg, Fluent66_18, cexTraceIdx>>

NoErr == err = FALSE

CandSep == (\A var0 \in Node : (Fluent77_4[var0] => Fluent76_4[var0]))

Init ==
/\ transfer_msg = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
/\ seqnum_sent = [n \in Node |-> [s \in Seqnum |-> FALSE]]
/\ seqnum_recvd = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ Fluent76_4 = [x0 \in Node |-> FALSE]
/\ Fluent77_4 = [x0 \in Node |-> FALSE]
/\ Fluent20_37 = [x0 \in Seqnum |-> [x1 \in Node |-> FALSE]]
/\ Fluent21_37 = [x0 \in Seqnum |-> [x1 \in Node |-> FALSE]]
/\ Fluent67_18 = [x0 \in Key |-> [x1 \in Seqnum |-> [x2 \in Node |-> FALSE]]]
/\ Fluent66_18 = [x0 \in Key |-> [x1 \in Seqnum |-> [x2 \in Node |-> FALSE]]]
/\ cexTraceIdx = 0
/\ err = FALSE

reshard(n_old,n_new,k,v,s) ==
/\ ~(seqnum_sent[n_old][s])
/\ seqnum_sent' = [seqnum_sent EXCEPT![n_old][s] = TRUE]
/\ transfer_msg' = [transfer_msg EXCEPT![n_old][n_new][k][v][s] = TRUE]
/\ UNCHANGED <<seqnum_recvd>>
/\ Fluent76_4' = [Fluent76_4 EXCEPT![n_old] = TRUE]
/\ UNCHANGED <<Fluent77_4>>
/\ CandSep'
/\ Fluent67_18' = [Fluent67_18 EXCEPT![k][s][n_old] = TRUE]
/\ UNCHANGED <<Fluent20_37,Fluent21_37,Fluent66_18>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

drop_transfer_msg(src,dst,k,v,s) ==
/\ transfer_msg[src][dst][k][v][s]
/\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = FALSE]
/\ UNCHANGED <<seqnum_sent,seqnum_recvd>>
/\ UNCHANGED <<Fluent76_4,Fluent77_4>>
/\ CandSep'
/\ UNCHANGED <<Fluent20_37,Fluent21_37,Fluent67_18,Fluent66_18>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

retransmit(src,dst,k,v,s) ==
/\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = TRUE]
/\ UNCHANGED <<seqnum_sent,seqnum_recvd>>
/\ Fluent77_4' = [Fluent77_4 EXCEPT![src] = TRUE]
/\ UNCHANGED <<Fluent76_4>>
/\ CandSep'
/\ UNCHANGED <<Fluent20_37,Fluent21_37,Fluent67_18,Fluent66_18>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

recv_transfer_msg(src,n,k,v,s) ==
/\ transfer_msg[src][n][k][v][s]
/\ ~(seqnum_recvd[n][src][s])
/\ seqnum_recvd' = [seqnum_recvd EXCEPT![n][src][s] = TRUE]
/\ UNCHANGED <<transfer_msg,seqnum_sent>>
/\ UNCHANGED <<Fluent76_4,Fluent77_4>>
/\ CandSep'
/\ Fluent20_37' = [Fluent20_37 EXCEPT![s][src] = Fluent21_37[s][src]]
/\ Fluent21_37' = [Fluent21_37 EXCEPT![s][src] = TRUE]
/\ Fluent66_18' = [Fluent66_18 EXCEPT![k][s][src] = TRUE]
/\ UNCHANGED <<Fluent67_18>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

send_ack(src,n,k,v,s) ==
/\ transfer_msg[src][n][k][v][s]
/\ seqnum_recvd[n][src][s]
/\ UNCHANGED <<transfer_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED <<Fluent76_4,Fluent77_4>>
/\ CandSep'
/\ UNCHANGED <<Fluent20_37,Fluent21_37,Fluent67_18,Fluent66_18>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

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
/\ (\A var0 \in Key : (\A var1 \in Seqnum : (\A var2 \in Node : (Fluent66_18[var0][var1][var2] => Fluent67_18[var0][var1][var2]))))
/\ (\A var0 \in Node : (\A var1 \in Seqnum : (Fluent20_37[var1][var0] => ~(Fluent21_37[var1][var0]))))

TraceConstraint ==
/\ cexTraceIdx = 0 => reshard(n1,n1,k1,v1,1) /\ err' = err
/\ cexTraceIdx = 1 => recv_transfer_msg(n1,n1,k1,v1,1) /\ err' = err
/\ cexTraceIdx = 2 => reshard(n1,n2,k1,v1,2) /\ err' = err
/\ cexTraceIdx = 3 => reshard(n2,n2,k1,v1,1) /\ err' = err
/\ cexTraceIdx = 4 => retransmit(n1,n2,k1,v1,1) /\ err' = err
/\ cexTraceIdx = 5 => recv_transfer_msg(n1,n2,k1,v1,1) /\ err' = TRUE
/\ cexTraceIdx >= 6 => FALSE

InternalAction == UNCHANGED<<cexTraceIdx,err>>

TraceConstraintSpec == Init /\ [][Next /\ (TraceConstraint \/ InternalAction)]_vars
=============================================================================
