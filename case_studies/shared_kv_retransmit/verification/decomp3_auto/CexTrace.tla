--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS Seqnum, n1, n2, k1, k2, Node, NUM2, k3, NUM1, Value, v1, v2, Key

VARIABLES Fluent52_20, Fluent51_20, Fluent84_27, Fluent20_38, err, seqnum_sent, Fluent85_27, seqnum_recvd, transfer_msg, cexTraceIdx, Fluent19_38

vars == <<Fluent52_20, Fluent51_20, Fluent84_27, Fluent20_38, err, seqnum_sent, Fluent85_27, seqnum_recvd, transfer_msg, cexTraceIdx, Fluent19_38>>

NoErr == err = FALSE

CandSep == (\A var0 \in Value : (\A var1 \in Node : (\A var2 \in Node : (Fluent84_27[var1][var0][var2] => Fluent85_27[var1][var0][var2]))))

Init ==
/\ transfer_msg = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
/\ seqnum_sent = [n \in Node |-> [s \in Seqnum |-> FALSE]]
/\ seqnum_recvd = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ Fluent84_27 = [x0 \in Node |-> [x1 \in Value |-> [x2 \in Node |-> FALSE]]]
/\ Fluent85_27 = [x0 \in Node |-> [x1 \in Value |-> [x2 \in Node |-> FALSE]]]
/\ Fluent52_20 = [x0 \in Seqnum |-> [x1 \in Node |-> [x2 \in Key |-> FALSE]]]
/\ Fluent51_20 = [x0 \in Seqnum |-> [x1 \in Node |-> [x2 \in Key |-> FALSE]]]
/\ Fluent20_38 = [x0 \in Seqnum |-> [x1 \in Node |-> FALSE]]
/\ Fluent19_38 = [x0 \in Seqnum |-> [x1 \in Node |-> FALSE]]
/\ cexTraceIdx = 0
/\ err = FALSE

reshard(n_old,n_new,k,v,s) ==
/\ ~(seqnum_sent[n_old][s])
/\ seqnum_sent' = [seqnum_sent EXCEPT![n_old][s] = TRUE]
/\ transfer_msg' = [transfer_msg EXCEPT![n_old][n_new][k][v][s] = TRUE]
/\ UNCHANGED <<seqnum_recvd>>
/\ Fluent85_27' = [Fluent85_27 EXCEPT![n_old][v][n_new] = TRUE]
/\ UNCHANGED <<Fluent84_27>>
/\ CandSep'
/\ Fluent52_20' = [Fluent52_20 EXCEPT![s][n_old][k] = TRUE]
/\ UNCHANGED <<Fluent51_20,Fluent20_38,Fluent19_38>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

drop_transfer_msg(src,dst,k,v,s) ==
/\ transfer_msg[src][dst][k][v][s]
/\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = FALSE]
/\ UNCHANGED <<seqnum_sent,seqnum_recvd>>
/\ UNCHANGED <<Fluent84_27,Fluent85_27>>
/\ CandSep'
/\ UNCHANGED <<Fluent52_20,Fluent51_20,Fluent20_38,Fluent19_38>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

retransmit(src,dst,k,v,s) ==
/\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = TRUE]
/\ UNCHANGED <<seqnum_sent,seqnum_recvd>>
/\ Fluent84_27' = [Fluent84_27 EXCEPT![src][v][dst] = TRUE]
/\ UNCHANGED <<Fluent85_27>>
/\ CandSep'
/\ UNCHANGED <<Fluent52_20,Fluent51_20,Fluent20_38,Fluent19_38>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

recv_transfer_msg(src,n,k,v,s) ==
/\ transfer_msg[src][n][k][v][s]
/\ ~(seqnum_recvd[n][src][s])
/\ seqnum_recvd' = [seqnum_recvd EXCEPT![n][src][s] = TRUE]
/\ UNCHANGED <<transfer_msg,seqnum_sent>>
/\ UNCHANGED <<Fluent84_27,Fluent85_27>>
/\ CandSep'
/\ Fluent51_20' = [Fluent51_20 EXCEPT![s][src][k] = TRUE]
/\ Fluent20_38' = [Fluent20_38 EXCEPT![s][src] = TRUE]
/\ Fluent19_38' = [Fluent19_38 EXCEPT![s][src] = Fluent20_38[s][src]]
/\ UNCHANGED <<Fluent52_20>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

send_ack(src,n,k,v,s) ==
/\ transfer_msg[src][n][k][v][s]
/\ seqnum_recvd[n][src][s]
/\ UNCHANGED <<transfer_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED <<Fluent84_27,Fluent85_27>>
/\ CandSep'
/\ UNCHANGED <<Fluent52_20,Fluent51_20,Fluent20_38,Fluent19_38>>
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
/\ (\A var0 \in Seqnum : (\A var1 \in Node : (Fluent20_38[var0][var1] => ~(Fluent19_38[var0][var1]))))
/\ (\A var0 \in Seqnum : (\A var1 \in Key : (\A var2 \in Node : (Fluent51_20[var0][var2][var1] => Fluent52_20[var0][var2][var1]))))

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
