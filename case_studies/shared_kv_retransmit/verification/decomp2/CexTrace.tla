--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS Seqnum, n1, n2, k1, k2, Node, NUM2, Value, v1, v2, Key, NUM1

VARIABLES err, seqnum_sent, ack_msg, seqnum_recvd, cexTraceIdx

vars == <<err, seqnum_sent, ack_msg, seqnum_recvd, cexTraceIdx>>

NoErr == err = FALSE

Init ==
/\ ack_msg = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ seqnum_sent = [n \in Node |-> [s \in Seqnum |-> FALSE]]
/\ seqnum_recvd = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ cexTraceIdx = 0
/\ err = FALSE

reshard(n_old,n_new,k,v,s) ==
/\ ~(seqnum_sent[n_old][s])
/\ seqnum_sent' = [seqnum_sent EXCEPT![n_old][s] = TRUE]
/\ UNCHANGED <<ack_msg,seqnum_recvd>>
/\ cexTraceIdx' = cexTraceIdx + 1

recv_transfer_msg(src,n,k,v,s) ==
/\ ~(seqnum_recvd[n][src][s])
/\ seqnum_recvd' = [seqnum_recvd EXCEPT![n][src][s] = TRUE]
/\ UNCHANGED <<ack_msg,seqnum_sent>>
/\ cexTraceIdx' = cexTraceIdx + 1

send_ack(src,n,k,v,s) ==
/\ seqnum_recvd[n][src][s]
/\ ack_msg' = [ack_msg EXCEPT![src][n][s] = TRUE]
/\ UNCHANGED <<seqnum_sent,seqnum_recvd>>
/\ cexTraceIdx' = cexTraceIdx + 1

drop_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ ack_msg' = [ack_msg EXCEPT![src][dst][s] = FALSE]
/\ UNCHANGED <<seqnum_sent,seqnum_recvd>>
/\ cexTraceIdx' = cexTraceIdx

recv_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ UNCHANGED <<ack_msg,seqnum_sent,seqnum_recvd>>
/\ cexTraceIdx' = cexTraceIdx + 1

Next ==
\E n,m \in Node :
\E k \in Key :
\E v \in Value :
\E s \in Seqnum :
\/ reshard(n,m,k,v,s)
\/ recv_transfer_msg(n,m,k,v,s)
\/ send_ack(n,m,k,v,s)
\/ drop_ack_msg(n,m,s)
\/ recv_ack_msg(n,m,s)

Spec == (Init /\ [][Next]_vars)

TraceConstraint ==
/\ cexTraceIdx = 0 => reshard(n1,n1,k1,v1,1) /\ err' = err
/\ cexTraceIdx = 1 => recv_transfer_msg(n1,n1,k1,v1,1) /\ err' = err
/\ cexTraceIdx = 2 => recv_transfer_msg(n1,n1,k1,v1,1) /\ err' = TRUE
/\ cexTraceIdx >= 3 => FALSE

InternalAction == UNCHANGED<<cexTraceIdx,err>>

TraceConstraintSpec == Init /\ [][Next /\ (TraceConstraint \/ InternalAction)]_vars
=============================================================================
