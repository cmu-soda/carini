--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS Seqnum, n1, n2, k1, k2, Node, NUM2, Value, v1, v2, Key, NUM1

VARIABLES owner, Fluent29_41, seqnum_sent, ack_msg, Fluent28_41, seqnum_recvd, unacked, transfer_msg, cexTraceIdx

vars == <<owner, Fluent29_41, seqnum_sent, ack_msg, Fluent28_41, seqnum_recvd, unacked, transfer_msg, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ ack_msg = ( n1 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) @@
    n2 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) )
  /\ owner = (n1 :> (k1 :> TRUE @@ k2 :> FALSE) @@ n2 :> (k1 :> FALSE @@ k2 :> FALSE))
  /\ seqnum_sent = (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>)
  /\ Fluent29_41 = ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
    k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) )
  /\ Fluent28_41 = ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
    k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) )
  /\ unacked = ( n1 :>
        ( n1 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) @@
    n2 :>
        ( n1 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) )
  /\ transfer_msg = ( n1 :>
        ( n1 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) @@
    n2 :>
        ( n1 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) )
  /\ seqnum_recvd = ( n1 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) @@
    n2 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) )

/\ cexTraceIdx = 1 =>
  /\ ack_msg = ( n1 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) @@
    n2 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) )
  /\ owner = (n1 :> (k1 :> TRUE @@ k2 :> FALSE) @@ n2 :> (k1 :> FALSE @@ k2 :> FALSE))
  /\ seqnum_sent = (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>)
  /\ Fluent29_41 = ( k1 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<FALSE, FALSE>>) @@
    k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) )
  /\ Fluent28_41 = ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
    k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) )
  /\ unacked = ( n1 :>
        ( n1 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) @@
    n2 :>
        ( n1 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) )
  /\ transfer_msg = ( n1 :>
        ( n1 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) @@
    n2 :>
        ( n1 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) )
  /\ seqnum_recvd = ( n1 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) @@
    n2 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) )

/\ cexTraceIdx = 2 =>
  /\ ack_msg = ( n1 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) @@
    n2 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) )
  /\ owner = (n1 :> (k1 :> FALSE @@ k2 :> FALSE) @@ n2 :> (k1 :> FALSE @@ k2 :> FALSE))
  /\ seqnum_sent = (n1 :> <<TRUE, FALSE>> @@ n2 :> <<FALSE, FALSE>>)
  /\ Fluent29_41 = ( k1 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<FALSE, FALSE>>) @@
    k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) )
  /\ Fluent28_41 = ( k1 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) @@
    k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) )
  /\ unacked = ( n1 :>
        ( n1 :>
              ( k1 :> (v1 :> <<TRUE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) @@
    n2 :>
        ( n1 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) )
  /\ transfer_msg = ( n1 :>
        ( n1 :>
              ( k1 :> (v1 :> <<TRUE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) @@
    n2 :>
        ( n1 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) )
  /\ seqnum_recvd = ( n1 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) @@
    n2 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) )

/\ cexTraceIdx = 3 =>
  /\ ack_msg = ( n1 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) @@
    n2 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) )
  /\ owner = (n1 :> (k1 :> TRUE @@ k2 :> FALSE) @@ n2 :> (k1 :> FALSE @@ k2 :> FALSE))
  /\ seqnum_sent = (n1 :> <<TRUE, FALSE>> @@ n2 :> <<FALSE, FALSE>>)
  /\ Fluent29_41 = ( k1 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) @@
    k2 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) )
  /\ Fluent28_41 = ( k1 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) @@
    k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) )
  /\ unacked = ( n1 :>
        ( n1 :>
              ( k1 :> (v1 :> <<TRUE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) @@
    n2 :>
        ( n1 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) )
  /\ transfer_msg = ( n1 :>
        ( n1 :>
              ( k1 :> (v1 :> <<TRUE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) @@
    n2 :>
        ( n1 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) )
  /\ seqnum_recvd = ( n1 :> (n1 :> <<TRUE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) @@
    n2 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) )

/\ cexTraceIdx = 4 =>
  /\ ack_msg = ( n1 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) @@
    n2 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) )
  /\ owner = (n1 :> (k1 :> TRUE @@ k2 :> FALSE) @@ n2 :> (k1 :> FALSE @@ k2 :> FALSE))
  /\ seqnum_sent = (n1 :> <<TRUE, FALSE>> @@ n2 :> <<FALSE, FALSE>>)
  /\ Fluent29_41 = ( k1 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) @@
    k2 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) )
  /\ Fluent28_41 = ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
    k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) )
  /\ unacked = ( n1 :>
        ( n1 :>
              ( k1 :> (v1 :> <<TRUE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) @@
    n2 :>
        ( n1 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) )
  /\ transfer_msg = ( n1 :>
        ( n1 :>
              ( k1 :> (v1 :> <<TRUE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) @@
    n2 :>
        ( n1 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) )
  /\ seqnum_recvd = ( n1 :> (n1 :> <<TRUE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) @@
    n2 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) )


CandSep == (\A var0 \in Seqnum : (\E var1 \in Value : (\E var2 \in Key : (Fluent29_41[var2][var1][var0] => Fluent28_41[var2][var1][var0]))))

Init ==
/\ transfer_msg = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
/\ (owner \in [Node -> [Key -> BOOLEAN]])
/\ (\A N1,N2 \in Node : (\A K \in Key : ((owner[N1][K] /\ owner[N2][K]) => N1 = N2)))
/\ unacked = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
/\ ack_msg = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ seqnum_sent = [n \in Node |-> [s \in Seqnum |-> FALSE]]
/\ seqnum_recvd = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ Fluent29_41 = [x0 \in Key |-> [x1 \in Value |-> [x2 \in Seqnum |-> FALSE]]]
/\ Fluent28_41 = [x0 \in Key |-> [x1 \in Value |-> [x2 \in Seqnum |-> FALSE]]]
/\ cexTraceIdx = 0
/\ TraceConstraint

reshard(n_old,n_new,k,v,s) ==
/\ ~(seqnum_sent[n_old][s])
/\ seqnum_sent' = [seqnum_sent EXCEPT![n_old][s] = TRUE]
/\ owner' = [owner EXCEPT![n_old][k] = FALSE]
/\ transfer_msg' = [transfer_msg EXCEPT![n_old][n_new][k][v][s] = TRUE]
/\ unacked' = [unacked EXCEPT![n_old][n_new][k][v][s] = TRUE]
/\ UNCHANGED <<ack_msg,seqnum_recvd>>
/\ Fluent28_41' = [Fluent28_41 EXCEPT![k] = [x0 \in Value |-> [x1 \in Seqnum |-> Fluent29_41[k][v][s]]]]
/\ UNCHANGED <<Fluent29_41>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

drop_transfer_msg(src,dst,k,v,s) ==
/\ transfer_msg[src][dst][k][v][s]
/\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = FALSE]
/\ UNCHANGED <<unacked,owner,ack_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED <<Fluent29_41,Fluent28_41>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

retransmit(src,dst,k,v,s) ==
/\ unacked[src][dst][k][v][s]
/\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = TRUE]
/\ UNCHANGED <<unacked,owner,ack_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED <<Fluent29_41,Fluent28_41>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

recv_transfer_msg(src,n,k,v,s) ==
/\ transfer_msg[src][n][k][v][s]
/\ ~(seqnum_recvd[n][src][s])
/\ seqnum_recvd' = [seqnum_recvd EXCEPT![n][src][s] = TRUE]
/\ owner' = [owner EXCEPT![n][k] = TRUE]
/\ UNCHANGED <<unacked,transfer_msg,ack_msg,seqnum_sent>>
/\ Fluent29_41' = [x0 \in Key |-> [x1 \in Value |-> [x2 \in Seqnum |-> Fluent28_41[k][v][s]]]]
/\ UNCHANGED <<Fluent28_41>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

send_ack(src,n,k,v,s) ==
/\ transfer_msg[src][n][k][v][s]
/\ seqnum_recvd[n][src][s]
/\ ack_msg' = [ack_msg EXCEPT![src][n][s] = TRUE]
/\ UNCHANGED <<unacked,owner,transfer_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED <<Fluent29_41,Fluent28_41>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

drop_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ ack_msg' = [ack_msg EXCEPT![src][dst][s] = FALSE]
/\ UNCHANGED <<unacked,owner,transfer_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED <<Fluent29_41,Fluent28_41>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

recv_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ unacked' = [N1 \in Node |-> [N2 \in Node |-> [K \in Key |-> [V \in Value |-> [S \in Seqnum |-> IF ((N1 = src /\ N2 = dst) /\ S = s) THEN FALSE ELSE unacked[N1][N2][K][V][S]]]]]]
/\ UNCHANGED <<owner,transfer_msg,ack_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED <<Fluent29_41,Fluent28_41>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

put(n,k,v) ==
/\ owner[n][k]
/\ UNCHANGED <<unacked,owner,transfer_msg,ack_msg,seqnum_sent,seqnum_recvd>>
/\ Fluent29_41' = [Fluent29_41 EXCEPT![k][v] = [x0 \in Seqnum |-> TRUE]]
/\ Fluent28_41' = [Fluent28_41 EXCEPT![k] = [x0 \in Value |-> [x1 \in Seqnum |-> FALSE]]]
/\ UNCHANGED <<>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

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
\/ put(n,k,v)

Spec == (Init /\ [][Next]_vars)
=============================================================================
