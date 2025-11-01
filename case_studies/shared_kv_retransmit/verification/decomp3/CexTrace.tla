--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS Seqnum, n1, n2, k1, k2, Node, NUM2, Value, v1, v2, Key, NUM1

VARIABLES rectr2, rectr1, ack_msg, unacked, cexTraceIdx

vars == <<rectr2, rectr1, ack_msg, unacked, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ rectr1 = ( n1 :>
        ( n1 :>
              ( k1 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) @@
                k2 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) @@
                k2 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) ) ) @@
    n2 :>
        ( n1 :>
              ( k1 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) @@
                k2 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) @@
                k2 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) ) ) )
  /\ rectr2 = ( n1 :>
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
  /\ ack_msg = ( n1 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) @@
    n2 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) )
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

/\ cexTraceIdx = 1 =>
  /\ rectr1 = ( n1 :>
        ( n1 :>
              ( k1 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) @@
                k2 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) @@
                k2 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) ) ) @@
    n2 :>
        ( n1 :>
              ( k1 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) @@
                k2 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) @@
                k2 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) ) ) )
  /\ rectr2 = ( n1 :>
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
  /\ ack_msg = ( n1 :> (n1 :> <<TRUE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) @@
    n2 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) )
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

/\ cexTraceIdx = 2 =>
  /\ rectr1 = ( n1 :>
        ( n1 :>
              ( k1 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) @@
                k2 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) @@
                k2 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) ) ) @@
    n2 :>
        ( n1 :>
              ( k1 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) @@
                k2 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) @@
                k2 :> (v1 :> <<TRUE, TRUE>> @@ v2 :> <<TRUE, TRUE>>) ) ) )
  /\ rectr2 = ( n1 :>
        ( n1 :>
              ( k1 :> (v1 :> <<TRUE, FALSE>> @@ v2 :> <<TRUE, FALSE>>) @@
                k2 :> (v1 :> <<TRUE, FALSE>> @@ v2 :> <<TRUE, FALSE>>) ) @@
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
  /\ ack_msg = ( n1 :> (n1 :> <<TRUE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) @@
    n2 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) )
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


CandSep ==
/\ (\A n \in Node : (\A m \in Node : (\A k \in Key : (\A v \in Value : (\A s \in Seqnum : ~(rectr2[n][m][k][v][s]))))))

Init ==
/\ unacked = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
/\ ack_msg = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ rectr1 = [n \in Node |-> [m \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> TRUE]]]]]
/\ rectr2 = [n \in Node |-> [m \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
/\ cexTraceIdx = 0
/\ TraceConstraint

reshard(n_old,n_new,k,v,s) ==
/\ unacked' = [unacked EXCEPT![n_old][n_new][k][v][s] = TRUE]
/\ UNCHANGED <<ack_msg>>
/\ rectr1' = [rectr1 EXCEPT![n_old][n_new][k][v][s] = FALSE]
/\ rectr2' = [rectr2 EXCEPT![n_old][n_new][k][v][s] = FALSE]
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

retransmit(src,dst,k,v,s) ==
/\ unacked[src][dst][k][v][s]
/\ UNCHANGED <<unacked,ack_msg>>
/\ UNCHANGED <<rectr1,rectr2>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

send_ack(src,n,k,v,s) ==
/\ ack_msg' = [ack_msg EXCEPT![src][n][s] = TRUE]
/\ UNCHANGED <<unacked>>
/\ UNCHANGED <<rectr1,rectr2>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

drop_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ ack_msg' = [ack_msg EXCEPT![src][dst][s] = FALSE]
/\ UNCHANGED <<unacked>>
/\ UNCHANGED <<rectr1,rectr2>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

recv_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ unacked' = [N1 \in Node |-> [N2 \in Node |-> [K \in Key |-> [V \in Value |-> [S \in Seqnum |-> IF ((N1 = src /\ N2 = dst) /\ S = s) THEN FALSE ELSE unacked[N1][N2][K][V][S]]]]]]
/\ UNCHANGED <<ack_msg>>
/\ rectr1' = [N1 \in Node |-> [N2 \in Node |-> [K \in Key |-> [V \in Value |-> [S \in Seqnum |-> IF ((N1 = src /\ N2 = dst) /\ S = s) THEN TRUE ELSE rectr1[N1][N2][K][V][S]]]]]]
/\ rectr2' = [N1 \in Node |-> [N2 \in Node |-> [K \in Key |-> [V \in Value |-> [S \in Seqnum |-> IF ((N1 = src /\ N2 = dst) /\ S = s) THEN rectr1[N1][N2][K][V][S] ELSE rectr2[N1][N2][K][V][S]]]]]]
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

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
