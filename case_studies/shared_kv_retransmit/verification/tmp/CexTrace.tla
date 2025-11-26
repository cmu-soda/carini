--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS Seqnum, n1, n2, k1, k2, Node, NUM2, k3, NUM1, Value, v1, v2, Key

VARIABLES Fluent24_18, Fluent23_18, Fluent14_42, Fluent13_42, ack_msg, unacked, cexTraceIdx, Fluent55_28, Fluent54_28

vars == <<Fluent24_18, Fluent23_18, Fluent14_42, Fluent13_42, ack_msg, unacked, cexTraceIdx, Fluent55_28, Fluent54_28>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ Fluent24_18 = << ( k1 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k2 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k3 :> (n1 :> FALSE @@ n2 :> FALSE) ),
     ( k1 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k2 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k3 :> (n1 :> FALSE @@ n2 :> FALSE) ) >>
  /\ Fluent23_18 = << ( k1 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k2 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k3 :> (n1 :> FALSE @@ n2 :> FALSE) ),
     ( k1 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k2 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k3 :> (n1 :> FALSE @@ n2 :> FALSE) ) >>
  /\ ack_msg = ( n1 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) @@
    n2 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) )
  /\ Fluent14_42 = <<(n1 :> FALSE @@ n2 :> FALSE), (n1 :> FALSE @@ n2 :> FALSE)>>
  /\ Fluent13_42 = <<(n1 :> FALSE @@ n2 :> FALSE), (n1 :> FALSE @@ n2 :> FALSE)>>
  /\ unacked = ( n1 :>
        ( n1 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k3 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k3 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) @@
    n2 :>
        ( n1 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k3 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k3 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) )
  /\ Fluent55_28 = ( n1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
    n2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) )
  /\ Fluent54_28 = ( n1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
    n2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) )

/\ cexTraceIdx = 1 =>
  /\ Fluent24_18 = << ( k1 :> (n1 :> TRUE @@ n2 :> FALSE) @@
       k2 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k3 :> (n1 :> FALSE @@ n2 :> FALSE) ),
     ( k1 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k2 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k3 :> (n1 :> FALSE @@ n2 :> FALSE) ) >>
  /\ Fluent23_18 = << ( k1 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k2 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k3 :> (n1 :> FALSE @@ n2 :> FALSE) ),
     ( k1 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k2 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k3 :> (n1 :> FALSE @@ n2 :> FALSE) ) >>
  /\ ack_msg = ( n1 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) @@
    n2 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) )
  /\ Fluent14_42 = <<(n1 :> FALSE @@ n2 :> FALSE), (n1 :> FALSE @@ n2 :> FALSE)>>
  /\ Fluent13_42 = <<(n1 :> FALSE @@ n2 :> FALSE), (n1 :> FALSE @@ n2 :> FALSE)>>
  /\ unacked = ( n1 :>
        ( n1 :>
              ( k1 :> (v1 :> <<TRUE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k3 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k3 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) @@
    n2 :>
        ( n1 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k3 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k3 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) )
  /\ Fluent55_28 = ( n1 :> (v1 :> <<TRUE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
    n2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) )
  /\ Fluent54_28 = ( n1 :> (v1 :> <<TRUE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
    n2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) )

/\ cexTraceIdx = 2 =>
  /\ Fluent24_18 = << ( k1 :> (n1 :> TRUE @@ n2 :> FALSE) @@
       k2 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k3 :> (n1 :> FALSE @@ n2 :> FALSE) ),
     ( k1 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k2 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k3 :> (n1 :> FALSE @@ n2 :> FALSE) ) >>
  /\ Fluent23_18 = << ( k1 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k2 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k3 :> (n1 :> FALSE @@ n2 :> FALSE) ),
     ( k1 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k2 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k3 :> (n1 :> FALSE @@ n2 :> FALSE) ) >>
  /\ ack_msg = ( n1 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) @@
    n2 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) )
  /\ Fluent14_42 = <<(n1 :> FALSE @@ n2 :> FALSE), (n1 :> FALSE @@ n2 :> FALSE)>>
  /\ Fluent13_42 = <<(n1 :> FALSE @@ n2 :> FALSE), (n1 :> FALSE @@ n2 :> FALSE)>>
  /\ unacked = ( n1 :>
        ( n1 :>
              ( k1 :> (v1 :> <<TRUE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k3 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k3 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) @@
    n2 :>
        ( n1 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k3 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k3 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) )
  /\ Fluent55_28 = ( n1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
    n2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) )
  /\ Fluent54_28 = ( n1 :> (v1 :> <<TRUE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
    n2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) )

/\ cexTraceIdx = 3 =>
  /\ Fluent24_18 = << ( k1 :> (n1 :> TRUE @@ n2 :> FALSE) @@
       k2 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k3 :> (n1 :> FALSE @@ n2 :> FALSE) ),
     ( k1 :> (n1 :> FALSE @@ n2 :> TRUE) @@
       k2 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k3 :> (n1 :> FALSE @@ n2 :> FALSE) ) >>
  /\ Fluent23_18 = << ( k1 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k2 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k3 :> (n1 :> FALSE @@ n2 :> FALSE) ),
     ( k1 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k2 :> (n1 :> FALSE @@ n2 :> FALSE) @@
       k3 :> (n1 :> FALSE @@ n2 :> FALSE) ) >>
  /\ ack_msg = ( n1 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) @@
    n2 :> (n1 :> <<FALSE, FALSE>> @@ n2 :> <<FALSE, FALSE>>) )
  /\ Fluent14_42 = <<(n1 :> FALSE @@ n2 :> FALSE), (n1 :> FALSE @@ n2 :> FALSE)>>
  /\ Fluent13_42 = <<(n1 :> FALSE @@ n2 :> FALSE), (n1 :> FALSE @@ n2 :> FALSE)>>
  /\ unacked = ( n1 :>
        ( n1 :>
              ( k1 :> (v1 :> <<TRUE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k3 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k3 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) @@
    n2 :>
        ( n1 :>
              ( k1 :> (v1 :> <<FALSE, TRUE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k3 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) @@
          n2 :>
              ( k1 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
                k3 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) ) ) )
  /\ Fluent55_28 = ( n1 :> (v1 :> <<FALSE, TRUE>> @@ v2 :> <<FALSE, FALSE>>) @@
    n2 :> (v1 :> <<FALSE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) )
  /\ Fluent54_28 = ( n1 :> (v1 :> <<TRUE, FALSE>> @@ v2 :> <<FALSE, FALSE>>) @@
    n2 :> (v1 :> <<FALSE, TRUE>> @@ v2 :> <<FALSE, FALSE>>) )


CandSep == (\A var0 \in Value : (\E var1 \in Seqnum : (\A var2 \in Node : (Fluent54_28[var2][var0][var1] => Fluent55_28[var2][var0][var1]))))

Init ==
/\ unacked = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
/\ ack_msg = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ Fluent54_28 = [x0 \in Node |-> [x1 \in Value |-> [x2 \in Seqnum |-> FALSE]]]
/\ Fluent55_28 = [x0 \in Node |-> [x1 \in Value |-> [x2 \in Seqnum |-> FALSE]]]
/\ Fluent23_18 = [x0 \in Seqnum |-> [x1 \in Key |-> [x2 \in Node |-> FALSE]]]
/\ Fluent24_18 = [x0 \in Seqnum |-> [x1 \in Key |-> [x2 \in Node |-> FALSE]]]
/\ Fluent13_42 = [x0 \in Seqnum |-> [x1 \in Node |-> FALSE]]
/\ Fluent14_42 = [x0 \in Seqnum |-> [x1 \in Node |-> FALSE]]
/\ cexTraceIdx = 0
/\ TraceConstraint

reshard(n_old,n_new,k,v,s) ==
/\ unacked' = [unacked EXCEPT![n_old][n_new][k][v][s] = TRUE]
/\ UNCHANGED <<ack_msg>>
/\ Fluent54_28' = [Fluent54_28 EXCEPT![n_old][v][s] = TRUE]
/\ Fluent55_28' = [Fluent55_28 EXCEPT![n_new][v][s] = TRUE]
/\ UNCHANGED <<>>
/\ Fluent24_18' = [Fluent24_18 EXCEPT![s][k][n_old] = TRUE]
/\ UNCHANGED <<Fluent23_18,Fluent13_42,Fluent14_42>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

retransmit(src,dst,k,v,s) ==
/\ unacked[src][dst][k][v][s]
/\ UNCHANGED <<unacked,ack_msg>>
/\ Fluent55_28' = [Fluent55_28 EXCEPT![dst][v][s] = FALSE]
/\ UNCHANGED <<Fluent54_28>>
/\ UNCHANGED <<Fluent23_18,Fluent24_18,Fluent13_42,Fluent14_42>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

send_ack(src,n,k,v,s) ==
/\ ack_msg' = [ack_msg EXCEPT![src][n][s] = TRUE]
/\ UNCHANGED <<unacked>>
/\ UNCHANGED <<Fluent54_28,Fluent55_28>>
/\ UNCHANGED <<Fluent23_18,Fluent24_18,Fluent13_42,Fluent14_42>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

drop_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ ack_msg' = [ack_msg EXCEPT![src][dst][s] = FALSE]
/\ UNCHANGED <<unacked>>
/\ UNCHANGED <<Fluent54_28,Fluent55_28>>
/\ UNCHANGED <<Fluent23_18,Fluent24_18,Fluent13_42,Fluent14_42>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

recv_ack_msg(src,dst,s) ==
/\ ack_msg[src][dst][s]
/\ unacked' = [N1 \in Node |-> [N2 \in Node |-> [K \in Key |-> [V \in Value |-> [S \in Seqnum |-> IF ((N1 = src /\ N2 = dst) /\ S = s) THEN FALSE ELSE unacked[N1][N2][K][V][S]]]]]]
/\ UNCHANGED <<ack_msg>>
/\ UNCHANGED <<Fluent54_28,Fluent55_28>>
/\ UNCHANGED <<Fluent23_18,Fluent24_18,Fluent13_42,Fluent14_42>>
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
