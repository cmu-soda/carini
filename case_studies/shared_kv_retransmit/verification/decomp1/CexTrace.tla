--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS Seqnum, n1, n2, k1, k2, Node, NUM2, Value, v1, v2, Key, NUM1

VARIABLES owner, Fluent4_15, Fluent1_59, transfer_msg, Fluent3_15, table, cexTraceIdx, Fluent2_59

vars == <<owner, Fluent4_15, Fluent1_59, transfer_msg, Fluent3_15, table, cexTraceIdx, Fluent2_59>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ Fluent2_59 = (n1 :> FALSE @@ n2 :> FALSE)
  /\ Fluent1_59 = (n1 :> FALSE @@ n2 :> FALSE)
  /\ owner = (n1 :> (k1 :> TRUE @@ k2 :> FALSE) @@ n2 :> (k1 :> FALSE @@ k2 :> TRUE))
  /\ Fluent4_15 = (v1 :> FALSE @@ v2 :> FALSE)
  /\ Fluent3_15 = (v1 :> FALSE @@ v2 :> FALSE)
  /\ table = ( n1 :>
        ( k1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          k2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n2 :>
        ( k1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          k2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
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

/\ cexTraceIdx = 1 =>
  /\ Fluent2_59 = (n1 :> FALSE @@ n2 :> FALSE)
  /\ Fluent1_59 = (n1 :> FALSE @@ n2 :> FALSE)
  /\ owner = (n1 :> (k1 :> TRUE @@ k2 :> FALSE) @@ n2 :> (k1 :> FALSE @@ k2 :> TRUE))
  /\ Fluent4_15 = (v1 :> FALSE @@ v2 :> FALSE)
  /\ Fluent3_15 = (v1 :> FALSE @@ v2 :> FALSE)
  /\ table = ( n1 :>
        ( k1 :> (v1 :> TRUE @@ v2 :> FALSE) @@
          k2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n2 :>
        ( k1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          k2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
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

/\ cexTraceIdx = 2 =>
  /\ Fluent2_59 = (n1 :> FALSE @@ n2 :> FALSE)
  /\ Fluent1_59 = (n1 :> TRUE @@ n2 :> FALSE)
  /\ owner = (n1 :> (k1 :> FALSE @@ k2 :> FALSE) @@ n2 :> (k1 :> FALSE @@ k2 :> TRUE))
  /\ Fluent4_15 = (v1 :> TRUE @@ v2 :> FALSE)
  /\ Fluent3_15 = (v1 :> FALSE @@ v2 :> FALSE)
  /\ table = ( n1 :>
        ( k1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          k2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n2 :>
        ( k1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          k2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
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

/\ cexTraceIdx = 3 =>
  /\ Fluent2_59 = (n1 :> FALSE @@ n2 :> FALSE)
  /\ Fluent1_59 = (n1 :> TRUE @@ n2 :> FALSE)
  /\ owner = (n1 :> (k1 :> TRUE @@ k2 :> FALSE) @@ n2 :> (k1 :> FALSE @@ k2 :> TRUE))
  /\ Fluent4_15 = (v1 :> TRUE @@ v2 :> FALSE)
  /\ Fluent3_15 = (v1 :> FALSE @@ v2 :> FALSE)
  /\ table = ( n1 :>
        ( k1 :> (v1 :> TRUE @@ v2 :> FALSE) @@
          k2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n2 :>
        ( k1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          k2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
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

/\ cexTraceIdx = 4 =>
  /\ Fluent2_59 = (n1 :> FALSE @@ n2 :> FALSE)
  /\ Fluent1_59 = (n1 :> TRUE @@ n2 :> FALSE)
  /\ owner = (n1 :> (k1 :> TRUE @@ k2 :> FALSE) @@ n2 :> (k1 :> FALSE @@ k2 :> TRUE))
  /\ Fluent4_15 = (v1 :> TRUE @@ v2 :> FALSE)
  /\ Fluent3_15 = (v1 :> FALSE @@ v2 :> FALSE)
  /\ table = ( n1 :>
        ( k1 :> (v1 :> FALSE @@ v2 :> TRUE) @@
          k2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n2 :>
        ( k1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          k2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
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

/\ cexTraceIdx = 5 =>
  /\ Fluent2_59 = (n1 :> FALSE @@ n2 :> FALSE)
  /\ Fluent1_59 = (n1 :> TRUE @@ n2 :> FALSE)
  /\ owner = (n1 :> (k1 :> TRUE @@ k2 :> FALSE) @@ n2 :> (k1 :> FALSE @@ k2 :> TRUE))
  /\ Fluent4_15 = (v1 :> TRUE @@ v2 :> FALSE)
  /\ Fluent3_15 = (v1 :> FALSE @@ v2 :> FALSE)
  /\ table = ( n1 :>
        ( k1 :> (v1 :> TRUE @@ v2 :> TRUE) @@
          k2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n2 :>
        ( k1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          k2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
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


CandSep ==
/\ (\A var0 \in Node : (Fluent2_59[var0] => Fluent1_59[var0]))
/\ (\A var0 \in Value : (Fluent3_15[var0] => Fluent4_15[var0]))

Init ==
/\ table = [n \in Node |-> [k \in Key |-> [v \in Value |-> FALSE]]]
/\ transfer_msg = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
/\ (owner \in [Node -> [Key -> BOOLEAN]])
/\ (\A N1,N2 \in Node : (\A K \in Key : ((owner[N1][K] /\ owner[N2][K]) => N1 = N2)))
/\ Fluent4_15 = [x0 \in Value |-> FALSE]
/\ Fluent1_59 = [x0 \in Node |-> FALSE]
/\ Fluent3_15 = [x0 \in Value |-> FALSE]
/\ Fluent2_59 = [x0 \in Node |-> FALSE]
/\ cexTraceIdx = 0
/\ TraceConstraint

reshard(n_old,n_new,k,v,s) ==
/\ table[n_old][k][v]
/\ table' = [table EXCEPT![n_old][k][v] = FALSE]
/\ owner' = [owner EXCEPT![n_old][k] = FALSE]
/\ transfer_msg' = [transfer_msg EXCEPT![n_old][n_new][k][v][s] = TRUE]
/\ Fluent4_15' = [Fluent4_15 EXCEPT![v] = TRUE]
/\ Fluent1_59' = [Fluent1_59 EXCEPT![n_old] = TRUE]
/\ UNCHANGED <<Fluent3_15,Fluent2_59>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

drop_transfer_msg(src,dst,k,v,s) ==
/\ transfer_msg[src][dst][k][v][s]
/\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = FALSE]
/\ UNCHANGED <<table,owner>>
/\ UNCHANGED <<Fluent4_15,Fluent1_59,Fluent3_15,Fluent2_59>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

retransmit(src,dst,k,v,s) ==
/\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = TRUE]
/\ UNCHANGED <<table,owner>>
/\ Fluent3_15' = [Fluent3_15 EXCEPT![v] = TRUE]
/\ Fluent2_59' = [Fluent2_59 EXCEPT![src] = TRUE]
/\ UNCHANGED <<Fluent4_15,Fluent1_59>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

recv_transfer_msg(src,n,k,v,s) ==
/\ transfer_msg[src][n][k][v][s]
/\ table' = [table EXCEPT![n][k][v] = TRUE]
/\ owner' = [owner EXCEPT![n][k] = TRUE]
/\ UNCHANGED <<transfer_msg>>
/\ UNCHANGED <<Fluent4_15,Fluent1_59,Fluent3_15,Fluent2_59>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

send_ack(src,n,k,v,s) ==
/\ transfer_msg[src][n][k][v][s]
/\ UNCHANGED <<table,owner,transfer_msg>>
/\ UNCHANGED <<Fluent4_15,Fluent1_59,Fluent3_15,Fluent2_59>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

put(n,k,v) ==
/\ owner[n][k]
/\ table' = [table EXCEPT![n][k] = [V \in Value |-> V = v]]
/\ UNCHANGED <<owner,transfer_msg>>
/\ UNCHANGED <<Fluent4_15,Fluent1_59,Fluent3_15,Fluent2_59>>
/\ CandSep'
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
\/ put(n,k,v)

Spec == (Init /\ [][Next]_vars)

Safety == (\A N1,N2 \in Node : (\A K \in Key : (\A V1,V2 \in Value : ((table[N1][K][V1] /\ table[N2][K][V2]) => (N1 = N2 /\ V1 = V2)))))
=============================================================================
