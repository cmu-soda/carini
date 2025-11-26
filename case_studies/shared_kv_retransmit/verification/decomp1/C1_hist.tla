--------------------------- MODULE C1_hist ---------------------------


CONSTANTS Key, Node, Value, Seqnum

VARIABLES Fluent4_55, Fluent5_55, table

vars == <<Fluent4_55, Fluent5_55, table>>

CandSep ==
\A var0 \in Seqnum : (Fluent4_55[var0]) => (Fluent5_55[var0])

Init ==
/\ table = [n \in Node |-> [k \in Key |-> [v \in Value |-> FALSE]]]
/\ Fluent4_55 = [ x0 \in Seqnum |-> FALSE]
/\ Fluent5_55 = [ x0 \in Seqnum |-> FALSE]

reshard(n_old,n_new,k,v,s) ==
/\ table[n_old][k][v]
/\ table' = [table EXCEPT![n_old][k][v] = FALSE]
/\ Fluent5_55' = [Fluent5_55 EXCEPT ![s] = TRUE]
/\ UNCHANGED<<Fluent4_55>>
/\ CandSep'

recv_transfer_msg(src,n,k,v,s) ==
/\ table' = [table EXCEPT![n][k][v] = TRUE]
/\ Fluent4_55' = [Fluent4_55 EXCEPT ![s] = TRUE]
/\ UNCHANGED<<Fluent5_55>>
/\ CandSep'

put(n,k,v) ==
/\ table' = [table EXCEPT![n][k] = [V \in Value |-> V = v]]
/\ UNCHANGED<<Fluent4_55, Fluent5_55>>
/\ CandSep'

Next ==
\E n,m \in Node :
\E k \in Key :
\E v \in Value :
\E s \in Seqnum :
\/ reshard(n,m,k,v,s)
\/ recv_transfer_msg(n,m,k,v,s)
\/ put(n,k,v)

Spec == (Init /\ [][Next]_vars)

Safety == (\A N1,N2 \in Node : (\A K \in Key : (\A V1,V2 \in Value : ((table[N1][K][V1] /\ table[N2][K][V2]) => (N1 = N2 /\ V1 = V2)))))
=============================================================================
