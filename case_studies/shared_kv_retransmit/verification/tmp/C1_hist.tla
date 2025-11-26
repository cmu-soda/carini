--------------------------- MODULE C1_hist ---------------------------
EXTENDS Naturals

CONSTANTS Key, Node, Value, Seqnum

VARIABLES owner, Fluent23_18, Fluent24_18, Fluent13_42, Fluent14_42, table

vars == <<owner, Fluent23_18, Fluent24_18, Fluent13_42, Fluent14_42, table>>

CandSep ==
/\ \A var0 \in Key : \A var1 \in Seqnum : \A var2 \in Node : (Fluent23_18[var1][var0][var2]) => (Fluent24_18[var1][var0][var2])
/\ \A var0 \in Seqnum : \A var1 \in Node : (Fluent13_42[var0][var1]) => (~(Fluent14_42[var0][var1]))

Init ==
/\ table = [n \in Node |-> [k \in Key |-> [v \in Value |-> FALSE]]]
/\ (owner \in [Node -> [Key -> BOOLEAN]])
/\ (\A N1,N2 \in Node : (\A K \in Key : ((owner[N1][K] /\ owner[N2][K]) => N1 = N2)))
/\ Fluent23_18 = [ x0 \in Seqnum |-> [ x1 \in Key |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent24_18 = [ x0 \in Seqnum |-> [ x1 \in Key |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent13_42 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]
/\ Fluent14_42 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]

reshard(n_old,n_new,k,v,s) ==
/\ table[n_old][k][v]
/\ table' = [table EXCEPT![n_old][k][v] = FALSE]
/\ owner' = [owner EXCEPT![n_old][k] = FALSE]
/\ Fluent24_18' = [Fluent24_18 EXCEPT ![s][k][n_old] = TRUE]
/\ UNCHANGED<<Fluent23_18, Fluent13_42, Fluent14_42>>
/\ CandSep'

recv_transfer_msg(src,n,k,v,s) ==
/\ table' = [table EXCEPT![n][k][v] = TRUE]
/\ owner' = [owner EXCEPT![n][k] = TRUE]
/\ Fluent23_18' = [Fluent23_18 EXCEPT ![s][k][src] = TRUE]
/\ Fluent13_42' = [Fluent13_42 EXCEPT ![s][src] = Fluent14_42[s][src]]
/\ Fluent14_42' = [Fluent14_42 EXCEPT ![s][src] = TRUE]
/\ UNCHANGED<<Fluent24_18>>
/\ CandSep'

put(n,k,v) ==
/\ owner[n][k]
/\ table' = [table EXCEPT![n][k] = [V \in Value |-> V = v]]
/\ UNCHANGED <<owner>>
/\ UNCHANGED<<Fluent23_18, Fluent24_18, Fluent13_42, Fluent14_42>>
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
