--------------------------- MODULE C1_hist ---------------------------
EXTENDS Naturals

CONSTANTS Key, Node, Value, Seqnum

VARIABLES owner, Fluent52_20, Fluent51_20, Fluent20_38, table, Fluent19_38

vars == <<owner, Fluent52_20, Fluent51_20, Fluent20_38, table, Fluent19_38>>

CandSep ==
/\ \A var0 \in Seqnum : \A var1 \in Node : (Fluent20_38[var0][var1]) => (~(Fluent19_38[var0][var1]))
/\ \A var0 \in Seqnum : \A var1 \in Key : \A var2 \in Node : (Fluent51_20[var0][var2][var1]) => (Fluent52_20[var0][var2][var1])

Init ==
/\ table = [n \in Node |-> [k \in Key |-> [v \in Value |-> FALSE]]]
/\ (owner \in [Node -> [Key -> BOOLEAN]])
/\ (\A N1,N2 \in Node : (\A K \in Key : ((owner[N1][K] /\ owner[N2][K]) => N1 = N2)))
/\ Fluent52_20 = [ x0 \in Seqnum |-> [ x1 \in Node |-> [ x2 \in Key |-> FALSE]]]
/\ Fluent51_20 = [ x0 \in Seqnum |-> [ x1 \in Node |-> [ x2 \in Key |-> FALSE]]]
/\ Fluent20_38 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]
/\ Fluent19_38 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]

reshard(n_old,n_new,k,v,s) ==
/\ table[n_old][k][v]
/\ table' = [table EXCEPT![n_old][k][v] = FALSE]
/\ owner' = [owner EXCEPT![n_old][k] = FALSE]
/\ Fluent52_20' = [Fluent52_20 EXCEPT ![s][n_old][k] = TRUE]
/\ UNCHANGED<<Fluent51_20, Fluent20_38, Fluent19_38>>
/\ CandSep'

recv_transfer_msg(src,n,k,v,s) ==
/\ table' = [table EXCEPT![n][k][v] = TRUE]
/\ owner' = [owner EXCEPT![n][k] = TRUE]
/\ Fluent51_20' = [Fluent51_20 EXCEPT ![s][src][k] = TRUE]
/\ Fluent20_38' = [Fluent20_38 EXCEPT ![s][src] = TRUE]
/\ Fluent19_38' = [Fluent19_38 EXCEPT ![s][src] = Fluent20_38[s][src]]
/\ UNCHANGED<<Fluent52_20>>
/\ CandSep'

put(n,k,v) ==
/\ owner[n][k]
/\ table' = [table EXCEPT![n][k] = [V \in Value |-> V = v]]
/\ UNCHANGED <<owner>>
/\ UNCHANGED<<Fluent52_20, Fluent51_20, Fluent20_38, Fluent19_38>>
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
