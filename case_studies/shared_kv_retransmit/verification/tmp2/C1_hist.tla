--------------------------- MODULE C1_hist ---------------------------
EXTENDS Naturals

CONSTANTS Key, Node, Value, Seqnum

VARIABLES owner, Fluent20_37, Fluent21_37, Fluent67_18, table, Fluent66_18

vars == <<owner, Fluent20_37, Fluent21_37, Fluent67_18, table, Fluent66_18>>

CandSep ==
/\ \A var0 \in Key : \A var1 \in Seqnum : \A var2 \in Node : (Fluent66_18[var0][var1][var2]) => (Fluent67_18[var0][var1][var2])
/\ \A var0 \in Node : \A var1 \in Seqnum : (Fluent20_37[var1][var0]) => (~(Fluent21_37[var1][var0]))

Init ==
/\ table = [n \in Node |-> [k \in Key |-> [v \in Value |-> FALSE]]]
/\ (owner \in [Node -> [Key -> BOOLEAN]])
/\ (\A N1,N2 \in Node : (\A K \in Key : ((owner[N1][K] /\ owner[N2][K]) => N1 = N2)))
/\ Fluent20_37 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]
/\ Fluent21_37 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]
/\ Fluent67_18 = [ x0 \in Key |-> [ x1 \in Seqnum |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent66_18 = [ x0 \in Key |-> [ x1 \in Seqnum |-> [ x2 \in Node |-> FALSE]]]

reshard(n_old,n_new,k,v,s) ==
/\ table[n_old][k][v]
/\ table' = [table EXCEPT![n_old][k][v] = FALSE]
/\ owner' = [owner EXCEPT![n_old][k] = FALSE]
/\ Fluent67_18' = [Fluent67_18 EXCEPT ![k][s][n_old] = TRUE]
/\ UNCHANGED<<Fluent20_37, Fluent21_37, Fluent66_18>>
/\ CandSep'

recv_transfer_msg(src,n,k,v,s) ==
/\ table' = [table EXCEPT![n][k][v] = TRUE]
/\ owner' = [owner EXCEPT![n][k] = TRUE]
/\ Fluent20_37' = [Fluent20_37 EXCEPT ![s][src] = Fluent21_37[s][src]]
/\ Fluent21_37' = [Fluent21_37 EXCEPT ![s][src] = TRUE]
/\ Fluent66_18' = [Fluent66_18 EXCEPT ![k][s][src] = TRUE]
/\ UNCHANGED<<Fluent67_18>>
/\ CandSep'

put(n,k,v) ==
/\ owner[n][k]
/\ table' = [table EXCEPT![n][k] = [V \in Value |-> V = v]]
/\ UNCHANGED <<owner>>
/\ UNCHANGED<<Fluent20_37, Fluent21_37, Fluent67_18, Fluent66_18>>
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
