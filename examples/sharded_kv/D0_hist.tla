--------------------------- MODULE D0_hist ---------------------------


CONSTANTS Key, Value, Node

VARIABLES owner, Fluent9_12, Fluent25_14, table, Fluent10_12, Fluent24_14

vars == <<owner, Fluent9_12, Fluent25_14, table, Fluent10_12, Fluent24_14>>

CandSep ==
/\ \A var0 \in Value : \A var1 \in Node : \A var2 \in Key : (Fluent24_14[var1][var0][var2]) => (Fluent25_14[var1][var0][var2])
/\ \A var0 \in Value : \A var1 \in Key : \A var2 \in Node : (Fluent10_12[var1][var0][var2]) => (~(Fluent9_12[var1][var0][var2]))

Nil == "nil"

Reshard(k,v,n_old,n_new) ==
/\ table[n_old][k] = v
/\ table' = [table EXCEPT![n_old][k] = Nil]
/\ owner' = [owner EXCEPT![n_old] = (owner[n_old] \ {k})]
/\ Fluent25_14' = [Fluent25_14 EXCEPT ![n_new][v][k] = TRUE]
/\ Fluent10_12' = [Fluent10_12 EXCEPT ![k][v][n_new] = FALSE]
/\ UNCHANGED<<Fluent9_12, Fluent24_14>>
/\ CandSep'

RecvTransferMsg(n,k,v) ==
/\ table' = [table EXCEPT![n][k] = v]
/\ owner' = [owner EXCEPT![n] = (owner[n] \cup {k})]
/\ Fluent9_12' = [Fluent9_12 EXCEPT ![k][v][n] = Fluent10_12[k][v][n]]
/\ Fluent10_12' = [Fluent10_12 EXCEPT ![k][v][n] = TRUE]
/\ Fluent24_14' = [Fluent24_14 EXCEPT ![n][v][k] = TRUE]
/\ UNCHANGED<<Fluent25_14>>
/\ CandSep'

Put(n,k,v) ==
/\ (k \in owner[n])
/\ table' = [table EXCEPT![n][k] = v]
/\ UNCHANGED <<owner>>
/\ UNCHANGED<<Fluent25_14, Fluent9_12, Fluent10_12, Fluent24_14>>
/\ CandSep'

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))
\/ (\E n \in Node, k \in Key, v \in Value : Put(n,k,v))

Init ==
/\ table = [n \in Node |-> [k \in Key |-> Nil]]
/\ (owner \in [Node -> SUBSET(Key)])
/\ (\A i,j \in Node : (\A k \in Key : (((k \in owner[i]) /\ (k \in owner[j])) => i = j)))
/\ Fluent25_14 = [ x0 \in Node |-> [ x1 \in Value |-> [ x2 \in Key |-> FALSE]]]
/\ Fluent9_12 = [ x0 \in Key |-> [ x1 \in Value |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent10_12 = [ x0 \in Key |-> [ x1 \in Value |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent24_14 = [ x0 \in Node |-> [ x1 \in Value |-> [ x2 \in Key |-> FALSE]]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (table \in [Node -> [Key -> (Value \cup {Nil})]])
/\ (owner \in [Node -> SUBSET(Key)])

Safety == (\A n1,n2 \in Node, k \in Key, v1,v2 \in Value : ((table[n1][k] = v1 /\ table[n2][k] = v2) => (n1 = n2 /\ v1 = v2)))
=============================================================================
