--------------------------- MODULE D0_hist ---------------------------


CONSTANTS Key, Value, Node

VARIABLES owner, Fluent10_18, Fluent24_13, Fluent25_13, Fluent9_18, table

vars == <<owner, Fluent10_18, Fluent24_13, Fluent25_13, Fluent9_18, table>>

CandSep ==
/\ \A var0 \in Key : \A var1 \in Value : \A var2 \in Node : (Fluent10_18[var2][var1][var0]) => (~(Fluent9_18[var2][var1][var0]))
/\ \A var0 \in Value : \A var1 \in Node : \A var2 \in Key : (Fluent24_13[var2][var0][var1]) => (Fluent25_13[var2][var0][var1])

Nil == "nil"

Reshard(k,v,n_old,n_new) ==
/\ table[n_old][k] = v
/\ table' = [table EXCEPT![n_old][k] = Nil]
/\ owner' = [owner EXCEPT![n_old] = (owner[n_old] \ {k})]
/\ Fluent10_18' = [Fluent10_18 EXCEPT ![n_new][v][k] = FALSE]
/\ Fluent25_13' = [Fluent25_13 EXCEPT ![k][v][n_new] = TRUE]
/\ UNCHANGED<<Fluent24_13, Fluent9_18>>
/\ CandSep'

RecvTransferMsg(n,k,v) ==
/\ table' = [table EXCEPT![n][k] = v]
/\ owner' = [owner EXCEPT![n] = (owner[n] \cup {k})]
/\ Fluent10_18' = [Fluent10_18 EXCEPT ![n][v][k] = TRUE]
/\ Fluent24_13' = [Fluent24_13 EXCEPT ![k][v][n] = TRUE]
/\ Fluent9_18' = [Fluent9_18 EXCEPT ![n][v][k] = Fluent10_18[n][v][k]]
/\ UNCHANGED<<Fluent25_13>>
/\ CandSep'

Put(n,k,v) ==
/\ (k \in owner[n])
/\ table' = [table EXCEPT![n][k] = v]
/\ UNCHANGED <<owner>>
/\ UNCHANGED<<Fluent10_18, Fluent24_13, Fluent25_13, Fluent9_18>>
/\ CandSep'

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))
\/ (\E n \in Node, k \in Key, v \in Value : Put(n,k,v))

Init ==
/\ table = [n \in Node |-> [k \in Key |-> Nil]]
/\ (owner \in [Node -> SUBSET(Key)])
/\ (\A i,j \in Node : (\A k \in Key : (((k \in owner[i]) /\ (k \in owner[j])) => i = j)))
/\ Fluent10_18 = [ x0 \in Node |-> [ x1 \in Value |-> [ x2 \in Key |-> FALSE]]]
/\ Fluent24_13 = [ x0 \in Key |-> [ x1 \in Value |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent25_13 = [ x0 \in Key |-> [ x1 \in Value |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent9_18 = [ x0 \in Node |-> [ x1 \in Value |-> [ x2 \in Key |-> FALSE]]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (table \in [Node -> [Key -> (Value \cup {Nil})]])
/\ (owner \in [Node -> SUBSET(Key)])

Safety == (\A n1,n2 \in Node, k \in Key, v1,v2 \in Value : ((table[n1][k] = v1 /\ table[n2][k] = v2) => (n1 = n2 /\ v1 = v2)))
=============================================================================
