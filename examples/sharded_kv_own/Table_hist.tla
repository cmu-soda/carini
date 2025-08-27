--------------------------- MODULE Table_hist ---------------------------


CONSTANTS Key, Value, Node

VARIABLES Fluent12_2, Fluent13_4, Fluent23_17, Fluent22_17, Fluent14_4, Fluent19_20, Fluent20_20, Fluent27_9, Fluent26_9, table, Fluent11_2

vars == <<Fluent12_2, Fluent13_4, Fluent23_17, Fluent22_17, Fluent14_4, Fluent19_20, Fluent20_20, Fluent27_9, Fluent26_9, table, Fluent11_2>>

CandSep ==
/\ /\ \A var0 \in Node : (Fluent11_2[var0]) => (Fluent12_2[var0])
/\ \A var0 \in Key : (Fluent13_4[var0]) => (Fluent14_4[var0])
/\ \A var0 \in Key : \A var1 \in Node : (Fluent20_20[var1][var0]) => (~(Fluent19_20[var1][var0]))
/\ UNSAT
/\ \A var0 \in Node : \A var1 \in Key : (Fluent27_9[var0][var1]) => (Fluent26_9[var0][var1])
/\ \A var0 \in Key : \E var1 \in Node : (Fluent22_17[var1][var0]) => (Fluent23_17[var1])

Nil == "nil"

Reshard(k,v,n_old,n_new) ==
/\ table[n_old][k] = v
/\ table' = [table EXCEPT![n_old][k] = Nil]
/\ Fluent12_2' = [Fluent12_2 EXCEPT ![n_new] = TRUE]
/\ Fluent19_20' = [Fluent19_20 EXCEPT ![n_old][k] = TRUE]
/\ Fluent20_20' = [Fluent20_20 EXCEPT ![n_old][k] = FALSE]
/\ UNCHANGED<<Fluent13_4, Fluent23_17, Fluent22_17, Fluent14_4, Fluent27_9, Fluent26_9, Fluent11_2>>
/\ CandSep'

RecvTransferMsg(n,k,v) ==
/\ table' = [table EXCEPT![n][k] = v]
/\ Fluent23_17' = [Fluent23_17 EXCEPT ![n] = TRUE]
/\ Fluent19_20' = [Fluent19_20 EXCEPT ![n][k] = FALSE]
/\ Fluent26_9' = [Fluent26_9 EXCEPT ![n][k] = TRUE]
/\ Fluent11_2' = [Fluent11_2 EXCEPT ![n] = TRUE]
/\ UNCHANGED<<Fluent12_2, Fluent13_4, Fluent22_17, Fluent14_4, Fluent20_20, Fluent27_9>>
/\ CandSep'

Put(n,k,v) ==
/\ table' = [table EXCEPT![n][k] = v]
/\ Fluent13_4' = [Fluent13_4 EXCEPT ![k] = TRUE]
/\ Fluent22_17' = [Fluent22_17 EXCEPT ![n][k] = TRUE]
/\ Fluent14_4' = [Fluent14_4 EXCEPT ![k] = TRUE]
/\ Fluent20_20' = [Fluent20_20 EXCEPT ![n][k] = TRUE]
/\ Fluent27_9' = [Fluent27_9 EXCEPT ![n][k] = TRUE]
/\ UNCHANGED<<Fluent12_2, Fluent23_17, Fluent19_20, Fluent26_9, Fluent11_2>>
/\ CandSep'

Own(n,k) ==
/\ UNCHANGED <<table>>
/\ Fluent14_4' = [Fluent14_4 EXCEPT ![k] = FALSE]
/\ Fluent26_9' = [Fluent26_9 EXCEPT ![n][k] = TRUE]
/\ UNCHANGED<<Fluent12_2, Fluent13_4, Fluent23_17, Fluent22_17, Fluent19_20, Fluent20_20, Fluent27_9, Fluent11_2>>
/\ CandSep'

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))
\/ (\E n \in Node, k \in Key, v \in Value : Put(n,k,v))
\/ (\E n \in Node, k \in Key : Own(n,k))

Init ==
/\ table = [n \in Node |-> [k \in Key |-> Nil]]
/\ Fluent12_2 = [ x0 \in Node |-> FALSE]
/\ Fluent13_4 = [ x0 \in Key |-> FALSE]
/\ Fluent23_17 = [ x0 \in Node |-> FALSE]
/\ Fluent22_17 = [ x0 \in Node |-> [ x1 \in Key |-> FALSE]]
/\ Fluent14_4 = [ x0 \in Key |-> FALSE]
/\ Fluent19_20 = [ x0 \in Node |-> [ x1 \in Key |-> FALSE]]
/\ Fluent20_20 = [ x0 \in Node |-> [ x1 \in Key |-> FALSE]]
/\ Fluent27_9 = [ x0 \in Node |-> [ x1 \in Key |-> FALSE]]
/\ Fluent26_9 = [ x0 \in Node |-> [ x1 \in Key |-> FALSE]]
/\ Fluent11_2 = [ x0 \in Node |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (table \in [Node -> [Key -> (Value \cup {Nil})]])

Safety == (\A n1,n2 \in Node, k \in Key, v1,v2 \in Value : ((table[n1][k] = v1 /\ table[n2][k] = v2) => (n1 = n2 /\ v1 = v2)))
=============================================================================
