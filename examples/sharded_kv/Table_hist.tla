--------------------------- MODULE Table_hist ---------------------------


CONSTANTS Key, Value, Node

VARIABLES Fluent9_14, Fluent6_4, Fluent2_8, Fluent5_4, Fluent3_8, Fluent10_14, Fluent11_14, table

vars == <<Fluent9_14, Fluent6_4, Fluent2_8, Fluent5_4, Fluent3_8, Fluent10_14, Fluent11_14, table>>

CandSep ==
/\ \A var0 \in Key : \E var1 \in Node : (Fluent5_4[var0][var1]) => (Fluent6_4[var0][var1])
/\ \A var0 \in Node : (Fluent3_8[var0]) => (Fluent2_8[var0])
/\ \A var0 \in Node : \A var1 \in Key : (Fluent10_14[var0][var1]) => ((Fluent11_14[var0][var1]) => (Fluent9_14[var0][var1]))

Nil == "nil"

Reshard(k,v,n_old,n_new) ==
/\ table[n_old][k] = v
/\ table' = [table EXCEPT![n_old][k] = Nil]
/\ Fluent9_14' = [Fluent9_14 EXCEPT ![n_new][k] = TRUE]
/\ Fluent6_4' = [Fluent6_4 EXCEPT ![k][n_new] = TRUE]
/\ Fluent2_8' = [Fluent2_8 EXCEPT ![n_new] = TRUE]
/\ Fluent10_14' = [x0 \in Node |-> [x1 \in Key |-> FALSE]]
/\ Fluent11_14' = [Fluent11_14 EXCEPT ![n_old][k] = TRUE]
/\ UNCHANGED<<Fluent5_4, Fluent3_8>>
/\ CandSep'

RecvTransferMsg(n,k,v) ==
/\ table' = [table EXCEPT![n][k] = v]
/\ Fluent3_8' = [Fluent3_8 EXCEPT ![n] = TRUE]
/\ UNCHANGED<<Fluent9_14, Fluent6_4, Fluent2_8, Fluent5_4, Fluent10_14, Fluent11_14>>
/\ CandSep'

Put(n,k,v) ==
/\ table' = [table EXCEPT![n][k] = v]
/\ Fluent5_4' = [Fluent5_4 EXCEPT ![k][n] = TRUE]
/\ Fluent10_14' = [Fluent10_14 EXCEPT ![n][k] = TRUE]
/\ UNCHANGED<<Fluent9_14, Fluent6_4, Fluent2_8, Fluent3_8, Fluent11_14>>
/\ CandSep'

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))
\/ (\E n \in Node, k \in Key, v \in Value : Put(n,k,v))

Init ==
/\ table = [n \in Node |-> [k \in Key |-> Nil]]
/\ Fluent9_14 = [ x0 \in Node |-> [ x1 \in Key |-> FALSE]]
/\ Fluent6_4 = [ x0 \in Key |-> [ x1 \in Node |-> FALSE]]
/\ Fluent2_8 = [ x0 \in Node |-> FALSE]
/\ Fluent5_4 = [ x0 \in Key |-> [ x1 \in Node |-> FALSE]]
/\ Fluent3_8 = [ x0 \in Node |-> FALSE]
/\ Fluent10_14 = [ x0 \in Node |-> [ x1 \in Key |-> FALSE]]
/\ Fluent11_14 = [ x0 \in Node |-> [ x1 \in Key |-> FALSE]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (table \in [Node -> [Key -> (Value \cup {Nil})]])

Safety == (\A n1,n2 \in Node, k \in Key, v1,v2 \in Value : ((table[n1][k] = v1 /\ table[n2][k] = v2) => (n1 = n2 /\ v1 = v2)))
=============================================================================
