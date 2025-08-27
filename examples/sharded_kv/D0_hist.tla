--------------------------- MODULE D0_hist ---------------------------


CONSTANTS Key, Value, Node

VARIABLES owner, Fluent3_7, Fluent2_7, Fluent4_24, Fluent5_24, table

vars == <<owner, Fluent3_7, Fluent2_7, Fluent4_24, Fluent5_24, table>>

CandSep ==
/\ /\ \A var0 \in Node : (Fluent4_24[var0]) => (Fluent5_24[var0])
/\ \A var0 \in Key : (Fluent3_7[var0]) => (Fluent2_7[var0])
/\ UNSAT

Nil == "nil"

Reshard(k,v,n_old,n_new) ==
/\ table[n_old][k] = v
/\ table' = [table EXCEPT![n_old][k] = Nil]
/\ owner' = [owner EXCEPT![n_old] = (owner[n_old] \ {k})]
/\ Fluent5_24' = [Fluent5_24 EXCEPT ![n_new] = TRUE]
/\ Fluent2_7' = [Fluent2_7 EXCEPT ![k] = TRUE]
/\ UNCHANGED<<Fluent4_24, Fluent3_7>>
/\ CandSep'

RecvTransferMsg(n,k,v) ==
/\ table' = [table EXCEPT![n][k] = v]
/\ owner' = [owner EXCEPT![n] = (owner[n] \cup {k})]
/\ Fluent4_24' = [Fluent4_24 EXCEPT ![n] = TRUE]
/\ Fluent3_7' = [Fluent3_7 EXCEPT ![k] = TRUE]
/\ UNCHANGED<<Fluent5_24, Fluent2_7>>
/\ CandSep'

Put(n,k,v) ==
/\ (k \in owner[n])
/\ table' = [table EXCEPT![n][k] = v]
/\ UNCHANGED <<owner>>
/\ UNCHANGED<<Fluent4_24, Fluent5_24, Fluent3_7, Fluent2_7>>
/\ CandSep'

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))
\/ (\E n \in Node, k \in Key, v \in Value : Put(n,k,v))

Init ==
/\ table = [n \in Node |-> [k \in Key |-> Nil]]
/\ (owner \in [Node -> SUBSET(Key)])
/\ (\A i,j \in Node : (\A k \in Key : (((k \in owner[i]) /\ (k \in owner[j])) => i = j)))
/\ Fluent4_24 = [ x0 \in Node |-> FALSE]
/\ Fluent5_24 = [ x0 \in Node |-> FALSE]
/\ Fluent3_7 = [ x0 \in Key |-> FALSE]
/\ Fluent2_7 = [ x0 \in Key |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (table \in [Node -> [Key -> (Value \cup {Nil})]])
/\ (owner \in [Node -> SUBSET(Key)])

Safety == (\A n1,n2 \in Node, k \in Key, v1,v2 \in Value : ((table[n1][k] = v1 /\ table[n2][k] = v2) => (n1 = n2 /\ v1 = v2)))
=============================================================================
