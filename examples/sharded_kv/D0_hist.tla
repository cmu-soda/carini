--------------------------- MODULE D0_hist ---------------------------


CONSTANTS Key, Value, Node

VARIABLES owner, Fluent2, Fluent1, Fluent0, table

vars == <<owner, Fluent2, Fluent1, Fluent0, table>>

CandSep ==
/\ \A var0 \in Key : \E var1 \in Node : Fluent0[var1][var0]
/\ \A var0 \in Key : (Fluent2[var0]) => (Fluent1[var0])

Nil == "nil"

Reshard(k,v,n_old,n_new) ==
/\ table[n_old][k] = v
/\ table' = [table EXCEPT![n_old][k] = Nil]
/\ owner' = [owner EXCEPT![n_old] = (owner[n_old] \ {k})]
/\ Fluent2' = [Fluent2 EXCEPT![k] = FALSE]
/\ Fluent0' = [Fluent0 EXCEPT![n_old][k] = TRUE]
/\ UNCHANGED<<Fluent1>>
/\ CandSep'

RecvTransferMsg(n,k,v) ==
/\ table' = [table EXCEPT![n][k] = v]
/\ owner' = [owner EXCEPT![n] = (owner[n] \cup {k})]
/\ Fluent1' = [Fluent1 EXCEPT![k] = FALSE]
/\ Fluent0' = [Fluent0 EXCEPT![n][k] = FALSE]
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

Put(n,k,v) ==
/\ (k \in owner[n])
/\ table' = [table EXCEPT![n][k] = v]
/\ UNCHANGED <<owner>>
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ CandSep'

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))
\/ (\E n \in Node, k \in Key, v \in Value : Put(n,k,v))

Init ==
/\ table = [n \in Node |-> [k \in Key |-> Nil]]
/\ (owner \in [Node -> SUBSET(Key)])
/\ (\A i,j \in Node : (\A k \in Key : (((k \in owner[i]) /\ (k \in owner[j])) => i = j)))
/\ Fluent2 = [ x0 \in Key |-> TRUE]
/\ Fluent1 = [ x0 \in Key |-> TRUE]
/\ Fluent0 = [ x0 \in Node |-> [ x1 \in Key |-> TRUE]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (table \in [Node -> [Key -> (Value \cup {Nil})]])
/\ (owner \in [Node -> SUBSET(Key)])

Safety == (\A n1,n2 \in Node, k \in Key, v1,v2 \in Value : ((table[n1][k] = v1 /\ table[n2][k] = v2) => (n1 = n2 /\ v1 = v2)))
=============================================================================
