--------------------------- MODULE D0_ian3 ---------------------------
EXTENDS Naturals

CONSTANTS Key, Value, Node

VARIABLES owner, table, ctr1, ctr2

Nil == "nil"

vars == <<table,owner,ctr1,ctr2>>

CandSep == \A n \in Node : \A k \in Key : \A v \in Value : ~ctr2[n][k][v]

Reshard(k,v,n_old,n_new) ==
/\ table[n_old][k] = v
/\ table' = [table EXCEPT![n_old][k] = Nil]
/\ owner' = [owner EXCEPT![n_old] = (owner[n_old] \ {k})]
/\ ctr1' = [ctr1 EXCEPT![n_new][k][v] = FALSE]
/\ ctr2' = [ctr2 EXCEPT![n_new][k][v] = FALSE]
/\ CandSep'

RecvTransferMsg(n,k,v) ==
/\ table' = [table EXCEPT![n][k] = v]
/\ owner' = [owner EXCEPT![n] = (owner[n] \cup {k})]
/\ ctr1' = [ctr1 EXCEPT![n][k][v] = TRUE]
/\ ctr2' = [ctr2 EXCEPT![n][k][v] = ctr1[n][k][v]]
/\ CandSep'

Put(n,k,v) ==
/\ (k \in owner[n])
/\ table' = [table EXCEPT![n][k] = v]
/\ UNCHANGED <<owner>>
/\ UNCHANGED<<ctr1,ctr2>>
/\ CandSep'

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))
\/ (\E n \in Node, k \in Key, v \in Value : Put(n,k,v))

Init ==
/\ table = [n \in Node |-> [k \in Key |-> Nil]]
/\ (owner \in [Node -> SUBSET(Key)])
/\ (\A i,j \in Node : (\A k \in Key : (((k \in owner[i]) /\ (k \in owner[j])) => i = j)))
/\ ctr1 = [n \in Node |-> [k \in Key |-> [v \in Value |-> TRUE]]]
/\ ctr2 = [n \in Node |-> [k \in Key |-> [v \in Value |-> FALSE]]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (table \in [Node -> [Key -> (Value \cup {Nil})]])
/\ (owner \in [Node -> SUBSET(Key)])

Safety == (\A n1,n2 \in Node, k \in Key, v1,v2 \in Value : ((table[n1][k] = v1 /\ table[n2][k] = v2) => (n1 = n2 /\ v1 = v2)))
=============================================================================
