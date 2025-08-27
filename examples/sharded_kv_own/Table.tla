---- MODULE Table ----

CONSTANTS Key, Value, Node

Nil == "nil"

\* The key-value store state on each node.
VARIABLE table

vars == <<table>>

Reshard(k,v,n_old,n_new) ==
    /\ table[n_old][k] = v
    /\ table' = [table EXCEPT ![n_old][k] = Nil]

RecvTransferMsg(n, k, v) ==
    /\ table' = [table EXCEPT ![n][k] = v]

Put(n, k, v) == 
    /\ table' = [table EXCEPT ![n][k] = v]

Own(n, k) ==
    /\ UNCHANGED <<table>>

Next == 
    \/ \E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new)
    \/ \E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v)
    \/ \E n \in Node, k \in Key, v \in Value : Put(n,k,v)
    \/ \E n \in Node, k \in Key : Own(n,k)

Init == 
    /\ table = [n \in Node |-> [k \in Key |-> Nil]]

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ table \in [Node -> [Key -> Value \cup {Nil}]]

\* Keys unique.
Safety == 
    \A n1,n2 \in Node, k \in Key, v1,v2 \in Value : 
        (table[n1][k]=v1 /\ table[n2][k]=v2) => (n1=n2 /\ v1=v2)

====
