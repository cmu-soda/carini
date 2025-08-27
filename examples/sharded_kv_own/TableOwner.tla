---- MODULE TableOwner ----

CONSTANTS Key, Value, Node

Nil == "nil"

\* The key-value store state on each node.
VARIABLE table

\* The set of keys owned by each node.
VARIABLE owner

vars == <<table, owner>>

Reshard(k,v,n_old,n_new) ==
    /\ table[n_old][k] = v
    /\ table' = [table EXCEPT ![n_old][k] = Nil]
    /\ owner' = [owner EXCEPT ![n_old] = owner[n_old] \ {k}]

RecvTransferMsg(n, k, v) ==
    /\ table' = [table EXCEPT ![n][k] = v]
    \* Become the owner of this key.
    /\ owner' = [owner EXCEPT ![n] = owner[n] \cup {k}]

Put(n, k, v) == 
    /\ k \in owner[n]
    /\ table' = [table EXCEPT ![n][k] = v]
    /\ UNCHANGED <<owner>>

Own(n, k) ==
    /\ \A n2 \in Node : k \notin owner[n2]
    /\ owner' = [owner EXCEPT ![n] = owner[n] \cup {k}]
    /\ UNCHANGED <<table>>

Next == 
    \/ \E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new)
    \/ \E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v)
    \/ \E n \in Node, k \in Key, v \in Value : Put(n,k,v)
    \/ \E n \in Node, k \in Key : Own(n,k)

Init == 
    /\ table = [n \in Node |-> [k \in Key |-> Nil]]
    /\ owner = [n \in Node |-> {}]

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ table \in [Node -> [Key -> Value \cup {Nil}]]
    /\ owner \in [Node -> SUBSET Key]

\* Keys unique.
Safety == 
    \A n1,n2 \in Node, k \in Key, v1,v2 \in Value : 
        (table[n1][k]=v1 /\ table[n2][k]=v2) => (n1=n2 /\ v1=v2)

====
