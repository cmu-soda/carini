---- MODULE OwnerTransfer ----

CONSTANTS Key, Value, Node

Nil == "nil"

\* The set of keys owned by each node.
VARIABLE owner

\* The set of active transfer messages.
VARIABLE transfer_msg

vars == <<owner, transfer_msg>>

Reshard(k,v,n_old,n_new) ==
    /\ owner' = [owner EXCEPT ![n_old] = owner[n_old] \ {k}]
    /\ transfer_msg' = transfer_msg \cup {<<n_new,k,v>>}

RecvTransferMsg(n, k, v) ==
    /\ <<n,k,v>> \in transfer_msg
    /\ transfer_msg' = transfer_msg \ {<<n,k,v>>}
    /\ owner' = [owner EXCEPT ![n] = owner[n] \cup {k}]

Put(n, k, v) == 
    /\ k \in owner[n]
    /\ UNCHANGED <<owner, transfer_msg>>

Own(n, k) ==
    /\ \A n2 \in Node : k \notin owner[n2]
    /\ \A n2 \in Node : \A v2 \in Value : <<n2,k,v2>> \notin transfer_msg
    /\ owner' = [owner EXCEPT ![n] = owner[n] \cup {k}]
    /\ UNCHANGED <<transfer_msg>>

Next == 
    \/ \E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new)
    \/ \E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v)
    \/ \E n \in Node, k \in Key, v \in Value : Put(n,k,v)
    \/ \E n \in Node, k \in Key : Own(n,k)

Init == 
    /\ owner = [n \in Node |-> {}]
    /\ transfer_msg = {}

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ owner \in [Node -> SUBSET Key]
    /\ transfer_msg \in SUBSET (Node \times Key \times Value)

====
