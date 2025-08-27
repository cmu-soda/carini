---- MODULE Transfer ----

CONSTANTS Key, Value, Node

Nil == "nil"

\* The set of active transfer messages.
VARIABLE transfer_msg

vars == <<transfer_msg>>

Reshard(k,v,n_old,n_new) ==
    /\ transfer_msg' = transfer_msg \cup {<<n_new,k,v>>}

RecvTransferMsg(n, k, v) ==
    /\ <<n,k,v>> \in transfer_msg
    /\ transfer_msg' = transfer_msg \ {<<n,k,v>>}

Own(n, k) ==
    /\ \A n2 \in Node : \A v2 \in Value : <<n2,k,v2>> \notin transfer_msg
    /\ UNCHANGED <<transfer_msg>>

Next == 
    \/ \E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new)
    \/ \E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v)
    \/ \E n \in Node, k \in Key : Own(n,k)

Init == 
    /\ transfer_msg = {}

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ transfer_msg \in SUBSET (Node \times Key \times Value)

====
