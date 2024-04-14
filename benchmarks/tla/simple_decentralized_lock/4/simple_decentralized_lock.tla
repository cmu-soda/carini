---- MODULE simple_decentralized_lock ----
\* benchmark: ex-simple-decentralized-lock

Node == {"n1","n2","n3","n4"}

VARIABLE message
VARIABLE has_lock

vars == <<message, has_lock>>

Send(src, dst) ==
    /\ src \in has_lock
    /\ message' = message \cup {<<src, dst>>}
    /\ has_lock' = has_lock \ {src}

Recv(src, dst) ==
    /\ <<src, dst>> \in message
    /\ message' = message \ {<<src,dst>>}
    /\ has_lock' = has_lock \cup {dst}

Next ==
    \/ \E src,dst \in Node : Send(src,dst)
    \/ \E src,dst \in Node : Recv(src,dst)

Init ==
    /\ message = {}
    /\ \E start \in Node : has_lock = {start}

Spec == Init /\ [][Next]_vars

TypeOK == 
    /\ message \in SUBSET (Node \X Node)
    /\ has_lock \in SUBSET Node

\* Two nodes can't hold lock at once.
Inv == \A x,y \in Node : (x \in has_lock /\ y \in has_lock) => (x = y)

====
