------------- MODULE Ring -------------

EXTENDS Naturals, TLC, FiniteSets

CONSTANTS Node, Id

N == Cardinality(Node)

id == 0 :> 5 @@ 1 :> 3 @@ 2 :> 8

ASSUME 
    /\ Id \subseteq Nat
    /\ id \in [Node -> Id]
    /\ \A i,j \in Node : i # j => id[i] # id[j]

succ(n) == (n + 1) % N

VARIABLE inbox

TypeOK ==
    /\ inbox \in [Node -> SUBSET Id]

Init ==
    /\ inbox = [i \in Node |-> {}]

Send(i,m) ==
    /\ inbox' = [inbox EXCEPT ![succ(i)] = @ \cup {m}]

Delete(i,m) ==
    /\ m \in inbox[i]
    /\ inbox' = [inbox EXCEPT ![i] = @ \ {m}]

Propagate(i,m) ==
    /\ m \in inbox[i]
    /\ inbox' = [inbox EXCEPT ![i] = @ \ {m}, ![succ(i)] = @ \cup {m}]

Next ==
    \E i \in Node, m \in Id :
        \/ Send(i,m)
        \/ Delete(i,m)
        \/ Propagate(i,m)

Spec == Init /\ [][Next]_inbox

===============================
