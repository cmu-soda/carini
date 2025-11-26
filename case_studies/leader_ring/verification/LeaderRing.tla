------------- MODULE LeaderRing -------------

EXTENDS Naturals, TLC, FiniteSets

CONSTANTS Node, Id

N == Cardinality(Node)

id == 0 :> 5 @@ 1 :> 3 @@ 2 :> 8

ASSUME 
    /\ Id \subseteq Nat
    /\ id \in [Node -> Id]
    /\ \A i,j \in Node : i # j => id[i] # id[j]

succ(n) == (n + 1) % N

VARIABLE elected
VARIABLE inbox

TypeOK ==
    /\ elected \subseteq Node
    /\ inbox \in [Node -> SUBSET Id]

Init ==
    /\ elected = {}
    /\ inbox = [i \in Node |-> {}]

Send(i,m) ==
    /\ m = id[i] /\ UNCHANGED elected
    /\ inbox' = [inbox EXCEPT ![succ(i)] = @ \cup {m}]

Delete(i,m) ==
    /\ m <= id[i]
    /\ IF m = id[i] THEN elected' = elected \cup {i} ELSE UNCHANGED elected
    /\ m \in inbox[i]
    /\ inbox' = [inbox EXCEPT ![i] = @ \ {m}]

Propagate(i,m) ==
    /\ m > id[i]
    /\ UNCHANGED elected
    /\ m \in inbox[i]
    /\ inbox' = [inbox EXCEPT ![i] = @ \ {m}, ![succ(i)] = @ \cup {m}]

Next ==
    \E i \in Node, m \in Id :
        \/ Send(i,m)
        \/ Delete(i,m)
        \/ Propagate(i,m)

Spec == Init /\ [][Next]_elected

AtMostOneLeader == Cardinality(elected) <= 1

===============================
