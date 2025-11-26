------------- MODULE Leader -------------

EXTENDS Naturals, TLC, FiniteSets

CONSTANTS Node, Id

id == 0 :> 5 @@ 1 :> 3 @@ 2 :> 8

ASSUME 
    /\ Id \subseteq Nat
    /\ id \in [Node -> Id]
    /\ \A i,j \in Node : i # j => id[i] # id[j]

VARIABLE elected

TypeOK ==
    /\ elected \subseteq Node

Init ==
    /\ elected = {}

Send(i,m) ==
    /\ m = id[i]
    /\ UNCHANGED elected

Delete(i,m) ==
    /\ m <= id[i]
    /\ IF m = id[i] THEN elected' = elected \cup {i} ELSE UNCHANGED elected

Propagate(i,m) ==
    /\ m > id[i]
    /\ UNCHANGED elected

Next ==
    \E i \in Node, m \in Id :
        \/ Send(i,m)
        \/ Delete(i,m)
        \/ Propagate(i,m)

Spec == Init /\ [][Next]_elected

AtMostOneLeader == Cardinality(elected) <= 1

===============================
