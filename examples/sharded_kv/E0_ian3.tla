--------------------------- MODULE E0_ian3 ---------------------------
EXTENDS Naturals

CONSTANTS Key, Value, Node

VARIABLES transfer_msg, ctr1, ctr2

Nil == "nil"

vars == <<transfer_msg,ctr1,ctr2>>

CandSep == \A n \in Node : \A k \in Key : \A v \in Value : ~ctr2[n][k][v]

Reshard(k,v,n_old,n_new) ==
/\ transfer_msg' = (transfer_msg \cup {<<n_new,k,v>>})
/\ ctr1' = [ctr1 EXCEPT![n_new][k][v] = FALSE]
/\ ctr2' = [ctr2 EXCEPT![n_new][k][v] = FALSE]

RecvTransferMsg(n,k,v) ==
/\ (<<n,k,v>> \in transfer_msg)
/\ transfer_msg' = (transfer_msg \ {<<n,k,v>>})
/\ ctr1' = [ctr1 EXCEPT![n][k][v] = TRUE]
/\ ctr2' = [ctr2 EXCEPT![n][k][v] = ctr1[n][k][v]]

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))

Init ==
/\ transfer_msg = {}
/\ ctr1 = [n \in Node |-> [k \in Key |-> [v \in Value |-> TRUE]]]
/\ ctr2 = [n \in Node |-> [k \in Key |-> [v \in Value |-> FALSE]]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (transfer_msg \in SUBSET((Node \X Key \X Value)))
=============================================================================
