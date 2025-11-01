--------------------------- MODULE E0_ian ---------------------------
EXTENDS Naturals

CONSTANTS Key, Value, Node

VARIABLES transfer_msg, reshardCount, recvTransferMsgCount

Nil == "nil"

vars == <<transfer_msg,reshardCount,recvTransferMsgCount>>

CandSep ==
    \A n \in Node : \A k \in Key : \A v \in Value :
        \/ reshardCount[n][k][v] = recvTransferMsgCount[n][k][v]
        \/ reshardCount[n][k][v] = recvTransferMsgCount[n][k][v] + 1

Reshard(k,v,n_old,n_new) ==
/\ transfer_msg' = (transfer_msg \cup {<<n_new,k,v>>})
/\ reshardCount' = [reshardCount EXCEPT![n_new][k][v] = 1]
/\ recvTransferMsgCount' = [recvTransferMsgCount EXCEPT![n_new][k][v] = 0]

RecvTransferMsg(n,k,v) ==
/\ (<<n,k,v>> \in transfer_msg)
/\ transfer_msg' = (transfer_msg \ {<<n,k,v>>})
/\ recvTransferMsgCount' = [recvTransferMsgCount EXCEPT![n][k][v] = @+1]
/\ UNCHANGED<<reshardCount>>

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))

Init ==
/\ transfer_msg = {}
/\ reshardCount = [n \in Node |-> [k \in Key |-> [v \in Value |-> 0]]]
/\ recvTransferMsgCount = [n \in Node |-> [k \in Key |-> [v \in Value |-> 0]]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (transfer_msg \in SUBSET((Node \X Key \X Value)))
=============================================================================
