--------------------------- MODULE E0_ian2 ---------------------------
EXTENDS Naturals

CONSTANTS Key, Value, Node

VARIABLES transfer_msg, recvTransferMsgCount

Nil == "nil"

vars == <<transfer_msg,recvTransferMsgCount>>

CandSep ==
    \A n \in Node : \A k \in Key : \A v \in Value :
        recvTransferMsgCount[n][k][v] <= 1

Reshard(k,v,n_old,n_new) ==
/\ transfer_msg' = (transfer_msg \cup {<<n_new,k,v>>})
/\ recvTransferMsgCount' = [recvTransferMsgCount EXCEPT![n_new][k][v] = 0]

RecvTransferMsg(n,k,v) ==
/\ (<<n,k,v>> \in transfer_msg)
/\ transfer_msg' = (transfer_msg \ {<<n,k,v>>})
/\ recvTransferMsgCount' = [recvTransferMsgCount EXCEPT![n][k][v] = @+1]

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))

Init ==
/\ transfer_msg = {}
/\ recvTransferMsgCount = [n \in Node |-> [k \in Key |-> [v \in Value |-> 1]]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (transfer_msg \in SUBSET((Node \X Key \X Value)))
=============================================================================
