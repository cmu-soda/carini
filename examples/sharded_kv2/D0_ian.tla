--------------------------- MODULE D0_ian ---------------------------
EXTENDS Naturals

CONSTANTS Key, Value, Node

VARIABLES owner, table, reshardCount, recvTransferMsgCount

Nil == "nil"

vars == <<table,owner,reshardCount,recvTransferMsgCount>>

CandSep ==
    \A n \in Node : \A k \in Key : \A v \in Value :
        \/ reshardCount[n][k][v] = recvTransferMsgCount[n][k][v]
        \/ reshardCount[n][k][v] = recvTransferMsgCount[n][k][v] + 1

Reshard(k,v,n_old,n_new) ==
/\ table[n_old][k] = v
/\ table' = [table EXCEPT![n_old][k] = Nil]
/\ owner' = [owner EXCEPT![n_old] = (owner[n_old] \ {k})]
/\ reshardCount' = [reshardCount EXCEPT![n_new][k][v] = 1]
/\ recvTransferMsgCount' = [recvTransferMsgCount EXCEPT![n_new][k][v] = 0]
/\ CandSep'

RecvTransferMsg(n,k,v) ==
/\ table' = [table EXCEPT![n][k] = v]
/\ owner' = [owner EXCEPT![n] = (owner[n] \cup {k})]
/\ recvTransferMsgCount' = [recvTransferMsgCount EXCEPT![n][k][v] = @+1]
/\ UNCHANGED<<reshardCount>>
/\ CandSep'

Put(n,k,v) ==
/\ (k \in owner[n])
/\ table' = [table EXCEPT![n][k] = v]
/\ UNCHANGED <<owner>>
/\ UNCHANGED<<reshardCount, recvTransferMsgCount>>
/\ CandSep'

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))
\/ (\E n \in Node, k \in Key, v \in Value : Put(n,k,v))

Init ==
/\ table = [n \in Node |-> [k \in Key |-> Nil]]
/\ (owner \in [Node -> SUBSET(Key)])
/\ (\A i,j \in Node : (\A k \in Key : (((k \in owner[i]) /\ (k \in owner[j])) => i = j)))
/\ reshardCount = [n \in Node |-> [k \in Key |-> [v \in Value |-> 0]]]
/\ recvTransferMsgCount = [n \in Node |-> [k \in Key |-> [v \in Value |-> 0]]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (table \in [Node -> [Key -> (Value \cup {Nil})]])
/\ (owner \in [Node -> SUBSET(Key)])

Safety == (\A n1,n2 \in Node, k \in Key, v1,v2 \in Value : ((table[n1][k] = v1 /\ table[n2][k] = v2) => (n1 = n2 /\ v1 = v2)))
=============================================================================
