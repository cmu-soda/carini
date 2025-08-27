--------------------------- MODULE OwnerTransfer_hist ---------------------------


CONSTANTS Key, Value, Node

VARIABLES owner, Fluent12_2, Fluent13_4, Fluent23_17, Fluent22_17, Fluent14_4, Fluent19_20, Fluent20_20, Fluent27_9, Fluent26_9, transfer_msg, Fluent11_2

vars == <<owner, Fluent12_2, Fluent13_4, Fluent23_17, Fluent22_17, Fluent14_4, Fluent19_20, Fluent20_20, Fluent27_9, Fluent26_9, transfer_msg, Fluent11_2>>

CandSep ==
/\ /\ \A var0 \in Node : (Fluent11_2[var0]) => (Fluent12_2[var0])
/\ \A var0 \in Key : (Fluent13_4[var0]) => (Fluent14_4[var0])
/\ \A var0 \in Key : \A var1 \in Node : (Fluent20_20[var1][var0]) => (~(Fluent19_20[var1][var0]))
/\ UNSAT
/\ \A var0 \in Node : \A var1 \in Key : (Fluent27_9[var0][var1]) => (Fluent26_9[var0][var1])
/\ \A var0 \in Key : \E var1 \in Node : (Fluent22_17[var1][var0]) => (Fluent23_17[var1])

Nil == "nil"

Reshard(k,v,n_old,n_new) ==
/\ owner' = [owner EXCEPT![n_old] = (owner[n_old] \ {k})]
/\ transfer_msg' = (transfer_msg \cup {<<n_new,k,v>>})
/\ Fluent12_2' = [Fluent12_2 EXCEPT ![n_new] = TRUE]
/\ Fluent19_20' = [Fluent19_20 EXCEPT ![n_old][k] = TRUE]
/\ Fluent20_20' = [Fluent20_20 EXCEPT ![n_old][k] = FALSE]
/\ UNCHANGED<<Fluent13_4, Fluent23_17, Fluent22_17, Fluent14_4, Fluent27_9, Fluent26_9, Fluent11_2>>

RecvTransferMsg(n,k,v) ==
/\ (<<n,k,v>> \in transfer_msg)
/\ transfer_msg' = (transfer_msg \ {<<n,k,v>>})
/\ owner' = [owner EXCEPT![n] = (owner[n] \cup {k})]
/\ Fluent23_17' = [Fluent23_17 EXCEPT ![n] = TRUE]
/\ Fluent19_20' = [Fluent19_20 EXCEPT ![n][k] = FALSE]
/\ Fluent26_9' = [Fluent26_9 EXCEPT ![n][k] = TRUE]
/\ Fluent11_2' = [Fluent11_2 EXCEPT ![n] = TRUE]
/\ UNCHANGED<<Fluent12_2, Fluent13_4, Fluent22_17, Fluent14_4, Fluent20_20, Fluent27_9>>

Put(n,k,v) ==
/\ (k \in owner[n])
/\ UNCHANGED <<owner,transfer_msg>>
/\ Fluent13_4' = [Fluent13_4 EXCEPT ![k] = TRUE]
/\ Fluent22_17' = [Fluent22_17 EXCEPT ![n][k] = TRUE]
/\ Fluent14_4' = [Fluent14_4 EXCEPT ![k] = TRUE]
/\ Fluent20_20' = [Fluent20_20 EXCEPT ![n][k] = TRUE]
/\ Fluent27_9' = [Fluent27_9 EXCEPT ![n][k] = TRUE]
/\ UNCHANGED<<Fluent12_2, Fluent23_17, Fluent19_20, Fluent26_9, Fluent11_2>>

Own(n,k) ==
/\ (\A n2 \in Node : (k \notin owner[n2]))
/\ (\A n2 \in Node : (\A v2 \in Value : (<<n2,k,v2>> \notin transfer_msg)))
/\ owner' = [owner EXCEPT![n] = (owner[n] \cup {k})]
/\ UNCHANGED <<transfer_msg>>
/\ Fluent14_4' = [Fluent14_4 EXCEPT ![k] = FALSE]
/\ Fluent26_9' = [Fluent26_9 EXCEPT ![n][k] = TRUE]
/\ UNCHANGED<<Fluent12_2, Fluent13_4, Fluent23_17, Fluent22_17, Fluent19_20, Fluent20_20, Fluent27_9, Fluent11_2>>

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))
\/ (\E n \in Node, k \in Key, v \in Value : Put(n,k,v))
\/ (\E n \in Node, k \in Key : Own(n,k))

Init ==
/\ owner = [n \in Node |-> {}]
/\ transfer_msg = {}
/\ Fluent12_2 = [ x0 \in Node |-> FALSE]
/\ Fluent13_4 = [ x0 \in Key |-> FALSE]
/\ Fluent23_17 = [ x0 \in Node |-> FALSE]
/\ Fluent22_17 = [ x0 \in Node |-> [ x1 \in Key |-> FALSE]]
/\ Fluent14_4 = [ x0 \in Key |-> FALSE]
/\ Fluent19_20 = [ x0 \in Node |-> [ x1 \in Key |-> FALSE]]
/\ Fluent20_20 = [ x0 \in Node |-> [ x1 \in Key |-> FALSE]]
/\ Fluent27_9 = [ x0 \in Node |-> [ x1 \in Key |-> FALSE]]
/\ Fluent26_9 = [ x0 \in Node |-> [ x1 \in Key |-> FALSE]]
/\ Fluent11_2 = [ x0 \in Node |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (owner \in [Node -> SUBSET(Key)])
/\ (transfer_msg \in SUBSET((Node \X Key \X Value)))
=============================================================================
