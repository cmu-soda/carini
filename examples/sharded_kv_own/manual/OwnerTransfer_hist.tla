--------------------------- MODULE OwnerTransfer_hist ---------------------------


CONSTANTS Key, Value, Node

VARIABLES owner, Fluent6_4, Fluent5_4, transfer_msg, Fluent13_21, Fluent12_21, Fluent15_23, Fluent10_3, Fluent25_1, Fluent11_3, Fluent16_23, Fluent20_8, Fluent26_1, Fluent22_8, Fluent21_8,
    rcvMsg, transfer

vars == <<owner, Fluent6_4, Fluent5_4, transfer_msg, Fluent13_21, Fluent12_21, Fluent15_23, Fluent10_3, Fluent25_1, Fluent11_3, Fluent16_23, Fluent20_8, Fluent26_1, Fluent22_8, Fluent21_8,
    rcvMsg, transfer>>

CandSep ==
/\ /\ \A var0 \in Key : (Fluent5_4[var0]) => (Fluent6_4[var0])
/\ \A var0 \in Key : (Fluent12_21[var0]) => (Fluent13_21[var0])
/\ \A var0 \in Node : \A var1 \in Key : (Fluent21_8[var1][var0]) => ((Fluent20_8[var1][var0]) => (Fluent22_8[var1][var0]))
/\ \A var0 \in Node : (Fluent10_3[var0]) => (Fluent11_3[var0])
/\ \A var0 \in Key : \E var1 \in Node : (Fluent15_23[var1][var0]) => (Fluent16_23[var1])
/\ \A var0 \in Node : \A var1 \in Key : (Fluent25_1[var0][var1]) => (Fluent26_1[var0][var1])
/\ \A n \in Node : \A k \in Key : \A v \in Value : rcvMsg[k][n][v] => transfer[k][n][v]

Nil == "nil"

Reshard(k,v,n_old,n_new) ==
/\ owner' = [owner EXCEPT![n_old] = (owner[n_old] \ {k})]
/\ transfer_msg' = (transfer_msg \cup {<<n_new,k,v>>})
/\ Fluent6_4' = [Fluent6_4 EXCEPT ![k] = TRUE]
/\ Fluent11_3' = [Fluent11_3 EXCEPT ![n_new] = TRUE]
/\ Fluent20_8' = [x0 \in Key |-> [x1 \in Node |-> FALSE]]
/\ Fluent22_8' = [Fluent22_8 EXCEPT ![k][n_new] = TRUE]
/\ Fluent21_8' = [Fluent21_8 EXCEPT ![k][n_old] = TRUE]
/\ UNCHANGED<<Fluent5_4, Fluent13_21, Fluent12_21, Fluent15_23, Fluent10_3, Fluent25_1, Fluent16_23, Fluent26_1>>
/\ rcvMsg' = [rcvMsg EXCEPT![k] = [ x1 \in Node |-> [ x2 \in Value |-> FALSE]]]
/\ transfer' = [[transfer EXCEPT![k] = [ x1 \in Node |-> [ x2 \in Value |-> FALSE]]] EXCEPT![k][n_new][v] = TRUE]

RecvTransferMsg(n,k,v) ==
/\ (<<n,k,v>> \in transfer_msg)
/\ transfer_msg' = (transfer_msg \ {<<n,k,v>>})
/\ owner' = [owner EXCEPT![n] = (owner[n] \cup {k})]
/\ Fluent5_4' = [Fluent5_4 EXCEPT ![k] = TRUE]
/\ Fluent10_3' = [Fluent10_3 EXCEPT ![n] = TRUE]
/\ Fluent16_23' = [Fluent16_23 EXCEPT ![n] = TRUE]
/\ Fluent26_1' = [Fluent26_1 EXCEPT ![n][k] = TRUE]
/\ UNCHANGED<<Fluent6_4, Fluent13_21, Fluent12_21, Fluent15_23, Fluent25_1, Fluent11_3, Fluent20_8, Fluent22_8, Fluent21_8>>
/\ rcvMsg' = [rcvMsg EXCEPT![k][n][v] = TRUE]
/\ transfer' = [transfer EXCEPT![n][k][v] = FALSE]

Put(n,k,v) ==
/\ (k \in owner[n])
/\ UNCHANGED <<owner,transfer_msg>>
/\ Fluent13_21' = [Fluent13_21 EXCEPT ![k] = TRUE]
/\ Fluent12_21' = [Fluent12_21 EXCEPT ![k] = TRUE]
/\ Fluent15_23' = [Fluent15_23 EXCEPT ![n][k] = TRUE]
/\ Fluent25_1' = [Fluent25_1 EXCEPT ![n][k] = TRUE]
/\ Fluent20_8' = [Fluent20_8 EXCEPT ![k][n] = TRUE]
/\ UNCHANGED<<Fluent6_4, Fluent5_4, Fluent10_3, Fluent11_3, Fluent16_23, Fluent26_1, Fluent22_8, Fluent21_8>>
/\ UNCHANGED <<rcvMsg, transfer>>

Own(n,k) ==
/\ (\A n2 \in Node : (k \notin owner[n2]))
/\ (\A n2 \in Node : (\A v2 \in Value : (<<n2,k,v2>> \notin transfer_msg)))
/\ owner' = [owner EXCEPT![n] = (owner[n] \cup {k})]
/\ UNCHANGED <<transfer_msg>>
/\ Fluent13_21' = [Fluent13_21 EXCEPT ![k] = FALSE]
/\ Fluent26_1' = [Fluent26_1 EXCEPT ![n][k] = TRUE]
/\ UNCHANGED<<Fluent6_4, Fluent5_4, Fluent12_21, Fluent15_23, Fluent10_3, Fluent25_1, Fluent11_3, Fluent16_23, Fluent20_8, Fluent22_8, Fluent21_8>>
/\ UNCHANGED <<rcvMsg, transfer>>

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))
\/ (\E n \in Node, k \in Key, v \in Value : Put(n,k,v))
\/ (\E n \in Node, k \in Key : Own(n,k))

Init ==
/\ owner = [n \in Node |-> {}]
/\ transfer_msg = {}
/\ Fluent6_4 = [ x0 \in Key |-> FALSE]
/\ Fluent5_4 = [ x0 \in Key |-> FALSE]
/\ Fluent13_21 = [ x0 \in Key |-> FALSE]
/\ Fluent12_21 = [ x0 \in Key |-> FALSE]
/\ Fluent15_23 = [ x0 \in Node |-> [ x1 \in Key |-> FALSE]]
/\ Fluent10_3 = [ x0 \in Node |-> FALSE]
/\ Fluent25_1 = [ x0 \in Node |-> [ x1 \in Key |-> FALSE]]
/\ Fluent11_3 = [ x0 \in Node |-> FALSE]
/\ Fluent16_23 = [ x0 \in Node |-> FALSE]
/\ Fluent20_8 = [ x0 \in Key |-> [ x1 \in Node |-> FALSE]]
/\ Fluent26_1 = [ x0 \in Node |-> [ x1 \in Key |-> FALSE]]
/\ Fluent22_8 = [ x0 \in Key |-> [ x1 \in Node |-> FALSE]]
/\ Fluent21_8 = [ x0 \in Key |-> [ x1 \in Node |-> FALSE]]
/\ rcvMsg = [ x0 \in Key |-> [ x1 \in Node |-> [ x2 \in Value |-> FALSE]]]
/\ transfer = [ x0 \in Key |-> [ x1 \in Node |-> [ x2 \in Value |-> FALSE]]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (owner \in [Node -> SUBSET(Key)])
/\ (transfer_msg \in SUBSET((Node \X Key \X Value)))
=============================================================================
