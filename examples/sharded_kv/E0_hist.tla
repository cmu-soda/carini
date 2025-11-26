--------------------------- MODULE E0_hist ---------------------------


CONSTANTS Key, Value, Node

VARIABLES Fluent9_12, Fluent25_14, transfer_msg, Fluent10_12, Fluent24_14

vars == <<Fluent9_12, Fluent25_14, transfer_msg, Fluent10_12, Fluent24_14>>

CandSep ==
/\ \A var0 \in Value : \A var1 \in Node : \A var2 \in Key : (Fluent24_14[var1][var0][var2]) => (Fluent25_14[var1][var0][var2])
/\ \A var0 \in Value : \A var1 \in Key : \A var2 \in Node : (Fluent10_12[var1][var0][var2]) => (~(Fluent9_12[var1][var0][var2]))

Nil == "nil"

Reshard(k,v,n_old,n_new) ==
/\ transfer_msg' = (transfer_msg \cup {<<n_new,k,v>>})
/\ Fluent25_14' = [Fluent25_14 EXCEPT ![n_new][v][k] = TRUE]
/\ Fluent10_12' = [Fluent10_12 EXCEPT ![k][v][n_new] = FALSE]
/\ UNCHANGED<<Fluent9_12, Fluent24_14>>

RecvTransferMsg(n,k,v) ==
/\ (<<n,k,v>> \in transfer_msg)
/\ transfer_msg' = (transfer_msg \ {<<n,k,v>>})
/\ Fluent9_12' = [Fluent9_12 EXCEPT ![k][v][n] = Fluent10_12[k][v][n]]
/\ Fluent10_12' = [Fluent10_12 EXCEPT ![k][v][n] = TRUE]
/\ Fluent24_14' = [Fluent24_14 EXCEPT ![n][v][k] = TRUE]
/\ UNCHANGED<<Fluent25_14>>

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))

Init ==
/\ transfer_msg = {}
/\ Fluent25_14 = [ x0 \in Node |-> [ x1 \in Value |-> [ x2 \in Key |-> FALSE]]]
/\ Fluent9_12 = [ x0 \in Key |-> [ x1 \in Value |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent10_12 = [ x0 \in Key |-> [ x1 \in Value |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent24_14 = [ x0 \in Node |-> [ x1 \in Value |-> [ x2 \in Key |-> FALSE]]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (transfer_msg \in SUBSET((Node \X Key \X Value)))
=============================================================================
