--------------------------- MODULE E0_hist ---------------------------


CONSTANTS Key, Value, Node

VARIABLES Fluent10_18, Fluent24_13, Fluent25_13, transfer_msg, Fluent9_18

vars == <<Fluent10_18, Fluent24_13, Fluent25_13, transfer_msg, Fluent9_18>>

CandSep ==
/\ \A var0 \in Key : \A var1 \in Value : \A var2 \in Node : (Fluent10_18[var2][var1][var0]) => (~(Fluent9_18[var2][var1][var0]))
/\ \A var0 \in Value : \A var1 \in Node : \A var2 \in Key : (Fluent24_13[var2][var0][var1]) => (Fluent25_13[var2][var0][var1])

Nil == "nil"

Reshard(k,v,n_old,n_new) ==
/\ transfer_msg' = (transfer_msg \cup {<<n_new,k,v>>})
/\ Fluent10_18' = [Fluent10_18 EXCEPT ![n_new][v][k] = FALSE]
/\ Fluent25_13' = [Fluent25_13 EXCEPT ![k][v][n_new] = TRUE]
/\ UNCHANGED<<Fluent24_13, Fluent9_18>>

RecvTransferMsg(n,k,v) ==
/\ (<<n,k,v>> \in transfer_msg)
/\ transfer_msg' = (transfer_msg \ {<<n,k,v>>})
/\ Fluent10_18' = [Fluent10_18 EXCEPT ![n][v][k] = TRUE]
/\ Fluent24_13' = [Fluent24_13 EXCEPT ![k][v][n] = TRUE]
/\ Fluent9_18' = [Fluent9_18 EXCEPT ![n][v][k] = Fluent10_18[n][v][k]]
/\ UNCHANGED<<Fluent25_13>>

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))

Init ==
/\ transfer_msg = {}
/\ Fluent10_18 = [ x0 \in Node |-> [ x1 \in Value |-> [ x2 \in Key |-> FALSE]]]
/\ Fluent24_13 = [ x0 \in Key |-> [ x1 \in Value |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent25_13 = [ x0 \in Key |-> [ x1 \in Value |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent9_18 = [ x0 \in Node |-> [ x1 \in Value |-> [ x2 \in Key |-> FALSE]]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (transfer_msg \in SUBSET((Node \X Key \X Value)))
=============================================================================
