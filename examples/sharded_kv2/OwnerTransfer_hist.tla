--------------------------- MODULE OwnerTransfer_hist ---------------------------


CONSTANTS Key, Value, Node

VARIABLES owner, Fluent9_14, Fluent6_4, Fluent2_8, Fluent5_4, Fluent3_8, transfer_msg, Fluent10_14, Fluent11_14

vars == <<owner, Fluent9_14, Fluent6_4, Fluent2_8, Fluent5_4, Fluent3_8, transfer_msg, Fluent10_14, Fluent11_14>>

CandSep ==
/\ /\ \A var0 \in Key : \E var1 \in Node : (Fluent5_4[var0][var1]) => (Fluent6_4[var0][var1])
/\ \A var0 \in Node : (Fluent3_8[var0]) => (Fluent2_8[var0])
/\ UNSAT
/\ \A var0 \in Node : \A var1 \in Key : (Fluent10_14[var0][var1]) => ((Fluent11_14[var0][var1]) => (Fluent9_14[var0][var1]))

Nil == "nil"

Reshard(k,v,n_old,n_new) ==
/\ owner' = [owner EXCEPT![n_old] = (owner[n_old] \ {k})]
/\ transfer_msg' = (transfer_msg \cup {<<n_new,k,v>>})
/\ Fluent9_14' = [Fluent9_14 EXCEPT ![n_new][k] = TRUE]
/\ Fluent6_4' = [Fluent6_4 EXCEPT ![k][n_new] = TRUE]
/\ Fluent2_8' = [Fluent2_8 EXCEPT ![n_new] = TRUE]
/\ Fluent10_14' = [x0 \in Node |-> [x1 \in Key |-> FALSE]]
/\ Fluent11_14' = [Fluent11_14 EXCEPT ![n_old][k] = TRUE]
/\ UNCHANGED<<Fluent5_4, Fluent3_8>>

RecvTransferMsg(n,k,v) ==
/\ (<<n,k,v>> \in transfer_msg)
/\ transfer_msg' = (transfer_msg \ {<<n,k,v>>})
/\ owner' = [owner EXCEPT![n] = (owner[n] \cup {k})]
/\ Fluent3_8' = [Fluent3_8 EXCEPT ![n] = TRUE]
/\ UNCHANGED<<Fluent9_14, Fluent6_4, Fluent2_8, Fluent5_4, Fluent10_14, Fluent11_14>>

Put(n,k,v) ==
/\ (k \in owner[n])
/\ UNCHANGED <<owner,transfer_msg>>
/\ Fluent5_4' = [Fluent5_4 EXCEPT ![k][n] = TRUE]
/\ Fluent10_14' = [Fluent10_14 EXCEPT ![n][k] = TRUE]
/\ UNCHANGED<<Fluent9_14, Fluent6_4, Fluent2_8, Fluent3_8, Fluent11_14>>

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))
\/ (\E n \in Node, k \in Key, v \in Value : Put(n,k,v))

Init ==
/\ (owner \in [Node -> SUBSET(Key)])
/\ (\A i,j \in Node : (\A k \in Key : (((k \in owner[i]) /\ (k \in owner[j])) => i = j)))
/\ transfer_msg = {}
/\ Fluent9_14 = [ x0 \in Node |-> [ x1 \in Key |-> FALSE]]
/\ Fluent6_4 = [ x0 \in Key |-> [ x1 \in Node |-> FALSE]]
/\ Fluent2_8 = [ x0 \in Node |-> FALSE]
/\ Fluent5_4 = [ x0 \in Key |-> [ x1 \in Node |-> FALSE]]
/\ Fluent3_8 = [ x0 \in Node |-> FALSE]
/\ Fluent10_14 = [ x0 \in Node |-> [ x1 \in Key |-> FALSE]]
/\ Fluent11_14 = [ x0 \in Node |-> [ x1 \in Key |-> FALSE]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (owner \in [Node -> SUBSET(Key)])
/\ (transfer_msg \in SUBSET((Node \X Key \X Value)))
=============================================================================
