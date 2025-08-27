--------------------------- MODULE E0_hist ---------------------------


CONSTANTS Key, Value, Node

VARIABLES Fluent3_7, Fluent2_7, Fluent4_24, Fluent5_24, transfer_msg

vars == <<Fluent3_7, Fluent2_7, Fluent4_24, Fluent5_24, transfer_msg>>

CandSep ==
/\ /\ \A var0 \in Node : (Fluent4_24[var0]) => (Fluent5_24[var0])
/\ \A var0 \in Key : (Fluent3_7[var0]) => (Fluent2_7[var0])
/\ UNSAT

Nil == "nil"

Reshard(k,v,n_old,n_new) ==
/\ transfer_msg' = (transfer_msg \cup {<<n_new,k,v>>})
/\ Fluent5_24' = [Fluent5_24 EXCEPT ![n_new] = TRUE]
/\ Fluent2_7' = [Fluent2_7 EXCEPT ![k] = TRUE]
/\ UNCHANGED<<Fluent4_24, Fluent3_7>>

RecvTransferMsg(n,k,v) ==
/\ (<<n,k,v>> \in transfer_msg)
/\ transfer_msg' = (transfer_msg \ {<<n,k,v>>})
/\ Fluent4_24' = [Fluent4_24 EXCEPT ![n] = TRUE]
/\ Fluent3_7' = [Fluent3_7 EXCEPT ![k] = TRUE]
/\ UNCHANGED<<Fluent5_24, Fluent2_7>>

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))

Init ==
/\ transfer_msg = {}
/\ Fluent4_24 = [ x0 \in Node |-> FALSE]
/\ Fluent5_24 = [ x0 \in Node |-> FALSE]
/\ Fluent3_7 = [ x0 \in Key |-> FALSE]
/\ Fluent2_7 = [ x0 \in Key |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (transfer_msg \in SUBSET((Node \X Key \X Value)))
=============================================================================
