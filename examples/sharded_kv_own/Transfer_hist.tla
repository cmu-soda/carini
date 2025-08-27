--------------------------- MODULE Transfer_hist ---------------------------


CONSTANTS Key, Value, Node

VARIABLES Fluent8_0, Fluent7_0, Fluent4_24, Fluent2_21, Fluent5_24, Fluent1_21, transfer_msg

vars == <<Fluent8_0, Fluent7_0, Fluent4_24, Fluent2_21, Fluent5_24, Fluent1_21, transfer_msg>>

CandSep ==
/\ /\ \A var0 \in Node : (Fluent4_24[var0]) => (Fluent5_24[var0])
/\ \A var0 \in Key : (Fluent1_21[var0]) => (Fluent2_21[var0])
/\ UNSAT
/\ \A var0 \in Key : (Fluent7_0[var0]) => (Fluent8_0[var0])

Nil == "nil"

Reshard(k,v,n_old,n_new) ==
/\ transfer_msg' = (transfer_msg \cup {<<n_new,k,v>>})
/\ Fluent8_0' = [Fluent8_0 EXCEPT ![k] = TRUE]
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![k] = TRUE]
/\ Fluent2_21' = [Fluent2_21 EXCEPT ![k] = TRUE]
/\ Fluent5_24' = [Fluent5_24 EXCEPT ![n_new] = TRUE]
/\ UNCHANGED<<Fluent4_24, Fluent1_21>>

RecvTransferMsg(n,k,v) ==
/\ (<<n,k,v>> \in transfer_msg)
/\ transfer_msg' = (transfer_msg \ {<<n,k,v>>})
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![k] = FALSE]
/\ Fluent4_24' = [Fluent4_24 EXCEPT ![n] = TRUE]
/\ Fluent1_21' = [Fluent1_21 EXCEPT ![k] = TRUE]
/\ UNCHANGED<<Fluent8_0, Fluent2_21, Fluent5_24>>

Own(n,k) ==
/\ (\A n2 \in Node : (\A v2 \in Value : (<<n2,k,v2>> \notin transfer_msg)))
/\ UNCHANGED <<transfer_msg>>
/\ Fluent8_0' = [Fluent8_0 EXCEPT ![k] = FALSE]
/\ UNCHANGED<<Fluent7_0, Fluent4_24, Fluent2_21, Fluent5_24, Fluent1_21>>

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))
\/ (\E n \in Node, k \in Key : Own(n,k))

Init ==
/\ transfer_msg = {}
/\ Fluent8_0 = [ x0 \in Key |-> FALSE]
/\ Fluent7_0 = [ x0 \in Key |-> FALSE]
/\ Fluent4_24 = [ x0 \in Node |-> FALSE]
/\ Fluent2_21 = [ x0 \in Key |-> FALSE]
/\ Fluent5_24 = [ x0 \in Node |-> FALSE]
/\ Fluent1_21 = [ x0 \in Key |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (transfer_msg \in SUBSET((Node \X Key \X Value)))
=============================================================================
