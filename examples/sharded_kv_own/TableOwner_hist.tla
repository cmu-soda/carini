--------------------------- MODULE TableOwner_hist ---------------------------


CONSTANTS Key, Value, Node

VARIABLES owner, Fluent8_0, Fluent7_0, Fluent4_24, Fluent2_21, Fluent5_24, Fluent1_21, table

vars == <<owner, Fluent8_0, Fluent7_0, Fluent4_24, Fluent2_21, Fluent5_24, Fluent1_21, table>>

CandSep ==
/\ /\ \A var0 \in Node : (Fluent4_24[var0]) => (Fluent5_24[var0])
/\ \A var0 \in Key : (Fluent1_21[var0]) => (Fluent2_21[var0])
/\ UNSAT
/\ \A var0 \in Key : (Fluent7_0[var0]) => (Fluent8_0[var0])

Nil == "nil"

Reshard(k,v,n_old,n_new) ==
/\ table[n_old][k] = v
/\ table' = [table EXCEPT![n_old][k] = Nil]
/\ owner' = [owner EXCEPT![n_old] = (owner[n_old] \ {k})]
/\ Fluent8_0' = [Fluent8_0 EXCEPT ![k] = TRUE]
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![k] = TRUE]
/\ Fluent2_21' = [Fluent2_21 EXCEPT ![k] = TRUE]
/\ Fluent5_24' = [Fluent5_24 EXCEPT ![n_new] = TRUE]
/\ UNCHANGED<<Fluent4_24, Fluent1_21>>
/\ CandSep'

RecvTransferMsg(n,k,v) ==
/\ table' = [table EXCEPT![n][k] = v]
/\ owner' = [owner EXCEPT![n] = (owner[n] \cup {k})]
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![k] = FALSE]
/\ Fluent4_24' = [Fluent4_24 EXCEPT ![n] = TRUE]
/\ Fluent1_21' = [Fluent1_21 EXCEPT ![k] = TRUE]
/\ UNCHANGED<<Fluent8_0, Fluent2_21, Fluent5_24>>
/\ CandSep'

Put(n,k,v) ==
/\ (k \in owner[n])
/\ table' = [table EXCEPT![n][k] = v]
/\ UNCHANGED <<owner>>
/\ UNCHANGED<<Fluent8_0, Fluent7_0, Fluent4_24, Fluent2_21, Fluent5_24, Fluent1_21>>
/\ CandSep'

Own(n,k) ==
/\ (\A n2 \in Node : (k \notin owner[n2]))
/\ owner' = [owner EXCEPT![n] = (owner[n] \cup {k})]
/\ UNCHANGED <<table>>
/\ Fluent8_0' = [Fluent8_0 EXCEPT ![k] = FALSE]
/\ UNCHANGED<<Fluent7_0, Fluent4_24, Fluent2_21, Fluent5_24, Fluent1_21>>
/\ CandSep'

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))
\/ (\E n \in Node, k \in Key, v \in Value : Put(n,k,v))
\/ (\E n \in Node, k \in Key : Own(n,k))

Init ==
/\ table = [n \in Node |-> [k \in Key |-> Nil]]
/\ owner = [n \in Node |-> {}]
/\ Fluent8_0 = [ x0 \in Key |-> FALSE]
/\ Fluent7_0 = [ x0 \in Key |-> FALSE]
/\ Fluent4_24 = [ x0 \in Node |-> FALSE]
/\ Fluent2_21 = [ x0 \in Key |-> FALSE]
/\ Fluent5_24 = [ x0 \in Node |-> FALSE]
/\ Fluent1_21 = [ x0 \in Key |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (table \in [Node -> [Key -> (Value \cup {Nil})]])
/\ (owner \in [Node -> SUBSET(Key)])

Safety == (\A n1,n2 \in Node, k \in Key, v1,v2 \in Value : ((table[n1][k] = v1 /\ table[n2][k] = v2) => (n1 = n2 /\ v1 = v2)))
=============================================================================
