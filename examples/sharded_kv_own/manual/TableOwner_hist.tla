--------------------------- MODULE TableOwner_hist ---------------------------


CONSTANTS Key, Value, Node

VARIABLES owner, Fluent7_69, Fluent8_69, Fluent4_6, Fluent3_6, Fluent2_56, Fluent1_56, Fluent6_69, table, ownk, rcvMsg

vars == <<owner, Fluent7_69, Fluent8_69, Fluent4_6, Fluent3_6, Fluent2_56, Fluent1_56, Fluent6_69, table, ownk, rcvMsg>>

CandSep ==
/\ \A var0 \in Key : (Fluent8_69[var0]) => ((Fluent6_69[var0]) => (Fluent7_69[var0]))
/\ \A var0 \in Node : (Fluent4_6[var0]) => (Fluent3_6[var0])
/\ \A var0 \in Value : (Fluent2_56[var0]) => (Fluent1_56[var0])
\*/\ \A n \in Node : \A k \in Key : rcvMsg[n][k] => ownk[n][k]

Nil == "nil"

Reshard(k,v,n_old,n_new) ==
/\ table[n_old][k] = v
/\ table' = [table EXCEPT![n_old][k] = Nil]
/\ owner' = [owner EXCEPT![n_old] = (owner[n_old] \ {k})]
/\ Fluent8_69' = [Fluent8_69 EXCEPT ![k] = TRUE]
/\ Fluent3_6' = [Fluent3_6 EXCEPT ![n_new] = TRUE]
/\ Fluent1_56' = [Fluent1_56 EXCEPT ![v] = TRUE]
/\ Fluent6_69' = [x0 \in Key |-> FALSE]
/\ UNCHANGED<<Fluent7_69, Fluent4_6, Fluent2_56>>
/\ ownk' = [[ownk EXCEPT![n_old][k] = FALSE] EXCEPT![n_new][k] = TRUE]
/\ rcvMsg' = [[rcvMsg EXCEPT![n_old][k] = FALSE] EXCEPT![n_new][k] = FALSE]
/\ CandSep'

RecvTransferMsg(n,k,v) ==
/\ table' = [table EXCEPT![n][k] = v]
/\ owner' = [owner EXCEPT![n] = (owner[n] \cup {k})]
/\ Fluent7_69' = [Fluent7_69 EXCEPT ![k] = TRUE]
/\ Fluent4_6' = [Fluent4_6 EXCEPT ![n] = TRUE]
/\ Fluent2_56' = [Fluent2_56 EXCEPT ![v] = TRUE]
/\ UNCHANGED<<Fluent8_69, Fluent3_6, Fluent1_56, Fluent6_69>>
/\ rcvMsg' = [rcvMsg EXCEPT![n][k] = TRUE]
/\ UNCHANGED<<ownk>>
/\ CandSep'

Put(n,k,v) ==
/\ (k \in owner[n])
/\ table' = [table EXCEPT![n][k] = v]
/\ UNCHANGED <<owner>>
/\ UNCHANGED<<Fluent7_69, Fluent8_69, Fluent4_6, Fluent3_6, Fluent2_56, Fluent1_56, Fluent6_69>>
/\ UNCHANGED<<rcvMsg,ownk>>
/\ CandSep'

Own(n,k) ==
/\ (\A n2 \in Node : (k \notin owner[n2]))
/\ owner' = [owner EXCEPT![n] = (owner[n] \cup {k})]
/\ UNCHANGED <<table>>
/\ Fluent6_69' = [Fluent6_69 EXCEPT ![k] = TRUE]
/\ UNCHANGED<<Fluent7_69, Fluent8_69, Fluent4_6, Fluent3_6, Fluent2_56, Fluent1_56>>
/\ UNCHANGED<<rcvMsg,ownk>> \* could add ownk, but unneeded
/\ CandSep'

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))
\/ (\E n \in Node, k \in Key, v \in Value : Put(n,k,v))
\/ (\E n \in Node, k \in Key : Own(n,k))

Init ==
/\ table = [n \in Node |-> [k \in Key |-> Nil]]
/\ owner = [n \in Node |-> {}]
/\ Fluent7_69 = [ x0 \in Key |-> FALSE]
/\ Fluent8_69 = [ x0 \in Key |-> FALSE]
/\ Fluent4_6 = [ x0 \in Node |-> FALSE]
/\ Fluent3_6 = [ x0 \in Node |-> FALSE]
/\ Fluent2_56 = [ x0 \in Value |-> FALSE]
/\ Fluent1_56 = [ x0 \in Value |-> FALSE]
/\ Fluent6_69 = [ x0 \in Key |-> FALSE]
/\ ownk = [x0 \in Node |-> [x1 \in Key |-> FALSE]]
/\ rcvMsg = [x0 \in Node |-> [x1 \in Key |-> FALSE]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (table \in [Node -> [Key -> (Value \cup {Nil})]])
/\ (owner \in [Node -> SUBSET(Key)])

Safety == (\A n1,n2 \in Node, k \in Key, v1,v2 \in Value : ((table[n1][k] = v1 /\ table[n2][k] = v2) => (n1 = n2 /\ v1 = v2)))
=============================================================================
