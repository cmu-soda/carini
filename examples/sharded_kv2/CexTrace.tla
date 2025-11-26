--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS N1, N2, K1, K2, Node, Value, V1, V2, Key

VARIABLES owner, err, Fluent17_6, Fluent18_6, table, cexTraceIdx

vars == <<owner, err, Fluent17_6, Fluent18_6, table, cexTraceIdx>>

NoErr == err = FALSE

CandSep == (\A var0 \in Node : (\A var1 \in Value : (Fluent17_6[var0][var1] => Fluent18_6[var0][var1])))

Nil == "nil"

Reshard(k,v,n_old,n_new) ==
/\ table[n_old][k] = v
/\ table' = [table EXCEPT![n_old][k] = Nil]
/\ owner' = [owner EXCEPT![n_old] = (owner[n_old] \ {k})]
/\ Fluent18_6' = [Fluent18_6 EXCEPT![n_new][v] = TRUE]
/\ UNCHANGED <<Fluent17_6>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

RecvTransferMsg(n,k,v) ==
/\ table' = [table EXCEPT![n][k] = v]
/\ owner' = [owner EXCEPT![n] = (owner[n] \cup {k})]
/\ Fluent17_6' = [Fluent17_6 EXCEPT![n][v] = TRUE]
/\ UNCHANGED <<Fluent18_6>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

Put(n,k,v) ==
/\ (k \in owner[n])
/\ table' = [table EXCEPT![n][k] = v]
/\ UNCHANGED <<owner>>
/\ UNCHANGED <<Fluent17_6,Fluent18_6>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))
\/ (\E n \in Node, k \in Key, v \in Value : Put(n,k,v))

Init ==
/\ table = [n \in Node |-> [k \in Key |-> Nil]]
/\ (owner \in [Node -> SUBSET(Key)])
/\ (\A i,j \in Node : (\A k \in Key : (((k \in owner[i]) /\ (k \in owner[j])) => i = j)))
/\ Fluent17_6 = [x0 \in Node |-> [x1 \in Value |-> FALSE]]
/\ Fluent18_6 = [x0 \in Node |-> [x1 \in Value |-> FALSE]]
/\ cexTraceIdx = 0
/\ err = FALSE

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (table \in [Node -> [Key -> (Value \cup {Nil})]])
/\ (owner \in [Node -> SUBSET(Key)])

Safety == (\A n1,n2 \in Node, k \in Key, v1,v2 \in Value : ((table[n1][k] = v1 /\ table[n2][k] = v2) => (n1 = n2 /\ v1 = v2)))

TraceConstraint ==
/\ cexTraceIdx = 0 => Put(N1,K1,V1) /\ err' = err
/\ cexTraceIdx = 1 => Reshard(K1,V1,N1,N1) /\ err' = err
/\ cexTraceIdx = 2 => RecvTransferMsg(N1,K1,V1) /\ err' = err
/\ cexTraceIdx = 3 => Put(N1,K1,V2) /\ err' = err
/\ cexTraceIdx = 4 => Reshard(K1,V2,N1,N2) /\ err' = err
/\ cexTraceIdx = 5 => RecvTransferMsg(N2,K1,V2) /\ err' = err
/\ cexTraceIdx = 6 => Put(N2,K2,V2) /\ err' = err
/\ cexTraceIdx = 7 => Reshard(K2,V2,N2,N1) /\ err' = err
/\ cexTraceIdx = 8 => RecvTransferMsg(N1,K1,V2) /\ err' = TRUE
/\ cexTraceIdx >= 9 => FALSE

InternalAction == UNCHANGED<<cexTraceIdx,err>>

TraceConstraintSpec == Init /\ [][Next /\ (TraceConstraint \/ InternalAction)]_vars
=============================================================================
