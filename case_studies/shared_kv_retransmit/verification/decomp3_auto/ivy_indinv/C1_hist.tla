--------------------------- MODULE C1_hist ---------------------------
EXTENDS Naturals

CONSTANTS Key, Node, Value, Seqnum

VARIABLES owner, fluent52, fluent51, fluent20, table, fluent19

vars == <<owner, fluent52, fluent51, fluent20, table, fluent19>>

CandSep ==
/\ \A var0 \in Seqnum : \A var1 \in Node : (fluent20[var0][var1]) => (~(fluent19[var0][var1]))
/\ \A var0 \in Seqnum : \A var1 \in Key : \A var2 \in Node : (fluent51[var0][var2][var1]) => (fluent52[var0][var2][var1])

Init ==
/\ table = [n \in Node |-> [k \in Key |-> [v \in Value |-> FALSE]]]
/\ (owner \in [Node -> [Key -> BOOLEAN]])
/\ (\A N1,N2 \in Node : (\A K \in Key : ((owner[N1][K] /\ owner[N2][K]) => N1 = N2)))
/\ fluent52 = [ x0 \in Seqnum |-> [ x1 \in Node |-> [ x2 \in Key |-> FALSE]]]
/\ fluent51 = [ x0 \in Seqnum |-> [ x1 \in Node |-> [ x2 \in Key |-> FALSE]]]
/\ fluent20 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]
/\ fluent19 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]

reshard(n_old,n_new,k,v,s) ==
/\ table[n_old][k][v]
/\ table' = [table EXCEPT![n_old][k][v] = FALSE]
/\ owner' = [owner EXCEPT![n_old][k] = FALSE]
/\ fluent52' = [fluent52 EXCEPT ![s][n_old][k] = TRUE]
/\ UNCHANGED<<fluent51, fluent20, fluent19>>
/\ CandSep'

recv_transfer_msg(src,n,k,v,s) ==
/\ table' = [table EXCEPT![n][k][v] = TRUE]
/\ owner' = [owner EXCEPT![n][k] = TRUE]
/\ fluent51' = [fluent51 EXCEPT ![s][src][k] = TRUE]
/\ fluent20' = [fluent20 EXCEPT ![s][src] = TRUE]
/\ fluent19' = [fluent19 EXCEPT ![s][src] = fluent20[s][src]]
/\ UNCHANGED<<fluent52>>
/\ CandSep'
\*/\ ~fluent20[s][src] /\ fluent52[s][src][k]

put(n,k,v) ==
/\ owner[n][k]
/\ table' = [table EXCEPT![n][k] = [V \in Value |-> V = v]]
/\ UNCHANGED <<owner>>
/\ UNCHANGED<<fluent52, fluent51, fluent20, fluent19>>
/\ CandSep'

Next ==
\E n,m \in Node :
\E k \in Key :
\E v \in Value :
\E s \in Seqnum :
\/ reshard(n,m,k,v,s)
\/ recv_transfer_msg(n,m,k,v,s)
\/ put(n,k,v)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ table \in [Node -> [Key -> [Value -> BOOLEAN]]]
/\ owner \in [Node -> [Key -> BOOLEAN]]
/\ fluent52 \in [Seqnum -> [Node -> [Key -> BOOLEAN]]]
/\ fluent51 \in [Seqnum -> [Node -> [Key -> BOOLEAN]]]
/\ fluent20 \in [Seqnum -> [Node -> BOOLEAN]]
/\ fluent19 \in [Seqnum -> [Node -> BOOLEAN]]

Safety == (\A N1,N2 \in Node : (\A K \in Key : (\A V1,V2 \in Value : ((table[N1][K][V1] /\ table[N2][K][V2]) => (N1 = N2 /\ V1 = V2)))))

Inv1 == \A S \in Seqnum, N \in Node : ~fluent19[S][N]
Inv2 == ~(\E key0 \in Key, node0 \in Node, value0 \in Value : ~owner[node0][key0] /\ table[node0][key0][value0])
Inv3 == ~(\E N1 \in Node, K \in Key, V1 \in Value, N2 \in Node, V2 \in Value : table[N1][K][V1] /\ table[N2][K][V2] /\ V1 /= V2)
Inv4 == \A N1 \in Node, K \in Key, N2 \in Node : owner[N1][K] /\ owner[N2][K] => N1 = N2
Inv5 == ~(\E key0 \in Key, node0 \in Node, node1 \in Node, seqnum0 \in Seqnum, seqnum1 \in Seqnum :
            /\ node0 /= node1
            /\ ~fluent20[seqnum0][node1]
            /\ ~fluent20[seqnum1][node0]
            /\ fluent52[seqnum0][node1][key0]
            /\ fluent52[seqnum1][node0][key0])
Inv6 == ~(\E key0 \in Key, node0 \in Node, seqnum0 \in Seqnum, seqnum1 \in Seqnum :
            /\ seqnum0 /= seqnum1
            /\ ~fluent20[seqnum0][node0]
            /\ ~fluent20[seqnum1][node0]
            /\ fluent52[seqnum0][node0][key0]
            /\ fluent52[seqnum1][node0][key0])
Inv7 == ~(\E key0 \in Key, node0 \in Node, node1 \in Node, seqnum0 \in Seqnum : ~fluent20[seqnum0][node1] /\ fluent52[seqnum0][node1][key0] /\ owner[node0][key0])

IndInv ==
    /\ TypeOK
    /\ Safety
    /\ Inv1
    /\ Inv2
    /\ Inv3
    /\ Inv4
    /\ Inv5
    /\ Inv6
    /\ Inv7

IISpec == IndInv /\ [][Next]_vars

=============================================================================
