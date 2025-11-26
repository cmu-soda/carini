--------------------------- MODULE C2_hist ---------------------------
EXTENDS Naturals, Randomization

CONSTANTS Key, Node, Value, Seqnum

VARIABLES fluent52, fluent51, fluent20, seqnum_sent, fluent95, fluent94, seqnum_recvd, fluent107, transfer_msg, fluent108, fluent19

vars == <<fluent52, fluent51, fluent20, seqnum_sent, fluent95, fluent94, seqnum_recvd, fluent107, transfer_msg, fluent108, fluent19>>

CandSep ==
/\ \A var0 \in Seqnum : \A var1 \in Node : \A var2 \in Key : (fluent94[var1][var2][var0]) => (fluent95[var1][var2][var0])
/\ \A var0 \in Seqnum : \A var1 \in Node : \A var2 \in Node : (fluent108[var0][var1][var2]) => (fluent107[var0][var1][var2])

Init ==
/\ transfer_msg = [n \in Node |-> [nn \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]
/\ seqnum_sent = [n \in Node |-> [s \in Seqnum |-> FALSE]]
/\ seqnum_recvd = [n \in Node |-> [nn \in Node |-> [s \in Seqnum |-> FALSE]]]
/\ fluent95 = [ x0 \in Node |-> [ x1 \in Key |-> [ x2 \in Seqnum |-> FALSE]]]
/\ fluent94 = [ x0 \in Node |-> [ x1 \in Key |-> [ x2 \in Seqnum |-> FALSE]]]
/\ fluent107 = [ x0 \in Seqnum |-> [ x1 \in Node |-> [ x2 \in Node |-> FALSE]]]
/\ fluent108 = [ x0 \in Seqnum |-> [ x1 \in Node |-> [ x2 \in Node |-> FALSE]]]
/\ fluent52 = [ x0 \in Seqnum |-> [ x1 \in Node |-> [ x2 \in Key |-> FALSE]]]
/\ fluent51 = [ x0 \in Seqnum |-> [ x1 \in Node |-> [ x2 \in Key |-> FALSE]]]
/\ fluent20 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]
/\ fluent19 = [ x0 \in Seqnum |-> [ x1 \in Node |-> FALSE]]

reshard(n_old,n_new,k,v,s) ==
/\ ~(seqnum_sent[n_old][s])
/\ seqnum_sent' = [seqnum_sent EXCEPT![n_old][s] = TRUE]
/\ transfer_msg' = [transfer_msg EXCEPT![n_old][n_new][k][v][s] = TRUE]
/\ UNCHANGED <<seqnum_recvd>>
/\ fluent95' = [fluent95 EXCEPT ![n_old][k][s] = TRUE]
/\ fluent107' = [fluent107 EXCEPT ![s][n_new][n_old] = TRUE]
/\ UNCHANGED<<fluent94, fluent108>>
/\ fluent52' = [fluent52 EXCEPT ![s][n_old][k] = TRUE]
/\ UNCHANGED<<fluent51, fluent20, fluent19>>
\*/\ CandSep'

drop_transfer_msg(src,dst,k,v,s) ==
/\ transfer_msg[src][dst][k][v][s]
/\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = FALSE]
/\ UNCHANGED <<seqnum_sent,seqnum_recvd>>
/\ UNCHANGED<<fluent95, fluent94, fluent107, fluent108>>
/\ UNCHANGED<<fluent52, fluent51, fluent20, fluent19>>
/\ CandSep'

retransmit(src,dst,k,v,s) ==
/\ transfer_msg' = [transfer_msg EXCEPT![src][dst][k][v][s] = TRUE]
/\ UNCHANGED <<seqnum_sent,seqnum_recvd>>
/\ fluent94' = [fluent94 EXCEPT ![src][k][s] = TRUE]
/\ fluent108' = [fluent108 EXCEPT ![s][dst][src] = TRUE]
/\ UNCHANGED<<fluent95, fluent107>>
/\ UNCHANGED<<fluent52, fluent51, fluent20, fluent19>>
/\ CandSep'
\*/\ fluent95[src][k][s] = TRUE
\*/\ fluent107[s][dst][src] = TRUE

recv_transfer_msg(src,n,k,v,s) ==
/\ transfer_msg[src][n][k][v][s]
/\ ~(seqnum_recvd[n][src][s])
/\ seqnum_recvd' = [seqnum_recvd EXCEPT![n][src][s] = TRUE]
/\ UNCHANGED <<transfer_msg,seqnum_sent>>
/\ UNCHANGED<<fluent95, fluent94, fluent107, fluent108>>
/\ fluent51' = [fluent51 EXCEPT ![s][src][k] = TRUE]
/\ fluent20' = [fluent20 EXCEPT ![s][src] = TRUE]
/\ fluent19' = [fluent19 EXCEPT ![s][src] = fluent20[s][src]]
/\ UNCHANGED<<fluent52>>
/\ CandSep'

send_ack(src,n,k,v,s) ==
/\ transfer_msg[src][n][k][v][s]
/\ seqnum_recvd[n][src][s]
/\ UNCHANGED <<transfer_msg,seqnum_sent,seqnum_recvd>>
/\ UNCHANGED<<fluent95, fluent94, fluent107, fluent108>>
/\ UNCHANGED<<fluent52, fluent51, fluent20, fluent19>>
/\ CandSep'

Next ==
\E n,m \in Node :
\E k \in Key :
\E v \in Value :
\E s \in Seqnum :
\/ reshard(n,m,k,v,s)
\/ drop_transfer_msg(n,m,k,v,s)
\/ retransmit(n,m,k,v,s)
\/ recv_transfer_msg(n,m,k,v,s)
\/ send_ack(n,m,k,v,s)

Spec == (Init /\ [][Next]_vars)

Safety ==
/\ \A var0 \in Seqnum : \A var1 \in Node : (fluent20[var0][var1]) => (~(fluent19[var0][var1]))
/\ \A var0 \in Seqnum : \A var1 \in Key : \A var2 \in Node : (fluent51[var0][var2][var1]) => (fluent52[var0][var2][var1])

TypeOK ==
/\ transfer_msg \in   [Node -> [Node -> [Key -> [Value -> [Seqnum -> BOOLEAN]]]]]
/\ seqnum_sent \in    [Node -> [Seqnum -> BOOLEAN]]
/\ seqnum_recvd \in   [Node -> [Node -> [Seqnum -> BOOLEAN]]]
/\ fluent95 \in       [Node -> [Key -> [Seqnum -> BOOLEAN]]]
/\ fluent94 \in       [Node -> [Key -> [Seqnum -> BOOLEAN]]]
/\ fluent107 \in      [Seqnum -> [Node -> [Node -> BOOLEAN]]]
/\ fluent108 \in      [Seqnum -> [Node -> [Node -> BOOLEAN]]]
/\ fluent52 \in       [Seqnum -> [Node -> [Key -> BOOLEAN]]]
/\ fluent51 \in       [Seqnum -> [Node -> [Key -> BOOLEAN]]]
/\ fluent20 \in       [Seqnum -> [Node -> BOOLEAN]]
/\ fluent19 \in       [Seqnum -> [Node -> BOOLEAN]]

Num == 5
TypeOKRand ==
/\ transfer_msg \in  RandomSubset(Num, [Node -> [Node -> [Key -> [Value -> [Seqnum -> BOOLEAN]]]]])
/\ seqnum_sent \in   RandomSubset(Num, [Node -> [Seqnum -> BOOLEAN]])
/\ seqnum_recvd \in  RandomSubset(Num, [Node -> [Node -> [Seqnum -> BOOLEAN]]])
/\ fluent95 \in      RandomSubset(Num, [Node -> [Key -> [Seqnum -> BOOLEAN]]])
/\ fluent94 \in      RandomSubset(Num, [Node -> [Key -> [Seqnum -> BOOLEAN]]])
/\ fluent107 \in     RandomSubset(Num, [Seqnum -> [Node -> [Node -> BOOLEAN]]])
/\ fluent108 \in     RandomSubset(Num, [Seqnum -> [Node -> [Node -> BOOLEAN]]])
/\ fluent52 \in      RandomSubset(Num, [Seqnum -> [Node -> [Key -> BOOLEAN]]])
/\ fluent51 \in      RandomSubset(Num, [Seqnum -> [Node -> [Key -> BOOLEAN]]])
/\ fluent20 \in      RandomSubset(Num, [Seqnum -> [Node -> BOOLEAN]])
/\ fluent19 \in      RandomSubset(Num, [Seqnum -> [Node -> BOOLEAN]])

Inv1 == ~(\E key1 \in Key, node0 \in Node, seqnum0 \in Seqnum : fluent52[seqnum0][node0][key1] /\ ~fluent95[node0][key1][seqnum0])
Inv2 == ~(\E key1 \in Key, node0 \in Node, node1 \in Node, seqnum0 \in Seqnum, value0 \in Value : ~fluent107[seqnum0][node1][node0] /\ transfer_msg[node0][node1][key1][value0][seqnum0])
Inv3 == ~(\E node1 \in Node, node2 \in Node, seqnum0 \in Seqnum : fluent107[seqnum0][node2][node1] /\ ~seqnum_sent[node1][seqnum0])
Inv4 == ~(\E node1 \in Node, seqnum0 \in Seqnum : fluent20[seqnum0][node1] /\ ~seqnum_sent[node1][seqnum0])
Inv5 == ~(\E node0 \in Node, node1 \in Node, node2 \in Node, seqnum0 \in Seqnum : node0 /= node2 /\ fluent107[seqnum0][node0][node1] /\ fluent107[seqnum0][node2][node1])
Inv6 == ~(\E node0 \in Node, node1 \in Node, seqnum0 \in Seqnum : fluent107[seqnum0][node1][node0] /\ fluent20[seqnum0][node0] /\ ~seqnum_recvd[node1][node0][seqnum0])
Inv7 == ~(\E key0 \in Key, node0 \in Node, seqnum0 \in Seqnum : ~fluent52[seqnum0][node0][key0] /\ fluent95[node0][key0][seqnum0])
Inv8 == ~(\E key0 \in Key, node0 \in Node, node1 \in Node, seqnum0 \in Seqnum, value0 \in Value : ~fluent52[seqnum0][node0][key0] /\ transfer_msg[node0][node1][key0][value0][seqnum0])
Inv9 == ~(\E S \in Seqnum, N \in Node, K \in Key : fluent51[S][N][K] /\ ~fluent52[S][N][K])
Inv10 == \A S \in Seqnum, N \in Node : ~fluent19[S][N]

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
    /\ Inv8
    /\ Inv9
    /\ Inv10

IISpec == TypeOKRand /\ IndInv /\ [][Next]_vars

=============================================================================
