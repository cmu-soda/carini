---- MODULE C1 ----
EXTENDS TLC, Randomization

CONSTANTS Key, Node, Value, Seqnum

VARIABLES table, owner, ctr1, ctr2

vars == <<table, owner, ctr1, ctr2>>

CandSep == \A n \in Node : \A m \in Node : \A k \in Key : \A v \in Value : \A s \in Seqnum : ~ctr2[n][m][k][v][s]


Init ==
    /\ table = [n \in Node |-> [k \in Key |-> [v \in Value |-> FALSE]]]
    /\ owner \in [Node -> [Key -> BOOLEAN]]
    /\ \A N1,N2 \in Node : \A K \in Key : (owner[N1][K] /\ owner[N2][K]) => (N1 = N2)
    /\ ctr1 = [n \in Node |-> [m \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> TRUE]]]]]
    /\ ctr2 = [n \in Node |-> [m \in Node |-> [k \in Key |-> [v \in Value |-> [s \in Seqnum |-> FALSE]]]]]

reshard(n_old, n_new, k, v, s) ==
  /\ table[n_old][k][v]
  /\ table' = [table EXCEPT![n_old][k][v] = FALSE]
  /\ owner' = [owner EXCEPT![n_old][k] = FALSE]
  /\ ctr1' = [ctr1 EXCEPT![n_old][n_new][k][v][s] = FALSE]
  /\ ctr2' = [ctr2 EXCEPT![n_old][n_new][k][v][s] = FALSE]
  /\ CandSep'

recv_transfer_msg(src, n, k, v, s) ==
  /\ table' = [table EXCEPT![n][k][v] = TRUE]
  /\ owner' = [owner EXCEPT![n][k] = TRUE]
  /\ ctr1' = [ctr1 EXCEPT![src][n][k][v][s] = TRUE]
  /\ ctr2' = [ctr2 EXCEPT![src][n][k][v][s] = ctr1[src][n][k][v][s]]
  /\ CandSep'

put(n, k, v) ==
  /\ owner[n][k]
  /\ table' = [table EXCEPT![n][k] = [V \in Value |-> (V=v)]]
  /\ UNCHANGED<<owner>>
  /\ UNCHANGED<<ctr1, ctr2>>
  /\ CandSep'

Next ==
    \E n,m \in Node : \E k \in Key : \E v \in Value : \E s \in Seqnum :
        \/ reshard(n, m, k, v, s)
        \/ recv_transfer_msg(n, m, k, v, s)
        \/ put(n, k, v)

Spec == Init /\ [][Next]_vars

\*safety [keys_unique] table(N1, K, V1) & table(N2, K, V2) -> N1 = N2 & V1 = V2
Safety ==
    \A N1,N2 \in Node : \A K \in Key : \A V1,V2 \in Value :
        (table[N1][K][V1] /\ table[N2][K][V2]) => (N1 = N2 /\ V1 = V2)

TypeOK ==
    /\ table \in [Node -> [Key -> [Value -> BOOLEAN]]]
    /\ owner \in [Node -> [Key -> BOOLEAN]]
    /\ ctr1 \in [Node -> [Node -> [Key -> [Value -> [Seqnum -> BOOLEAN]]]]]
    /\ ctr2 \in [Node -> [Node -> [Key -> [Value -> [Seqnum -> BOOLEAN]]]]]

Num == 40
TypeOKRand ==
    /\ table \in RandomSubset(Num, [Node -> [Key -> [Value -> BOOLEAN]]])
    /\ owner \in RandomSubset(Num, [Node -> [Key -> BOOLEAN]])
    /\ ctr1 \in RandomSubset(Num, [Node -> [Node -> [Key -> [Value -> [Seqnum -> BOOLEAN]]]]])
    /\ ctr2 \in RandomSubset(Num, [Node -> [Node -> [Key -> [Value -> [Seqnum -> BOOLEAN]]]]])

\* Automatically inferred by PDH
\* predicates[  0] (1) (1) (implied by human invariant): forall N1:node, K:key, V1:value, N2:node, V2:value. !table(N1, K, V1) | !table(N2, K, V2) | N1 = N2
Inv1 == \A N1 \in Node, K \in Key, V1 \in Value, N2\in Node, V2 \in Value : ~table[N1][K][V1] \/ ~table[N2][K][V2] \/ N1 = N2

\* predicates[  1] (1) (1) (implied by human invariant): forall N1:node, K:key, V1:value, N2:node, V2:value. !table(N1, K, V1) | !table(N2, K, V2) | V1 = V2
Inv2 == \A N1 \in Node, K \in Key, V1 \in Value, N2 \in Node, V2 \in Value : ~table[N1][K][V1] \/ ~table[N2][K][V2] \/ V1 = V2

\* predicates[  4] (1) (2): forall key_0:key, node_0:node, value_0:value, value_1:value. owner(node_0, key_0) | table(node_0, key_0, value_0) | !table(node_0, key_0, value_1)
Inv3 == \A key_0 \in Key, node_0 \in Node, value_0 \in Value, value_1 \in Value :
    owner[node_0][key_0] \/ table[node_0][key_0][value_0] \/ ~table[node_0][key_0][value_1]

\* predicates[  8] (invariant): forall key_0:key, node_1:node, seqnum_0:seqnum, value_0:value. !ctr2(node_1, node_1, key_0, value_0, seqnum_0)
Inv4 == \A key_0 \in Key, node_1 \in Node, seqnum_0 \in Seqnum, value_0 \in Value : ~ctr2[node_1][node_1][key_0][value_0][seqnum_0]

\* predicates[ 11] (1) (1): forall key_0:key, node_0:node, node_1:node. node_0 = node_1 | !owner(node_0, key_0) | !owner(node_1, key_0)
Inv5 == \A key_0 \in Key, node_0 \in Node, node_1 \in Node : node_0 = node_1 \/ ~owner[node_0][key_0] \/ ~owner[node_1][key_0]

\* predicates[ 12] (1) (1): forall key_0:key, node_1:node, node_2:node, seqnum_0:seqnum, value_0:value. ctr1(node_2, node_1, key_0, value_0, seqnum_0) | !owner(node_1, key_0) | owner(node_2, key_0)
Inv6 == \A key_0 \in Key, node_1 \in Node, node_2 \in Node, seqnum_0 \in Seqnum, value_0 \in Value :
    ctr1[node_2][node_1][key_0][value_0][seqnum_0] \/ ~owner[node_1][key_0] \/ owner[node_2][key_0]

\* predicates[ 13] (1) (2): forall key_0:key, node_0:node, node_1:node, seqnum_0:seqnum, value_0:value. !ctr1(node_1, node_0, key_0, value_0, seqnum_0) | owner(node_0, key_0) | !table(node_0, key_0, value_0)
Inv7 == \A key_0 \in Key, node_0 \in Node, node_1 \in Node, seqnum_0 \in Seqnum, value_0 \in Value :
    ~ctr1[node_1][node_0][key_0][value_0][seqnum_0] \/ owner[node_0][key_0] \/ ~table[node_0][key_0][value_0]

\* predicates[ 14] (1) (1): forall key0:key, node0:node, node1:node, seqnum0:seqnum, value0:value. node0 = node1 | ctr1(node1, node0, key0, value0, seqnum0) | !table(node0, key0, value0)
Inv8 == \A key0 \in Key, node0 \in Node, node1 \in Node, seqnum0 \in Seqnum, value0 \in Value :
    node0 = node1 \/ ctr1[node1][node0][key0][value0][seqnum0] \/ ~table[node0][key0][value0]

\* human_invariant[  0](learned as predicates[0]): forall N1:node, K:key, V1:value, N2:node, V2:value. !table(N1, K, V1) | !table(N2, K, V2) | N1 = N2
Inv9 == \A N1 \in Node, K \in Key, V1 \in Value, N2 \in Node, V2 \in Value : ~table[N1][K][V1] \/ ~table[N2][K][V2] \/ N1 = N2

\* human_invariant[  1](learned as predicates[1]): forall N1:node, K:key, V1:value, N2:node, V2:value. !table(N1, K, V1) | !table(N2, K, V2) | V1 = V2
Inv10 == \A N1 \in Node, K \in Key, V1 \in Value, N2 \in Node, V2 \in Value : ~table[N1][K][V1] \/ ~table[N2][K][V2] \/ V1 = V2

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

IISpec == TypeOK /\ IndInv /\ [][Next]_vars

======
