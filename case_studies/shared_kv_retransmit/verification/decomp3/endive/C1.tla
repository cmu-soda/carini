---- MODULE C1 ----
EXTENDS TLC, Randomization

CONSTANTS Key, Node, Value, Seqnum

VARIABLES table, owner, ctr1, ctr2

vars == <<table, owner, ctr1, ctr2>>

NextUnchanged == UNCHANGED vars
Symmetry == Permutations(Key) \cup Permutations(Node) \cupPermutations(Value)

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

\*invariant owner(N1, K) & owner(N2, K) -> N1 = N2
Inv1 == \A N1,N2 \in Node : \A K \in Key : (owner[N1][K] /\ owner[N2][K]) => (N1 = N2)

\*invariant table(N, K, V) -> owner(N, K)
Inv2 == \A N \in Node : \A K \in Key : \A V \in Value : table[N][K][V] => owner[N][K]

Inv ==
    /\ TypeOK
    /\ Safety
    /\ Inv1
    /\ Inv2

IISpec == TypeOK /\ Inv /\ [][Next]_vars

======
