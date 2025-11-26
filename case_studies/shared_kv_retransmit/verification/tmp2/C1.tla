---- MODULE C1 ----
EXTENDS Naturals

CONSTANTS Key, Node, Value, Seqnum

VARIABLES table, owner

vars == <<table, owner>>


Init ==
    /\ table = [n \in Node |-> [k \in Key |-> [v \in Value |-> FALSE]]]
    /\ owner \in [Node -> [Key -> BOOLEAN]]
    /\ \A N1,N2 \in Node : \A K \in Key : (owner[N1][K] /\ owner[N2][K]) => (N1 = N2)

reshard(n_old, n_new, k, v, s) ==
  /\ table[n_old][k][v]
  /\ table' = [table EXCEPT![n_old][k][v] = FALSE]
  /\ owner' = [owner EXCEPT![n_old][k] = FALSE]

recv_transfer_msg(src, n, k, v, s) ==
  /\ table' = [table EXCEPT![n][k][v] = TRUE]
  /\ owner' = [owner EXCEPT![n][k] = TRUE]

put(n, k, v) ==
  /\ owner[n][k]
  /\ table' = [table EXCEPT![n][k] = [V \in Value |-> (V=v)]]
  /\ UNCHANGED<<owner>>

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

======
