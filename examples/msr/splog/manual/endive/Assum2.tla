--------------------------- MODULE Assum2 ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, Randomization

\*CONSTANTS Server, Quorums, FinNat

CONSTANTS Server, FinNat
Quorums == {S \in SUBSET Server : 2*Cardinality(S) > Cardinality(Server)}

VARIABLES BecLeaderTerm, LeaderTerm, ClReq, ActiveTerm, CommitTerm, CommitQuorum, ActiveQuorum

vars == <<BecLeaderTerm, LeaderTerm, ClReq, ActiveTerm, CommitTerm, CommitQuorum, ActiveQuorum>>

Symmetry == Permutations(Server)
NextUnchanged == UNCHANGED vars

CandSep ==
/\ \A var0 \in FinNat : \E var1 \in Server : \A var2 \in Server : (BecLeaderTerm[var2][var0]) => (var2 = var1)
/\ \A var0 \in Quorums : \A var1 \in Quorums : CommitQuorum[var0] => (ActiveQuorum[var1] => (var0 \cap var1 # {}))
/\ \A var0 \in FinNat : CommitTerm[var0] => ActiveTerm[var0]
/\ \A var0 \in FinNat : \A var1 \in FinNat : ActiveTerm[var0] => (LeaderTerm[var1] => (var1 <= var0))
/\ \A var0 \in Server : \A var1 \in FinNat : ClReq[var0][var1] => BecLeaderTerm[var0][var1]


FalseQuorums == [q \in Quorums |-> FALSE]

ClientRequest(i,curTerm) ==
/\ ClReq' = [ClReq EXCEPT ![i][curTerm] = TRUE]
/\ UNCHANGED<<BecLeaderTerm, LeaderTerm, ActiveTerm, CommitTerm, CommitQuorum, ActiveQuorum>>

GetEntries(i,j) ==
/\ ClReq' = [ClReq EXCEPT ![i] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ BecLeaderTerm' = [BecLeaderTerm EXCEPT ![i] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ UNCHANGED<<LeaderTerm, ActiveTerm, CommitTerm, CommitQuorum, ActiveQuorum>>

RollbackEntries(i,j) ==
/\ ClReq' = [ClReq EXCEPT ![i] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ BecLeaderTerm' = [BecLeaderTerm EXCEPT ![i] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ UNCHANGED<<LeaderTerm, ActiveTerm, CommitTerm, CommitQuorum, ActiveQuorum>>

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ ClReq' = [s \in Server |-> IF (s \in voteQuorum) THEN [x1 \in FinNat |-> FALSE] ELSE ClReq[s]] \* specialized fluent
/\ BecLeaderTerm' = [[s \in Server |-> IF (s \in voteQuorum) THEN [x1 \in FinNat |-> FALSE] ELSE BecLeaderTerm[s]] EXCEPT![i][newTerm] = TRUE] \* specialized fluent
/\ ActiveQuorum' = [[q \in Quorums |-> FALSE] EXCEPT ![voteQuorum] = TRUE]
/\ CommitQuorum' = FalseQuorums \* for some reason Endive needs this \*[q \in Quorums |-> FALSE]
/\ ActiveTerm' = [[x \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ CommitTerm' = [x \in FinNat |-> FALSE]
/\ LeaderTerm' = [LeaderTerm EXCEPT ![newTerm] = TRUE]

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ ind > 0
/\ CommitQuorum' = [CommitQuorum EXCEPT ![commitQuorum] = TRUE]
/\ CommitTerm' = [CommitTerm EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<BecLeaderTerm, LeaderTerm, ClReq, ActiveTerm, ActiveQuorum>>

Init ==
/\ BecLeaderTerm = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ LeaderTerm = [ x0 \in FinNat |-> FALSE]
/\ ClReq = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ ActiveQuorum = [ q \in Quorums |-> FALSE]
/\ CommitQuorum = [ q \in Quorums |-> FALSE]
/\ ActiveTerm = [x \in FinNat |-> FALSE]
/\ CommitTerm = [x \in FinNat |-> FALSE]

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s,t \in Server : GetEntries(s,t))
\/ (\E s,t \in Server : RollbackEntries(s,t))
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)))))

Spec == (Init /\ [][Next]_vars)


TypeOK ==
/\ BecLeaderTerm \in [Server -> [FinNat -> BOOLEAN]]
/\ LeaderTerm \in [FinNat -> BOOLEAN]
/\ ClReq \in [Server -> [FinNat -> BOOLEAN]]
/\ ActiveQuorum \in [Quorums -> BOOLEAN]
/\ CommitQuorum \in [Quorums -> BOOLEAN]
/\ ActiveTerm \in [FinNat -> BOOLEAN]
/\ CommitTerm \in [FinNat -> BOOLEAN]

rnum == 17
TypeOKRand ==
/\ BecLeaderTerm \in RandomSubset(rnum, [Server -> [FinNat -> BOOLEAN]])
/\ LeaderTerm \in RandomSubset(rnum, [FinNat -> BOOLEAN])
/\ ClReq \in RandomSubset(rnum, [Server -> [FinNat -> BOOLEAN]])
/\ ActiveQuorum \in RandomSubset(rnum, [Quorums -> BOOLEAN])
/\ CommitQuorum \in RandomSubset(rnum, [Quorums -> BOOLEAN])
/\ ActiveTerm \in RandomSubset(rnum, [FinNat -> BOOLEAN])
/\ CommitTerm \in RandomSubset(rnum, [FinNat -> BOOLEAN])

IndInv ==
    /\ TypeOK
    /\ CandSep

IndInvRand == TypeOKRand /\ IndInv

IISpec == IndInvRand /\ [][Next]_vars

=============================================================================
