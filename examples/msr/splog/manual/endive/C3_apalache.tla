--------------------------- MODULE C3_apalache ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets

\*CONSTANTS Server, Quorums, FinNat

CONSTANTS
    \* @type: Set(Str);
    Server,
    \* @type: Set(Int);
    FinNat

Quorums == {S \in SUBSET Server : 2*Cardinality(S) > Cardinality(Server)}

VARIABLES
    \* @type: (Str -> Int -> Bool);
    BecLeaderTerm,
    \* @type: (Int -> Bool);
    LeaderTerm,
    \* @type: (Str -> Seq(Int));
    log,
    \* @type: (Str -> Int -> Bool);
    ClReq,
    \* @type: (Int -> Bool);
    ActiveTerm,
    \* @type: (Int -> Bool);
    CommitTerm,
    \* @type: (Int -> Int -> Bool);
    Fluent2,
    \* @type: (Set(Str) -> Bool);
    CommitQuorum,
    \* @type: (Set(Str) -> Bool);
    ActiveQuorum

vars == <<BecLeaderTerm, LeaderTerm, log, ClReq, ActiveTerm, CommitTerm, Fluent2, CommitQuorum, ActiveQuorum>>

CandSep ==
/\ \A var0 \in FinNat : \E var1 \in Server : \A var2 \in Server : (BecLeaderTerm[var2][var0]) => (var2 = var1)
/\ \A var0 \in Quorums : \A var1 \in Quorums : CommitQuorum[var0] => (ActiveQuorum[var1] => (var0 \cap var1 # {}))
/\ \A var0 \in FinNat : CommitTerm[var0] => ActiveTerm[var0]
/\ \A var0 \in FinNat : \A var1 \in FinNat : ActiveTerm[var0] => (LeaderTerm[var1] => (var1 <= var0))
/\ \A var0 \in Server : \A var1 \in FinNat : ClReq[var0][var1] => BecLeaderTerm[var0][var1]


FalseQuorums == [q \in Quorums |-> FALSE]

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

Empty(s) == Len(s) = 0

InLog(ind,curTerm,i) ==
\E x \in DOMAIN(log[i]) :
/\ x = ind
/\ log[i][x] = curTerm

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

IsPrefix(s,t) == (Len(s) <= Len(t) /\ SubSeq(s,1,Len(s)) = SubSeq(t,1,Len(s)))

CanRollback(i,j) ==
/\ LastTerm(log[i]) < LastTerm(log[j])
/\ ~(IsPrefix(log[i],log[j]))

CanVoteForOplog(i,j,term) ==
LET logOk == (LastTerm(log[j]) > LastTerm(log[i]) \/ (LastTerm(log[j]) = LastTerm(log[i]) /\ Len(log[j]) >= Len(log[i]))) IN
  /\ logOk

ClientRequest(i,curTerm) ==
/\ log' = [log EXCEPT![i] = Append(log[i],curTerm)]
/\ ClReq' = [ClReq EXCEPT ![i][curTerm] = TRUE]
/\ UNCHANGED<<BecLeaderTerm, LeaderTerm, ActiveTerm, CommitTerm, Fluent2, CommitQuorum, ActiveQuorum>>
/\ CandSep'

GetEntries(i,j) ==
/\ Len(log[j]) > Len(log[i])
/\ LET logOk == IF Empty(log[i]) THEN TRUE ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
  /\ logOk
  /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE (Len(log[i]) + 1)
      newEntry == log[j][newEntryIndex]
      newLog == Append(log[i],newEntry) IN
    /\ log' = [log EXCEPT![i] = newLog]
/\ UNCHANGED<<LeaderTerm, ActiveTerm, CommitTerm, Fluent2, CommitQuorum, ActiveQuorum>>
/\ ClReq' = [ClReq EXCEPT ![i] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ BecLeaderTerm' = [BecLeaderTerm EXCEPT ![i] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ CandSep'

RollbackEntries(i,j) ==
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED<<LeaderTerm, ActiveTerm, CommitTerm, Fluent2, CommitQuorum, ActiveQuorum>>
/\ ClReq' = [ClReq EXCEPT ![i] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ BecLeaderTerm' = [BecLeaderTerm EXCEPT ![i] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ CandSep'

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ UNCHANGED <<log>>
/\ ClReq' = [s \in Server |-> IF (s \in voteQuorum) THEN [x1 \in FinNat |-> FALSE] ELSE ClReq[s]] \* specialized fluent
/\ BecLeaderTerm' = [[s \in Server |-> IF (s \in voteQuorum) THEN [x1 \in FinNat |-> FALSE] ELSE BecLeaderTerm[s]] EXCEPT![i][newTerm] = TRUE] \* specialized fluent
/\ ActiveQuorum' = [[q \in Quorums |-> FALSE] EXCEPT ![voteQuorum] = TRUE]
/\ CommitQuorum' = FalseQuorums \* for some reason Endive needs this \*[q \in Quorums |-> FALSE]
/\ ActiveTerm' = [[x \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ CommitTerm' = [x \in FinNat |-> FALSE]
/\ LeaderTerm' = [LeaderTerm EXCEPT ![newTerm] = TRUE]
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ ind = Len(log[i])
/\ ind > 0
/\ log[i][ind] = curTerm
/\ (\A s \in commitQuorum : (Len(log[s]) >= ind /\ InLog(ind,curTerm,s)))
/\ UNCHANGED <<log>>
/\ CommitQuorum' = [CommitQuorum EXCEPT ![commitQuorum] = TRUE]
/\ CommitTerm' = [CommitTerm EXCEPT ![curTerm] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ UNCHANGED<<BecLeaderTerm, LeaderTerm, ClReq, ActiveTerm, ActiveQuorum>>
/\ CandSep'

Init ==
/\ log = [i \in Server |-> <<>>]
/\ BecLeaderTerm = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ LeaderTerm = [ x0 \in FinNat |-> FALSE]
/\ ClReq = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ ActiveQuorum = [ q \in Quorums |-> FALSE]
/\ CommitQuorum = [ q \in Quorums |-> FALSE]
/\ ActiveTerm = [x \in FinNat |-> FALSE]
/\ CommitTerm = [x \in FinNat |-> FALSE]
/\ Fluent2 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s,t \in Server : GetEntries(s,t))
\/ (\E s,t \in Server : RollbackEntries(s,t))
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)))))

Spec == (Init /\ [][Next]_vars)

Safety ==
/\ \A var0 \in FinNat : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent2[var0][var2]) => (var2 = var1)


FinSeq(S) == UNION {[1..n -> S] : n \in FinNat}
StateConstraint == \A s \in Server : Len(log[s]) <= 3

TypeOK ==
/\ BecLeaderTerm \in [Server -> [FinNat -> BOOLEAN]]
/\ LeaderTerm \in [FinNat -> BOOLEAN]
/\ ClReq \in [Server -> [FinNat -> BOOLEAN]]
/\ ActiveQuorum \in [Quorums -> BOOLEAN]
/\ CommitQuorum \in [Quorums -> BOOLEAN]
/\ ActiveTerm \in [FinNat -> BOOLEAN]
/\ CommitTerm \in [FinNat -> BOOLEAN]
/\ Fluent2 \in [FinNat -> [FinNat -> BOOLEAN]]
\*/\ log \in [Server -> Seq(FinNat)]


Inv2527_1_0 == \A N \in FinNat : \A I \in Server : \A J \in Server : \E F \in FinNat : \E S \in Server : \A M \in FinNat : \A K \in Server : ((N \in DOMAIN log[I]) => (log[I][N] <= M)) \/ (~(Fluent2[N][M]))
Inv7401_1_1 == \A N \in FinNat : \A I \in Server : \A J \in Server : \E F \in FinNat : \E S \in Server : \A M \in FinNat : \A K \in Server : (LeaderTerm[M]) \/ (~(Fluent2[N][M]))
Inv7393_1_2 == \A N \in FinNat : \A I \in Server : \A J \in Server : \E F \in FinNat : \E S \in Server : \A M \in FinNat : \A K \in Server : (LeaderTerm[M]) \/ (~(ClReq[J][M]))
Inv7855_1_3 == \A N \in FinNat : \A I \in Server : \A J \in Server : \E F \in FinNat : \E S \in Server : \A M \in FinNat : \A K \in Server : (M <= Len(log[S])) \/ (~(Fluent2[M][N]))
Inv693_1_4 == \A N \in FinNat : \A I \in Server : \A J \in Server : \E F \in FinNat : \E S \in Server : \A M \in FinNat : \A K \in Server : ((F \in DOMAIN log[I]) => (M <= log[I][F])) \/ (((N \in DOMAIN log[I] /\ M \in DOMAIN log[I]) => (log[I][N] <= log[I][M])))
Inv1383_1_5 == \A N \in FinNat : \A I \in Server : \A J \in Server : \E F \in FinNat : \E S \in Server : \A M \in FinNat : \A K \in Server : ((N \in DOMAIN log[I] /\ F \in DOMAIN log[K]) => (log[I][N] <= log[K][F])) \/ (~((N \in DOMAIN log[I] /\ M \in DOMAIN log[K]) => (log[I][N] <= log[K][M])))

IndEndive ==
    /\ Inv2527_1_0
    /\ Inv7401_1_1
    /\ Inv7393_1_2
    /\ Inv7855_1_3
    /\ Inv693_1_4
    /\ Inv1383_1_5

IndInv ==
    /\ TypeOK
    /\ Safety
    /\ CandSep
    /\ \A n \in Server : \A t \in FinNat : BecLeaderTerm[n][t] => LeaderTerm[t]
    /\ \A n \in Server : \A t \in FinNat : ClReq[n][t] => BecLeaderTerm[n][t]
    /\ \A idx,t \in FinNat : Fluent2[idx][t] => LeaderTerm[t]
    \*/\ \A n \in Server: \A idx,t \in FinNat : (Fluent2[idx][t] /\ CommitTerm[t])  => BecLeaderTerm[n][t]
    \*/\ IndEndive

IISpec == IndInv /\ [][Next]_vars

=============================================================================
