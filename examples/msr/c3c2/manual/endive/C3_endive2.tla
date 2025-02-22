--------------------------- MODULE C3_endive2 ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, Randomization

\*CONSTANTS Server, Quorums, FinNat

CONSTANTS Server, FinNat, n1,n2,n3
Quorums == {S \in SUBSET Server : 2*Cardinality(S) > Cardinality(Server)}

VARIABLES BecLeaderTerm, LeaderTerm, log, ClReq, ActiveTerm, CommitTerm, Fluent2

vars == <<BecLeaderTerm, LeaderTerm, log, ClReq, ActiveTerm, CommitTerm, Fluent2>>

Symmetry == Permutations(Server)
NextUnchanged == UNCHANGED vars

CandSep ==
/\ \A var0 \in FinNat : \E var1 \in Server : \A var2 \in Server : (BecLeaderTerm[var2][var0]) => (var2 = var1)
/\ \A var0 \in FinNat : CommitTerm[var0] => ActiveTerm[var0]
/\ \A var0 \in FinNat : \A var1 \in FinNat : ActiveTerm[var0] => (LeaderTerm[var1] => (var1 <= var0))
/\ \A var0 \in Server : \A var1 \in FinNat : ClReq[var0][var1] => BecLeaderTerm[var0][var1]
/\ \A ind,t \in FinNat : (Fluent2[ind][t] /\ ActiveTerm[t]) => CommitTerm[t]
/\ \A t \in FinNat : ActiveTerm[t] => \E s \in Server : BecLeaderTerm[s][t]


FalseQuorums == [q \in Quorums |-> FALSE]

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

Empty(s) == Len(s) = 0

InLog(e,i) ==
\E x \in DOMAIN(log[i]) :
/\ x = e[1]
/\ log[i][x] = e[2]

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

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
/\ UNCHANGED<<BecLeaderTerm, LeaderTerm, ActiveTerm, CommitTerm, Fluent2>>
/\ CandSep'

GetEntries(i,j) ==
/\ Len(log[j]) > Len(log[i])
/\ LET logOk == IF Empty(log[i]) THEN TRUE ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
  /\ logOk
  /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE (Len(log[i]) + 1)
      newEntry == log[j][newEntryIndex]
      newLog == Append(log[i],newEntry) IN
    /\ log' = [log EXCEPT![i] = newLog]
/\ UNCHANGED<<LeaderTerm, ActiveTerm, CommitTerm, Fluent2>>
/\ ClReq' = [ClReq EXCEPT ![i] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ BecLeaderTerm' = [BecLeaderTerm EXCEPT ![i] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ CandSep'

RollbackEntries(i,j) ==
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED<<LeaderTerm, ActiveTerm, CommitTerm, Fluent2>>
/\ ClReq' = [ClReq EXCEPT ![i] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ BecLeaderTerm' = [BecLeaderTerm EXCEPT ![i] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ CandSep'

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ UNCHANGED <<log>>
/\ ClReq' = [s \in Server |-> IF (s \in voteQuorum) THEN [x1 \in FinNat |-> FALSE] ELSE ClReq[s]] \* specialized fluent
/\ BecLeaderTerm' = [[s \in Server |-> IF (s \in voteQuorum) THEN [x1 \in FinNat |-> FALSE] ELSE BecLeaderTerm[s]] EXCEPT![i][newTerm] = TRUE] \* specialized fluent
/\ ActiveTerm' = [[x \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ CommitTerm' = [x \in FinNat |-> FALSE]
/\ LeaderTerm' = [LeaderTerm EXCEPT ![newTerm] = TRUE]
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ ind = Len(log[i])
/\ ind > 0
/\ log[i][ind] = curTerm
/\ (\A s \in commitQuorum : (Len(log[s]) >= ind /\ InLog(<<ind,curTerm>>,s)))
/\ UNCHANGED <<log>>
/\ CommitTerm' = [CommitTerm EXCEPT ![curTerm] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ UNCHANGED<<BecLeaderTerm, LeaderTerm, ClReq, ActiveTerm>>
/\ CandSep'

Init ==
/\ log = [i \in Server |-> <<>>]
/\ BecLeaderTerm = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ LeaderTerm = [ x0 \in FinNat |-> FALSE]
/\ ClReq = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
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
/\ ActiveTerm \in [FinNat -> BOOLEAN]
/\ CommitTerm \in [FinNat -> BOOLEAN]
/\ Fluent2 \in [FinNat -> [FinNat -> BOOLEAN]]
/\ log \in [Server -> Seq(FinNat)]

rnum == 200
TypeOKRand ==
(*
/\ ActiveTerm \in {tf \in [FinNat -> BOOLEAN] : \E t1 \in FinNat : \A t2 \in FinNat : tf[t2] => (t2 = t1)}
/\ CommitTerm \in {cf \in [FinNat -> BOOLEAN] : \A var0 \in FinNat : cf[var0] => ActiveTerm[var0]}
/\ LeaderTerm \in {lf \in [FinNat -> BOOLEAN] : \A var0 \in FinNat : \A var1 \in FinNat : ActiveTerm[var0] => (lf[var1] => (var1 <= var0))}
/\ BecLeaderTerm \in {bf \in RandomSubset(rnum, [Server -> [FinNat -> BOOLEAN]]) : \A var0 \in FinNat : \E var1 \in Server : \A var2 \in Server : (bf[var2][var0]) => (var2 = var1)}
/\ ClReq \in {cf \in RandomSubset(rnum, [Server -> [FinNat -> BOOLEAN]]) : \A var0 \in Server : \A var1 \in FinNat : cf[var0][var1] => BecLeaderTerm[var0][var1]}
/\ Fluent2 \in RandomSubset(rnum, [FinNat -> [FinNat -> BOOLEAN]])
/\ log \in {lf \in RandomSubset(rnum, [Server -> FinSeq(FinNat)]) : \A s \in Server : \A ind1,ind2 \in DOMAIN lf[s] : (ind1 < ind2) => (lf[s][ind1] <= lf[s][ind2])}
*)
\* TODO eliminate this CTI
/\ log = (n1 :> <<1, 1>> @@ n2 :> <<1, 1, 1>> @@ n3 :> <<1, 1, 1>>)
/\ CommitTerm = <<FALSE, FALSE, FALSE>>
/\ Fluent2 = <<<<TRUE, FALSE, FALSE>>, <<TRUE, FALSE, FALSE>>, <<TRUE, FALSE, FALSE>>>>
/\ LeaderTerm = <<TRUE, TRUE, TRUE>>
/\ ActiveTerm = <<FALSE, FALSE, TRUE>>
/\ BecLeaderTerm = ( n1 :> <<FALSE, TRUE, FALSE>> @@
  n2 :> <<FALSE, FALSE, TRUE>> @@
  n3 :> <<FALSE, FALSE, FALSE>> )
/\ ClReq = ( n1 :> <<FALSE, FALSE, FALSE>> @@
  n2 :> <<FALSE, FALSE, FALSE>> @@
  n3 :> <<FALSE, FALSE, FALSE>> )


IndInv ==
    /\ TypeOK
    /\ Safety
    /\ CandSep
    /\ \A n \in Server : \A t \in FinNat : BecLeaderTerm[n][t] => LeaderTerm[t]
    /\ \A n \in Server : \A t \in FinNat : (ActiveTerm[t] /\ BecLeaderTerm[n][t]) => (\A t2 \in FinNat : LeaderTerm[t2] => (t2 <= t))
    /\ \A n \in Server : \A t \in FinNat : ClReq[n][t] => BecLeaderTerm[n][t]
    /\ \A idx,t \in FinNat : Fluent2[idx][t] => LeaderTerm[t]

    \*/\ (\E q \in Quorums : CommitQuorum[q] \/ \E t \in FinNat : LeaderTerm[t]) => (\E q \in Quorums : ActiveQuorum[q])
    \*/\ (\E q \in Quorums : CommitQuorum[q]) => (\E ind,t \in FinNat : Fluent2[ind][t])

    /\ \A s \in Server : \A t \in FinNat : ClReq[s][t] => (\E idx \in DOMAIN log[s] : log[s][idx] = t)
    /\ \A ind,t \in FinNat : Fluent2[ind][t] => (\E q \in Quorums : \A s \in q : (ind \in DOMAIN log[s] /\ log[s][ind] = t))
    /\ \A s \in Server : \A ind1,ind2 \in DOMAIN log[s] : (ind1 < ind2) => (log[s][ind1] <= log[s][ind2])
    /\ \E p \in Server : \A s \in Server : \A ind \in DOMAIN log[s] : \A t,pt \in FinNat : (log[s][ind] = t /\ BecLeaderTerm[p][pt]) => (t <= pt)
    /\ \A t \in FinNat : (LeaderTerm[t] /\ \A t2 \in FinNat : t2 <= t) => ActiveTerm[t]
    /\ \A s \in Server : \A t \in FinNat : BecLeaderTerm[s][t] => (\A idx \in FinNat : Fluent2[idx][t] => (idx \in DOMAIN log[s] /\ log[s][idx] = t))
    /\ \A t \in FinNat : CommitTerm[t] => \E idx \in FinNat : Fluent2[idx][t]

    \*/\ (\E t \in FinNat : CommitTerm[t]) <=> (\E q \in Quorums : CommitQuorum[q])

    /\ \A s \in Server : \A t \in FinNat : BecLeaderTerm[s][t] => (\A idx \in DOMAIN log[s] : log[s][idx] <= t)
    /\ \A s \in Server : \A t \in FinNat : BecLeaderTerm[s][t] => (\A s2 \in Server : \A idx \in DOMAIN log[s2] : (log[s2][idx] = t) => (idx \in DOMAIN log[s] /\ log[s][idx] = t))
    /\ \A s \in Server : \A t \in FinNat : BecLeaderTerm[s][t] => (\A idx \in DOMAIN log[s] : log[s][idx] <= t)
    /\ \A s \in Server : \A idx \in DOMAIN log[s] : \A t \in FinNat : ActiveTerm[t] => (log[s][idx] <= t)
    /\ \A s \in Server : \A ind,ind2 \in (DOMAIN log[s] \cap FinNat) : \A t,t2 \in FinNat : (log[s][ind] = t /\ Fluent2[ind][t] /\ Fluent2[ind2][t2] /\ ind2 < ind) => (log[s][ind2]=t2)

    \*/\ \A s \in Server : \A t \in FinNat : \A q \in Quorums : (BecLeaderTerm[s][t] /\ ActiveTerm[t] /\ ActiveQuorum[q]) => (s \in q)
    \*/\ \A p,s \in Server : \A q \in Quorums : (\E t \in FinNat : BecLeaderTerm[p][t] /\ ActiveTerm[t] /\ ActiveQuorum[q] /\ s \in q /\ \E idx \in DOMAIN log[s] : log[s][idx] = t) => IsPrefix(log[s], log[p])
    \*/\ \A p,s \in Server : \A q \in Quorums : (\E t \in FinNat : BecLeaderTerm[p][t] /\ ActiveTerm[t] /\ s \in q /\ \E idx \in DOMAIN log[s] : log[s][idx] = t) => IsPrefix(log[s], log[p])
    /\ \A p,s \in Server : (\E t \in FinNat : BecLeaderTerm[p][t] /\ ActiveTerm[t] /\ \E idx \in DOMAIN log[s] : log[s][idx] = t) => IsPrefix(log[s], log[p])

    /\ \A s \in Server : \A t1,t2 \in FinNat : (BecLeaderTerm[s][t1] /\ t2 < t1) => ~BecLeaderTerm[s][t2]
    /\ \A t \in FinNat : LeaderTerm[t] => \E s \in Server : \E t2 \in FinNat : BecLeaderTerm[s][t2] /\ ActiveTerm[t2]
    /\ \A p \in Server : \A pt \in FinNat : \A ind,t \in FinNat : (BecLeaderTerm[p][pt] /\ ActiveTerm[pt] /\ Fluent2[ind][t]) => (ind \in DOMAIN log[p] /\ log[p][ind]=t)
    /\ \A s1,s2 \in Server : \A idx,idx2 \in (DOMAIN log[s1] \cap DOMAIN log[s2] \cap FinNat) : \A t \in FinNat : (Fluent2[idx][t] /\ log[s1][idx] = t /\ log[s2][idx] = t /\ idx2 < idx) => (log[s1][idx2] = log[s2][idx2])
    /\ \A s \in Server : (\E t \in FinNat : BecLeaderTerm[s][t]) \/ (\E p \in Server : IsPrefix(log[s],log[p]))

    \*/\ \A s1,s2 \in Server : \A t \in FinNat : \A q \in Quorums : (BecLeaderTerm[s1][t] /\ BecLeaderTerm[s2][t] /\ {s1,s2} \subseteq q) => (s1=s2)
    /\ \A s1,s2 \in Server : \A t \in FinNat : (BecLeaderTerm[s1][t] /\ BecLeaderTerm[s2][t]) => (s1=s2)

    /\ \A s1,s2 \in Server : \A t \in FinNat : \A idx,idx2 \in (DOMAIN log[s1] \cap DOMAIN log[s2]) : (CanVoteForOplog(s1,s2,t) /\ Len(log[s1]) <= Len(log[s2]) /\ log[s1][idx] = log[s2][idx] /\ idx2 < idx) => log[s1][idx2] = log[s2][idx2]
    /\ \A idx,t \in FinNat : Fluent2[idx][t] => \A s \in Server : idx \in DOMAIN log[s] => log[s][idx] <= t
    /\ (\E s \in Server : Len(log[s]) > 0) => \E t \in FinNat : LeaderTerm[t]

    /\ \A s \in Server : \A t \in FinNat : (ActiveTerm[t] /\ BecLeaderTerm[s][t]) => (\E Q \in Quorums : \A q \in Q : \A t2 \in FinNat : q # s => ~BecLeaderTerm[q][t2])

IndInvRand == TypeOKRand /\ IndInv

IISpec == IndInvRand /\ [][Next]_vars

=============================================================================
