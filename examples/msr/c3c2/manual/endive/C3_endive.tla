--------------------------- MODULE C3_endive ---------------------------
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
StateConstraint == \A s \in Server : Len(log[s]) < 3 \* should match MAX FinNat to prevent an error

TypeOK ==
/\ BecLeaderTerm \in [Server -> [FinNat -> BOOLEAN]]
/\ LeaderTerm \in [FinNat -> BOOLEAN]
/\ ClReq \in [Server -> [FinNat -> BOOLEAN]]
/\ ActiveTerm \in [FinNat -> BOOLEAN]
/\ CommitTerm \in [FinNat -> BOOLEAN]
/\ Fluent2 \in [FinNat -> [FinNat -> BOOLEAN]]
/\ log \in [Server -> Seq(FinNat)]

rnum == 70 \*100
TypeOKRand ==
/\ ActiveTerm \in {tf \in [FinNat -> BOOLEAN] : \E t1 \in FinNat : \A t2 \in FinNat : tf[t2] => (t2 = t1)}
/\ CommitTerm \in {cf \in [FinNat -> BOOLEAN] : \A var0 \in FinNat : cf[var0] => ActiveTerm[var0]}
/\ LeaderTerm \in {lf \in [FinNat -> BOOLEAN] : \A var0 \in FinNat : \A var1 \in FinNat : ActiveTerm[var0] => (lf[var1] => (var1 <= var0))}
/\ BecLeaderTerm \in {bf \in RandomSubset(rnum, [Server -> [FinNat -> BOOLEAN]]) : \A var0 \in FinNat : \E var1 \in Server : \A var2 \in Server : (bf[var2][var0]) => (var2 = var1)}
/\ ClReq \in {cf \in RandomSubset(25, [Server -> [FinNat -> BOOLEAN]]) : \A var0 \in Server : \A var1 \in FinNat : cf[var0][var1] => BecLeaderTerm[var0][var1]}
/\ Fluent2 \in RandomSubset(rnum, [FinNat -> [FinNat -> BOOLEAN]])
/\ log \in {lf \in RandomSubset(rnum, [Server -> FinSeq(FinNat)]) : \A s \in Server : \A ind1,ind2 \in DOMAIN lf[s] : (ind1 < ind2) => (lf[s][ind1] <= lf[s][ind2])}


IndInv ==
    /\ TypeOK
    /\ Safety
    /\ CandSep
    /\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        BecLeaderTerm[s][t] => LeaderTerm[t]
    /\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        (ActiveTerm[t] /\ BecLeaderTerm[s][t] /\ LeaderTerm[t2]) => (t2 <= t)
    /\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        ClReq[s][t] => BecLeaderTerm[s][t]
    /\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        Fluent2[idx][t] => LeaderTerm[t]
    (*/\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        (s2 \in q2 /\ Fluent2[idx][t]) => (idx \in DOMAIN log[s2] /\ log[s2][idx] = t)
        *)
    /\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        (idx < idx2 /\ idx \in DOMAIN log[s] /\ idx2 \in DOMAIN log[s]) => (log[s][idx] <= log[s][idx2])
    /\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        (BecLeaderTerm[s][t] /\ Fluent2[idx][t]) => (idx \in DOMAIN log[s] /\ log[s][idx] = t)
    /\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        CommitTerm[t] => Fluent2[idx3][t]
    /\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        (BecLeaderTerm[s][t] /\ idx \in DOMAIN log[s]) => (log[s][idx] <= t)
    /\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        (BecLeaderTerm[s][t] /\ idx \in DOMAIN log[s2] /\ log[s2][idx] = t) => (idx \in DOMAIN log[s] /\ log[s][idx] = t)
    \*/\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        \*(BecLeaderTerm[s][t] /\ ActiveTerm[t] /\ ActiveQuorum[q]) => (s \in q)
    (*/\ \A s \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        LeaderTerm[t] => (BecLeaderTerm[n][t3] /\ ActiveTerm[t3])
        *)
    /\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        (ActiveTerm[t] /\ idx \in DOMAIN log[s]) => (log[s][idx] <= t)
    /\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        Fluent2[idx][t] => (idx \in DOMAIN log[s] => log[s][idx] <= t)
    /\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        (Len(log[s]) > 0) => LeaderTerm[t3]
    /\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        (BecLeaderTerm[s][t] /\ ActiveTerm[t] /\ Fluent2[idx][t2]) => (idx \in DOMAIN log[s] /\ log[s][idx]=t2)
    \*/\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        \*(BecLeaderTerm[s][t] /\ BecLeaderTerm[s2][t] /\ ActiveQuorum[q] /\ s \in q /\ s2 \in q) => (s = s2)
    /\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        (CanVoteForOplog(s,s2,t) /\ idx \in DOMAIN log[s] /\ Len(log[s]) <= Len(log[s2]) /\ log[s][idx] = log[s2][idx] /\ idx2 < idx) => log[s][idx2] = log[s2][idx2]
    /\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        ClReq[s][t] => (idx3 \in DOMAIN log[s] /\ log[s][idx3] = t)
    \*/\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        \*(BecLeaderTerm[s3][t3] /\ ActiveTerm[t3] /\ ActiveQuorum[q] /\ s \in q /\ idx3 \in DOMAIN log[s] /\ log[s][idx3] = t3) => IsPrefix(log[s], log[s3])
    /\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        (idx \in (DOMAIN log[s] \cap DOMAIN log[s2]) /\ idx2 < idx /\ Fluent2[idx][t] /\ log[s][idx] = t /\ log[s2][idx] = t) => (log[s][idx2] = log[s2][idx2])
    /\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        ~BecLeaderTerm[s][t] => IsPrefix(log[s],log[n])
    /\ \A s,s3 \in Server : \A idx,idx2,t,t2 \in FinNat : \E n \in Server : \E idx3,t3 \in FinNat : \A s2 \in Server :
        (BecLeaderTerm[s][t] /\ t2 < t) => ~BecLeaderTerm[s][t2]


IndInvRand == TypeOKRand /\ IndInv

IISpec == IndInvRand /\ [][Next]_vars

=============================================================================
