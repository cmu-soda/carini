--------------------------- MODULE C3_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

\*CONSTANTS Server, Quorums, FinNat

CONSTANTS Server, FinNat
Quorums == {S \in SUBSET Server : 2*Cardinality(S) > Cardinality(Server)}

VARIABLES Fluent11, BecLeaderTerm, Fluent8, Fluent7, log, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, ClReq, ActiveQuorum, CommitQuorum, ActiveTerm, CommitTerm

vars == <<Fluent11, BecLeaderTerm, Fluent8, Fluent7, log, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, ClReq, ActiveQuorum, CommitQuorum, ActiveTerm, CommitTerm>>

Symmetry == Permutations(Server)

CandSep ==
\*/\ \A var0 \in Server : (Fluent3[var0]) => (Fluent4[var0])
\*/\ \A var0 \in Server : (Fluent6[var0]) => (Fluent5[var0])
\*/\ \A var0 \in FinNat : (Fluent7[var0][var0]) => (Fluent8[var0])
\*/\ \A var0 \in FinNat : \E var1 \in Server : \A var2 \in Server : (BecLeaderTerm[var2][var0]) => (var2 = var1)
\*/\ \A var0 \in Server : \A var1 \in FinNat : (Fluent11[var1][var0]) => (Fluent10[var1][var0])

\* hand crafted invariants
\*/\ \A var0 \in Quorums : \A var1 \in Quorums : CommitQuorum[var0] => (ActiveQuorum[var1] => (var0 \cap var1 # {}))
/\ \A var0 \in FinNat : CommitTerm[var0] => ActiveTerm[var0]
/\ \A var0 \in FinNat : \A var1 \in FinNat : ActiveTerm[var0] => (Fluent8[var1] => (var1 <= var0))
/\ \A var0 \in Server : \A var1 \in FinNat : ClReq[var0][var1] => BecLeaderTerm[var0][var1]


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
/\ Fluent6' = [Fluent6 EXCEPT ![i] = TRUE]
/\ ClReq' = [ClReq EXCEPT ![i][curTerm] = TRUE]
/\ UNCHANGED<<Fluent11, BecLeaderTerm, Fluent8, Fluent7, Fluent5, Fluent10, Fluent4, Fluent3, ActiveQuorum, CommitQuorum, ActiveTerm, CommitTerm>>
/\ CandSep'
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ CandSep'

GetEntries(i,j) ==
/\ Len(log[j]) > Len(log[i])
/\ LET logOk == IF Empty(log[i]) THEN TRUE ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
  /\ logOk
  /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE (Len(log[i]) + 1)
      newEntry == log[j][newEntryIndex]
      newLog == Append(log[i],newEntry) IN
    /\ log' = [log EXCEPT![i] = newLog]
/\ UNCHANGED<<Fluent11, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, ActiveQuorum, CommitQuorum, ActiveTerm, CommitTerm>>
/\ ClReq' = [ClReq EXCEPT ![i] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ BecLeaderTerm' = [BecLeaderTerm EXCEPT ![i] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ CandSep'
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ CandSep'

RollbackEntries(i,j) ==
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED<<Fluent11, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, ActiveQuorum, CommitQuorum, ActiveTerm, CommitTerm>>
/\ ClReq' = [ClReq EXCEPT ![i] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ BecLeaderTerm' = [BecLeaderTerm EXCEPT ![i] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ CandSep'
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ CandSep'

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ UNCHANGED <<log>>
/\ ClReq' = [s \in Server |-> IF (s \in voteQuorum) THEN [x1 \in FinNat |-> FALSE] ELSE ClReq[s]] \* specialized fluent
/\ BecLeaderTerm' = [[s \in Server |-> IF (s \in voteQuorum) THEN [x1 \in FinNat |-> FALSE] ELSE BecLeaderTerm[s]] EXCEPT![i][newTerm] = TRUE] \* specialized fluent
/\ ActiveQuorum' = [[q \in Quorums |-> FALSE] EXCEPT ![voteQuorum] = TRUE]
/\ CommitQuorum' = [q \in Quorums |-> FALSE]
/\ ActiveTerm' = [[x \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ CommitTerm' = [x \in FinNat |-> FALSE]
/\ Fluent8' = [Fluent8 EXCEPT ![newTerm] = TRUE]
/\ Fluent5' = [Fluent5 EXCEPT ![i] = TRUE]
/\ Fluent10' = [Fluent10 EXCEPT ![newTerm][i] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent7, Fluent6, Fluent3>>
/\ CandSep'
/\ Fluent1' = [Fluent1 EXCEPT ![newTerm] = TRUE]
/\ UNCHANGED<<Fluent2, Fluent0>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ ind = Len(log[i])
/\ ind > 0
/\ log[i][ind] = curTerm
/\ (\A s \in commitQuorum : (Len(log[s]) >= ind /\ InLog(<<ind,curTerm>>,s)))
/\ UNCHANGED <<log>>
/\ CommitQuorum' = [CommitQuorum EXCEPT ![commitQuorum] = TRUE]
/\ CommitTerm' = [CommitTerm EXCEPT ![curTerm] = TRUE]
/\ Fluent11' = [Fluent11 EXCEPT ![curTerm][i] = TRUE]
/\ Fluent7' = [Fluent7 EXCEPT ![ind][curTerm] = TRUE]
/\ Fluent3' = [Fluent3 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<BecLeaderTerm, Fluent8, Fluent6, Fluent5, Fluent10, Fluent4, ClReq, ActiveQuorum, ActiveTerm>>
/\ CandSep'
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent1>>
/\ CandSep'

Init ==
/\ log = [i \in Server |-> <<>>]
/\ Fluent11 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ BecLeaderTerm = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent8 = [ x0 \in FinNat |-> FALSE]
/\ Fluent7 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent6 = [ x0 \in Server |-> FALSE]
/\ Fluent5 = [ x0 \in Server |-> FALSE]
/\ Fluent10 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent4 = [ x0 \in Server |-> FALSE]
/\ Fluent3 = [ x0 \in Server |-> FALSE]
/\ Fluent2 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent1 = [ x0 \in FinNat |-> FALSE]
/\ Fluent0 = [ x0 \in FinNat |-> FALSE]
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

Safety ==
/\ \A var0 \in FinNat : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent2[var0][var2]) => (var2 = var1)
=============================================================================
