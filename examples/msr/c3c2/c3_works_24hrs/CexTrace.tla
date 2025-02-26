--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS n1, n2, Server, n3, Quorums, NUM2, NUM3, NUM0, NUM1, _n2n3_, _n1n2n3_, FinNat, _n1n3_, _n1n2_

VARIABLES err, log, Fluent29_5, Fluent2, Fluent30_5, cexTraceIdx

vars == <<err, log, Fluent29_5, Fluent2, Fluent30_5, cexTraceIdx>>

NoErr == err = FALSE

CandSep == (\A var0 \in Server : (Fluent29_5[var0] => ~(Fluent30_5[var0])))

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

StateConstraint == (\A s \in Server : Len(log[s]) < 4)

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
/\ Fluent29_5' = [Fluent29_5 EXCEPT![i] = TRUE]
/\ UNCHANGED <<Fluent30_5>>
/\ CandSep'
/\ UNCHANGED <<Fluent2>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

GetEntries(i,j) ==
/\ Len(log[j]) > Len(log[i])
/\ LET logOk == IF Empty(log[i]) THEN TRUE ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
  /\ logOk
  /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE (Len(log[i]) + 1)
      newEntry == log[j][newEntryIndex]
      newLog == Append(log[i],newEntry) IN
    /\ log' = [log EXCEPT![i] = newLog]
/\ Fluent29_5' = [Fluent29_5 EXCEPT![i] = FALSE]
/\ Fluent30_5' = [Fluent30_5 EXCEPT![i] = TRUE]
/\ UNCHANGED <<>>
/\ CandSep'
/\ UNCHANGED <<Fluent2>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

RollbackEntries(i,j) ==
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED <<Fluent29_5,Fluent30_5>>
/\ CandSep'
/\ UNCHANGED <<Fluent2>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ UNCHANGED <<log>>
/\ Fluent30_5' = [x0 \in Server |-> FALSE]
/\ UNCHANGED <<Fluent29_5>>
/\ CandSep'
/\ UNCHANGED <<Fluent2>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

CommitEntry(i,commitQuorum,ind,curTerm,minQTerm) ==
/\ ind = Len(log[i])
/\ ind > 0
/\ log[i][ind] = curTerm
/\ (\A s \in commitQuorum : (Len(log[s]) >= ind /\ InLog(<<ind,curTerm>>,s)))
/\ UNCHANGED <<log>>
/\ UNCHANGED <<Fluent29_5,Fluent30_5>>
/\ CandSep'
/\ Fluent2' = [Fluent2 EXCEPT![ind][curTerm] = TRUE]
/\ UNCHANGED <<>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

Init ==
/\ log = [i \in Server |-> <<>>]
/\ Fluent29_5 = [x0 \in Server |-> FALSE]
/\ Fluent30_5 = [x0 \in Server |-> FALSE]
/\ Fluent2 = [x0 \in FinNat |-> [x1 \in FinNat |-> FALSE]]
/\ cexTraceIdx = 0
/\ err = FALSE

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s,t \in Server : GetEntries(s,t))
\/ (\E s,t \in Server : RollbackEntries(s,t))
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : (\E minQTerm \in FinNat : CommitEntry(s,Q,ind,curTerm,minQTerm))))))

Spec == (Init /\ [][Next]_vars)

Safety ==
/\ (\A var0 \in FinNat : (\E var1 \in FinNat : (\A var2 \in FinNat : (Fluent2[var0][var2] => var2 = var1))))

TraceConstraint ==
/\ cexTraceIdx = 0 => BecomeLeader(n1,{n1, n2},1) /\ err' = err
/\ cexTraceIdx = 1 => BecomeLeader(n1,{n1, n3},2) /\ err' = err
/\ cexTraceIdx = 2 => ClientRequest(n1,2) /\ err' = err
/\ cexTraceIdx = 3 => ClientRequest(n1,2) /\ err' = err
/\ cexTraceIdx = 4 => GetEntries(n2,n1) /\ err' = err
/\ cexTraceIdx = 5 => GetEntries(n2,n1) /\ err' = err
/\ cexTraceIdx = 6 => GetEntries(n3,n2) /\ err' = err
/\ cexTraceIdx = 7 => CommitEntry(n1,{n1, n2},2,2,2) /\ err' = err
/\ cexTraceIdx = 8 => BecomeLeader(n2,{n2, n3},3) /\ err' = err
/\ cexTraceIdx = 9 => ClientRequest(n1,1) /\ err' = err
/\ cexTraceIdx = 10 => BecomeLeader(n3,{n1, n3},3) /\ err' = err
/\ cexTraceIdx = 11 => ClientRequest(n3,3) /\ err' = err
/\ cexTraceIdx = 12 => RollbackEntries(n2,n3) /\ err' = err
/\ cexTraceIdx = 13 => GetEntries(n2,n3) /\ err' = err
/\ cexTraceIdx = 14 => CommitEntry(n3,{n2, n3},2,3,3) /\ err' = TRUE
/\ cexTraceIdx >= 15 => FALSE

InternalAction == UNCHANGED<<cexTraceIdx,err>>

TraceConstraintSpec == Init /\ [][Next /\ (TraceConstraint \/ InternalAction)]_vars
=============================================================================
