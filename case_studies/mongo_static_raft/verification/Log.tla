--------------------------- MODULE Log ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

VARIABLES log

CONSTANTS Server, Quorums, FinNat

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

vars == <<log>>

Symmetry == Permutations(Server)

StateConstraint == \A s \in Server : Len(log[s]) < 4

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

GetEntries(i,j) ==
/\ Len(log[j]) > Len(log[i])
/\ LET logOk == IF Empty(log[i]) THEN TRUE ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
  /\ logOk
  /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE (Len(log[i]) + 1)
      newEntry == log[j][newEntryIndex]
      newLog == Append(log[i],newEntry) IN
    /\ log' = [log EXCEPT![i] = newLog]

RollbackEntries(i,j) ==
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]

BecomeLeader(i,newTerm) ==
\E voteQuorum \in Quorums :
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ UNCHANGED <<log>>

CommitEntry(i,ind,curTerm) ==
\E commitQuorum \in Quorums :
/\ ind = Len(log[i])
/\ ind > 0
/\ log[i][ind] = curTerm
/\ \A s \in commitQuorum :
    /\ Len(log[s]) >= ind
    /\ InLog(<<ind,curTerm>>, s) \* they have the entry.
/\ UNCHANGED <<log>>

Init ==
/\ log = [i \in Server |-> <<>>]

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s,t \in Server : GetEntries(s,t))
\/ (\E s,t \in Server : RollbackEntries(s,t))
\/ (\E s \in Server : (\E newTerm \in FinNat : BecomeLeader(s,newTerm)))
\/ (\E s \in Server : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,ind,curTerm))))

Spec == (Init /\ [][Next]_vars)
=============================================================================
