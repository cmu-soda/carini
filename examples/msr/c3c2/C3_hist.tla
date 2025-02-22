--------------------------- MODULE C3_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent28_24, log, Fluent20_2, Fluent21_2, Fluent2, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6

vars == <<Fluent28_24, log, Fluent20_2, Fluent21_2, Fluent2, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6>>

CandSep ==
/\ \A var0 \in FinNat : \A var1 \in FinNat : (Fluent17_6[var0]) => ((Fluent16_6[var1]) => (var0 <= var1))
/\ \A var0 \in FinNat : \A var1 \in Server : (Fluent18_2[var0][var1]) => (Fluent19_2[var0][var1])
/\ \A var0 \in FinNat : (Fluent20_2[var0]) => (Fluent21_2[var0])
/\ \A var0 \in FinNat : \E var1 \in Quorums : \A var2 \in Quorums : (Fluent28_24[var0][var2]) => (var2 = var1)

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
/\ Fluent18_2' = [Fluent18_2 EXCEPT ![curTerm][i] = TRUE]
/\ UNCHANGED<<Fluent28_24, Fluent20_2, Fluent21_2, Fluent19_2, Fluent17_6, Fluent16_6>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

GetEntries(i,j) ==
/\ Len(log[j]) > Len(log[i])
/\ LET logOk == IF Empty(log[i]) THEN TRUE ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
  /\ logOk
  /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE (Len(log[i]) + 1)
      newEntry == log[j][newEntryIndex]
      newLog == Append(log[i],newEntry) IN
    /\ log' = [log EXCEPT![i] = newLog]
/\ UNCHANGED<<Fluent28_24, Fluent20_2, Fluent21_2, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

RollbackEntries(i,j) ==
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED<<Fluent28_24, Fluent20_2, Fluent21_2, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ UNCHANGED <<log>>
/\ Fluent28_24' = [Fluent28_24 EXCEPT ![newTerm][voteQuorum] = TRUE]
/\ Fluent20_2' = [x0 \in FinNat |-> FALSE]
/\ Fluent21_2' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ Fluent19_2' = [Fluent19_2 EXCEPT ![newTerm][i] = TRUE]
/\ Fluent17_6' = [Fluent17_6 EXCEPT ![newTerm] = TRUE]
/\ Fluent16_6' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ UNCHANGED<<Fluent18_2>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm,minQTerm) ==
/\ ind = Len(log[i])
/\ ind > 0
/\ log[i][ind] = curTerm
/\ (\A s \in commitQuorum : (Len(log[s]) >= ind /\ InLog(<<ind,curTerm>>,s)))
/\ UNCHANGED <<log>>
/\ Fluent20_2' = [Fluent20_2 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent28_24, Fluent21_2, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6>>
/\ CandSep'
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ UNCHANGED<<>>
/\ CandSep'

Init ==
/\ log = [i \in Server |-> <<>>]
/\ Fluent28_24 = [ x0 \in FinNat |-> [ x1 \in Quorums |-> FALSE]]
/\ Fluent20_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent21_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent19_2 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent18_2 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent17_6 = [ x0 \in FinNat |-> FALSE]
/\ Fluent16_6 = [ x0 \in FinNat |-> FALSE]
/\ Fluent2 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s,t \in Server : GetEntries(s,t))
\/ (\E s,t \in Server : RollbackEntries(s,t))
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : (\E minQTerm \in FinNat : CommitEntry(s,Q,ind,curTerm,minQTerm))))))

Spec == (Init /\ [][Next]_vars)

Safety ==
/\ \A var0 \in FinNat : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent2[var0][var2]) => (var2 = var1)
=============================================================================
