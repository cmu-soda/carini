--------------------------- MODULE C3_ian ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent3_7, Fluent6_4, log, Fluent5_4, Fluent4_4, Fluent8_6, Fluent2, Fluent1, Fluent7_4, Fluent0, Fluent9_6, CurCommitEntry

vars == <<Fluent3_7, Fluent6_4, log, Fluent5_4, Fluent4_4, Fluent8_6, Fluent2, Fluent1, Fluent7_4, Fluent0, Fluent9_6, CurCommitEntry>>

CandSep ==
/\ \A var0 \in FinNat : \E var1 \in FinNat : (var0 <= var1) => (~(Fluent3_7[var0]))
/\ \A var0 \in FinNat : (Fluent5_4[var0]) => (Fluent4_4[var0])
/\ \A var0 \in FinNat : \A var1 \in Server : (Fluent7_4[var1][var0]) => (Fluent6_4[var1])
/\ \A var0 \in FinNat : \A var1 \in FinNat : (Fluent8_6[var0]) => ((Fluent9_6[var1]) => (var0 <= var1))

/\ \A var0 \in FinNat : \A var1 \in FinNat : Fluent9_6[var0] => (CurCommitEntry[var1] => (var0 = var1))

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
/\ Fluent3_7' = [Fluent3_7 EXCEPT ![curTerm] = TRUE]
/\ Fluent5_4' = [Fluent5_4 EXCEPT ![curTerm] = TRUE]
/\ Fluent7_4' = [Fluent7_4 EXCEPT ![i][curTerm] = TRUE]
/\ UNCHANGED<<Fluent6_4, Fluent4_4, Fluent8_6, Fluent9_6>>
/\ UNCHANGED CurCommitEntry
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
/\ UNCHANGED<<Fluent3_7, Fluent6_4, Fluent5_4, Fluent4_4, Fluent8_6, Fluent7_4, Fluent9_6>>
/\ UNCHANGED CurCommitEntry
/\ CandSep'
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ CandSep'

RollbackEntries(i,j) ==
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED<<Fluent3_7, Fluent6_4, Fluent5_4, Fluent4_4, Fluent8_6, Fluent7_4, Fluent9_6>>
/\ UNCHANGED CurCommitEntry
/\ CandSep'
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ CandSep'

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ UNCHANGED <<log>>
/\ Fluent6_4' = [Fluent6_4 EXCEPT ![i] = TRUE]
/\ Fluent4_4' = [Fluent4_4 EXCEPT ![newTerm] = TRUE]
/\ Fluent8_6' = [Fluent8_6 EXCEPT ![newTerm] = TRUE]
/\ Fluent9_6' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ UNCHANGED<<Fluent3_7, Fluent5_4, Fluent7_4>>
/\ CurCommitEntry' = [x0 \in FinNat |-> FALSE]
/\ CandSep'
/\ Fluent1' = [Fluent1 EXCEPT ![newTerm] = TRUE]
/\ UNCHANGED<<Fluent2, Fluent0>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm,minQTerm) ==
/\ ind = Len(log[i])
/\ ind > 0
/\ log[i][ind] = curTerm
/\ (\A s \in commitQuorum : (Len(log[s]) >= ind /\ InLog(<<ind,curTerm>>,s)))
/\ UNCHANGED <<log>>
/\ UNCHANGED<<Fluent3_7, Fluent6_4, Fluent5_4, Fluent4_4, Fluent8_6, Fluent7_4, Fluent9_6>>
/\ CurCommitEntry' = [CurCommitEntry EXCEPT ![minQTerm] = TRUE]
/\ CandSep'
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent1>>
/\ CandSep'

Init ==
/\ log = [i \in Server |-> <<>>]
/\ Fluent3_7 = [ x0 \in FinNat |-> FALSE]
/\ Fluent6_4 = [ x0 \in Server |-> FALSE]
/\ Fluent5_4 = [ x0 \in FinNat |-> FALSE]
/\ Fluent4_4 = [ x0 \in FinNat |-> FALSE]
/\ Fluent8_6 = [ x0 \in FinNat |-> FALSE]
/\ Fluent7_4 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent9_6 = [ x0 \in FinNat |-> FALSE]
/\ Fluent2 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent1 = [ x0 \in FinNat |-> FALSE]
/\ Fluent0 = [ x0 \in FinNat |-> FALSE]
/\ CurCommitEntry = [ x0 \in FinNat |-> FALSE]

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
