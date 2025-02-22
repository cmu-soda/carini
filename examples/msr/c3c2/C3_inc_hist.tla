--------------------------- MODULE C3_inc_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent5_0, Fluent7_13, Fluent6_13, Fluent9_10, log, Fluent8_10, Fluent3_13, Fluent11_22, Fluent2, Fluent1, Fluent4_13, Fluent0, Fluent13_21, Fluent12_21, Fluent10_22, Fluent14_1, Fluent15_1, Fluent16_7, Fluent18_4, Fluent17_7, Fluent102

vars == <<Fluent5_0, Fluent7_13, Fluent6_13, Fluent9_10, log, Fluent8_10, Fluent3_13, Fluent11_22, Fluent2, Fluent1, Fluent4_13, Fluent0, Fluent13_21, Fluent12_21, Fluent10_22, Fluent14_1, Fluent15_1, Fluent16_7, Fluent18_4, Fluent17_7, Fluent102>>

CandSep ==
TRUE

CandSepOrig ==
/\ (\A var0 \in FinNat : (Fluent3_13[var0] => Fluent4_13[var0]))
/\ (\A var0 \in FinNat : (\E var1 \in FinNat : (var0 <= var1 => ~(Fluent5_0[var0]))))
/\ (\A var0 \in Quorums : (\A var1 \in Quorums : (\A var2 \in Server : (var0 = var1 => (Fluent6_13[var2] => Fluent7_13[var2])))))
/\ (\A var0 \in Server : (Fluent9_10[var0] => Fluent8_10[var0]))
/\ (\A var0 \in Quorums : (\A var1 \in FinNat : (\A var2 \in FinNat : (Fluent10_22[var2] => (Fluent11_22[var1][var0] => var2 <= var1)))))
/\ (\A var0 \in Quorums : (\A var1 \in FinNat : (\A var2 \in Server : ((var2 \in var0) => (Fluent12_21[var2][var1] => Fluent13_21[var2][var1])))))
/\ (\A var0 \in Server : (\A var1 \in FinNat : (Fluent15_1[var0][var1] => Fluent14_1[var0][var1])))
/\ (\A var0 \in FinNat : (Fluent16_7[var0] => Fluent17_7[var0]))
/\ (\A var0 \in FinNat : (\E var1 \in Server : (\A var2 \in Server : (Fluent18_4[var2][var0] => var1 = var2))))

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
/\ Fluent6_13' = [Fluent6_13 EXCEPT![i] = TRUE]
/\ Fluent3_13' = [Fluent3_13 EXCEPT![curTerm] = TRUE]
/\ Fluent12_21' = [Fluent12_21 EXCEPT![i][curTerm] = TRUE]
/\ UNCHANGED <<Fluent5_0,Fluent7_13,Fluent9_10,Fluent8_10,Fluent11_22,Fluent4_13,Fluent13_21,Fluent10_22,Fluent14_1,Fluent15_1,Fluent16_7,Fluent18_4,Fluent17_7>>
/\ CandSepOrig'
/\ UNCHANGED <<Fluent2,Fluent1,Fluent0>>
/\ CandSepOrig'
/\ UNCHANGED<<>>
/\ CandSep'
/\ UNCHANGED<<Fluent1, Fluent0, Fluent102>>
/\ CandSep'

GetEntries(i,j) ==
/\ Len(log[j]) > Len(log[i])
/\ LET logOk == IF Empty(log[i]) THEN TRUE ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
  /\ logOk
  /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE (Len(log[i]) + 1)
      newEntry == log[j][newEntryIndex]
      newLog == Append(log[i],newEntry) IN
    /\ log' = [log EXCEPT![i] = newLog]
/\ UNCHANGED <<Fluent5_0,Fluent7_13,Fluent6_13,Fluent9_10,Fluent8_10,Fluent3_13,Fluent11_22,Fluent4_13,Fluent13_21,Fluent12_21,Fluent10_22,Fluent14_1,Fluent15_1,Fluent16_7,Fluent18_4,Fluent17_7>>
/\ CandSepOrig'
/\ UNCHANGED <<Fluent2,Fluent1,Fluent0>>
/\ CandSepOrig'
/\ UNCHANGED<<>>
/\ CandSep'
/\ UNCHANGED<<Fluent1, Fluent0, Fluent102>>
/\ CandSep'

RollbackEntries(i,j) ==
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED <<Fluent5_0,Fluent7_13,Fluent6_13,Fluent9_10,Fluent8_10,Fluent3_13,Fluent11_22,Fluent4_13,Fluent13_21,Fluent12_21,Fluent10_22,Fluent14_1,Fluent15_1,Fluent16_7,Fluent18_4,Fluent17_7>>
/\ CandSepOrig'
/\ UNCHANGED <<Fluent2,Fluent1,Fluent0>>
/\ CandSepOrig'
/\ UNCHANGED<<>>
/\ CandSep'
/\ UNCHANGED<<Fluent1, Fluent0, Fluent102>>
/\ CandSep'

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ UNCHANGED <<log>>
/\ Fluent5_0' = [Fluent5_0 EXCEPT![newTerm] = TRUE]
/\ Fluent7_13' = [Fluent7_13 EXCEPT![i] = TRUE]
/\ Fluent9_10' = [x0 \in Server |-> FALSE]
/\ Fluent8_10' = [[x0 \in Server |-> FALSE] EXCEPT![i] = TRUE]
/\ Fluent11_22' = [[x0 \in FinNat |-> [x1 \in Quorums |-> FALSE]] EXCEPT![newTerm][voteQuorum] = TRUE]
/\ Fluent4_13' = [Fluent4_13 EXCEPT![newTerm] = TRUE]
/\ Fluent13_21' = [Fluent13_21 EXCEPT![i][newTerm] = TRUE]
/\ Fluent10_22' = [Fluent10_22 EXCEPT![newTerm] = TRUE]
/\ Fluent14_1' = [Fluent14_1 EXCEPT![i][newTerm] = TRUE]
/\ Fluent18_4' = [Fluent18_4 EXCEPT![i][newTerm] = TRUE]
/\ UNCHANGED <<Fluent6_13,Fluent3_13,Fluent12_21,Fluent15_1,Fluent16_7,Fluent17_7>>
/\ CandSepOrig'
/\ Fluent1' = [Fluent1 EXCEPT![newTerm] = TRUE]
/\ UNCHANGED <<Fluent2,Fluent0>>
/\ CandSepOrig'
/\ UNCHANGED<<>>
/\ CandSep'
/\ Fluent1' = [Fluent1 EXCEPT ![newTerm] = TRUE]
/\ UNCHANGED<<Fluent0, Fluent102>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm,minQTerm) ==
/\ ind = Len(log[i])
/\ ind > 0
/\ log[i][ind] = curTerm
/\ (\A s \in commitQuorum : (Len(log[s]) >= ind /\ InLog(<<ind,curTerm>>,s)))
/\ UNCHANGED <<log>>
/\ Fluent9_10' = [Fluent9_10 EXCEPT![i] = TRUE]
/\ Fluent15_1' = [Fluent15_1 EXCEPT![i][minQTerm] = TRUE]
/\ Fluent16_7' = [Fluent16_7 EXCEPT![minQTerm] = TRUE]
/\ Fluent17_7' = [Fluent17_7 EXCEPT![curTerm] = TRUE]
/\ UNCHANGED <<Fluent5_0,Fluent7_13,Fluent6_13,Fluent8_10,Fluent3_13,Fluent11_22,Fluent4_13,Fluent13_21,Fluent12_21,Fluent10_22,Fluent14_1,Fluent18_4>>
/\ CandSepOrig'
/\ Fluent2' = [Fluent2 EXCEPT![ind][curTerm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT![curTerm] = TRUE]
/\ UNCHANGED <<Fluent1>>
/\ CandSepOrig'
/\ UNCHANGED<<>>
/\ CandSep'
/\ Fluent0' = [Fluent0 EXCEPT ![curTerm] = TRUE]
/\ Fluent102' = [Fluent102 EXCEPT ![ind][curTerm] = TRUE]
/\ UNCHANGED<<Fluent1>>
/\ CandSep'

Init ==
/\ log = [i \in Server |-> <<>>]
/\ Fluent5_0 = [x0 \in FinNat |-> FALSE]
/\ Fluent7_13 = [x0 \in Server |-> FALSE]
/\ Fluent6_13 = [x0 \in Server |-> FALSE]
/\ Fluent9_10 = [x0 \in Server |-> FALSE]
/\ Fluent8_10 = [x0 \in Server |-> FALSE]
/\ Fluent3_13 = [x0 \in FinNat |-> FALSE]
/\ Fluent11_22 = [x0 \in FinNat |-> [x1 \in Quorums |-> FALSE]]
/\ Fluent4_13 = [x0 \in FinNat |-> FALSE]
/\ Fluent13_21 = [x0 \in Server |-> [x1 \in FinNat |-> FALSE]]
/\ Fluent12_21 = [x0 \in Server |-> [x1 \in FinNat |-> FALSE]]
/\ Fluent10_22 = [x0 \in FinNat |-> FALSE]
/\ Fluent14_1 = [x0 \in Server |-> [x1 \in FinNat |-> FALSE]]
/\ Fluent15_1 = [x0 \in Server |-> [x1 \in FinNat |-> FALSE]]
/\ Fluent16_7 = [x0 \in FinNat |-> FALSE]
/\ Fluent18_4 = [x0 \in Server |-> [x1 \in FinNat |-> FALSE]]
/\ Fluent17_7 = [x0 \in FinNat |-> FALSE]
/\ Fluent2 = [x0 \in FinNat |-> [x1 \in FinNat |-> FALSE]]
/\ Fluent1 = [x0 \in FinNat |-> FALSE]
/\ Fluent0 = [x0 \in FinNat |-> FALSE]
/\ Fluent1 = [ x0 \in FinNat |-> FALSE]
/\ Fluent0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent102 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s,t \in Server : GetEntries(s,t))
\/ (\E s,t \in Server : RollbackEntries(s,t))
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : (\E minQTerm \in FinNat : CommitEntry(s,Q,ind,curTerm,minQTerm))))))

Spec == (Init /\ [][Next]_vars)

Safety ==
/\ \A var0 \in FinNat : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent102[var0][var2]) => (var2 = var1)
=============================================================================
