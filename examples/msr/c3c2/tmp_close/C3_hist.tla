--------------------------- MODULE C3_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent7_22, Fluent11_16, log, Fluent4_4, Fluent8_22, Fluent3_4, Fluent6_18, Fluent2, Fluent1, Fluent12_16, Fluent0, Fluent20_1, Fluent5_18, Fluent15_0, Fluent10_4, Fluent13_4, Fluent18_1, Fluent14_4, Fluent19_1, Fluent16_7, Fluent9_4, Fluent17_7

vars == <<Fluent7_22, Fluent11_16, log, Fluent4_4, Fluent8_22, Fluent3_4, Fluent6_18, Fluent2, Fluent1, Fluent12_16, Fluent0, Fluent20_1, Fluent5_18, Fluent15_0, Fluent10_4, Fluent13_4, Fluent18_1, Fluent14_4, Fluent19_1, Fluent16_7, Fluent9_4, Fluent17_7>>

CandSep ==
/\ \A var0 \in FinNat : (Fluent4_4[var0]) => (Fluent3_4[var0])
/\ \A var0 \in Server : (Fluent6_18[var0]) => (Fluent5_18[var0])
/\ \A var0 \in Quorums : \A var1 \in FinNat : (Fluent8_22[var1][var0]) => (Fluent7_22[var1])
/\ \A var0 \in FinNat : (Fluent10_4[var0]) => (~(Fluent9_4[var0]))
/\ \A var0 \in FinNat : (Fluent11_16[var0]) => (Fluent12_16[var0])
/\ \A var0 \in FinNat : \A var1 \in Server : (Fluent14_4[var1][var0]) => (Fluent13_4[var1][var0])
/\ \A var0 \in FinNat : \E var1 \in FinNat : (var0 <= var1) => (~(Fluent15_0[var0]))
/\ \A var0 \in FinNat : \A var1 \in FinNat : (Fluent17_7[var1]) => ((Fluent16_7[var0]) => (var0 <= var1))
/\ \A var0 \in Server : (Fluent19_1[var0]) => (~(Fluent18_1[var0]))
/\ \A var0 \in Server : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent20_1[var2][var0]) => (var1 = var2)

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
/\ Fluent4_4' = [Fluent4_4 EXCEPT ![curTerm] = TRUE]
/\ Fluent6_18' = [Fluent6_18 EXCEPT ![i] = TRUE]
/\ Fluent20_1' = [Fluent20_1 EXCEPT ![curTerm][i] = TRUE]
/\ Fluent10_4' = [x0 \in FinNat |-> FALSE]
/\ Fluent14_4' = [Fluent14_4 EXCEPT ![i][curTerm] = TRUE]
/\ Fluent19_1' = [Fluent19_1 EXCEPT ![i] = TRUE]
/\ Fluent9_4' = [Fluent9_4 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent7_22, Fluent11_16, Fluent8_22, Fluent3_4, Fluent12_16, Fluent5_18, Fluent15_0, Fluent13_4, Fluent18_1, Fluent16_7, Fluent17_7>>
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
/\ Fluent18_1' = [Fluent18_1 EXCEPT ![i] = TRUE]
/\ Fluent19_1' = [Fluent19_1 EXCEPT ![i] = FALSE]
/\ UNCHANGED<<Fluent7_22, Fluent11_16, Fluent4_4, Fluent8_22, Fluent3_4, Fluent6_18, Fluent12_16, Fluent20_1, Fluent5_18, Fluent15_0, Fluent10_4, Fluent13_4, Fluent14_4, Fluent16_7, Fluent9_4, Fluent17_7>>
/\ CandSep'
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ CandSep'

RollbackEntries(i,j) ==
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED<<Fluent7_22, Fluent11_16, Fluent4_4, Fluent8_22, Fluent3_4, Fluent6_18, Fluent12_16, Fluent20_1, Fluent5_18, Fluent15_0, Fluent10_4, Fluent13_4, Fluent18_1, Fluent14_4, Fluent19_1, Fluent16_7, Fluent9_4, Fluent17_7>>
/\ CandSep'
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ CandSep'

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ UNCHANGED <<log>>
/\ Fluent7_22' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ Fluent8_22' = [x0 \in FinNat |-> [x1 \in Quorums |-> FALSE]]
/\ Fluent3_4' = [Fluent3_4 EXCEPT ![newTerm] = TRUE]
/\ Fluent12_16' = [Fluent12_16 EXCEPT ![newTerm] = TRUE]
/\ Fluent20_1' = [x0 \in FinNat |-> [x1 \in Server |-> FALSE]]
/\ Fluent5_18' = [Fluent5_18 EXCEPT ![i] = TRUE]
/\ Fluent15_0' = [Fluent15_0 EXCEPT ![newTerm] = TRUE]
/\ Fluent10_4' = [Fluent10_4 EXCEPT ![newTerm] = TRUE]
/\ Fluent13_4' = [Fluent13_4 EXCEPT ![i][newTerm] = TRUE]
/\ Fluent18_1' = [Fluent18_1 EXCEPT ![i] = FALSE]
/\ Fluent16_7' = [Fluent16_7 EXCEPT ![newTerm] = TRUE]
/\ Fluent17_7' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ UNCHANGED<<Fluent11_16, Fluent4_4, Fluent6_18, Fluent14_4, Fluent19_1, Fluent9_4>>
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
/\ Fluent11_16' = [Fluent11_16 EXCEPT ![minQTerm] = TRUE]
/\ Fluent8_22' = [Fluent8_22 EXCEPT ![curTerm][commitQuorum] = TRUE]
/\ UNCHANGED<<Fluent7_22, Fluent4_4, Fluent3_4, Fluent6_18, Fluent12_16, Fluent20_1, Fluent5_18, Fluent15_0, Fluent10_4, Fluent13_4, Fluent18_1, Fluent14_4, Fluent19_1, Fluent16_7, Fluent9_4, Fluent17_7>>
/\ CandSep'
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent1>>
/\ CandSep'

Init ==
/\ log = [i \in Server |-> <<>>]
/\ Fluent7_22 = [ x0 \in FinNat |-> FALSE]
/\ Fluent11_16 = [ x0 \in FinNat |-> FALSE]
/\ Fluent4_4 = [ x0 \in FinNat |-> FALSE]
/\ Fluent8_22 = [ x0 \in FinNat |-> [ x1 \in Quorums |-> FALSE]]
/\ Fluent3_4 = [ x0 \in FinNat |-> FALSE]
/\ Fluent6_18 = [ x0 \in Server |-> FALSE]
/\ Fluent12_16 = [ x0 \in FinNat |-> FALSE]
/\ Fluent20_1 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent5_18 = [ x0 \in Server |-> FALSE]
/\ Fluent15_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent10_4 = [ x0 \in FinNat |-> FALSE]
/\ Fluent13_4 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent18_1 = [ x0 \in Server |-> FALSE]
/\ Fluent14_4 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent19_1 = [ x0 \in Server |-> FALSE]
/\ Fluent16_7 = [ x0 \in FinNat |-> FALSE]
/\ Fluent9_4 = [ x0 \in FinNat |-> FALSE]
/\ Fluent17_7 = [ x0 \in FinNat |-> FALSE]
/\ Fluent2 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent1 = [ x0 \in FinNat |-> FALSE]
/\ Fluent0 = [ x0 \in FinNat |-> FALSE]

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
