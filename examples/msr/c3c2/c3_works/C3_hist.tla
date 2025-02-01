--------------------------- MODULE C3_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent9_14, log, Fluent12_18, Fluent10_14, Fluent5_17, Fluent22_1, Fluent20_16, Fluent27_5, Fluent26_5, Fluent24_12, Fluent11_18, Fluent3_7, Fluent8_1, Fluent7_1, Fluent2, Fluent13_0, Fluent6_17, Fluent15_0, Fluent21_16, Fluent14_0, Fluent17_0, Fluent23_17, Fluent16_0, Fluent19_2, Fluent18_2, Fluent25_12, Fluent4_7

vars == <<Fluent9_14, log, Fluent12_18, Fluent10_14, Fluent5_17, Fluent22_1, Fluent20_16, Fluent27_5, Fluent26_5, Fluent24_12, Fluent11_18, Fluent3_7, Fluent8_1, Fluent7_1, Fluent2, Fluent13_0, Fluent6_17, Fluent15_0, Fluent21_16, Fluent14_0, Fluent17_0, Fluent23_17, Fluent16_0, Fluent19_2, Fluent18_2, Fluent25_12, Fluent4_7>>

CandSep ==
/\ \A var0 \in FinNat : (Fluent4_7[var0]) => (Fluent3_7[var0])
/\ \A var0 \in FinNat : (Fluent6_17[var0]) => (Fluent5_17[var0])
/\ \A var0 \in Server : (Fluent7_1[var0]) => (Fluent8_1[var0])
/\ \A var0 \in FinNat : (Fluent9_14[var0]) => (Fluent10_14[var0])
/\ \A var0 \in Server : (Fluent11_18[var0]) => (Fluent12_18[var0])
/\ \A var0 \in FinNat : (Fluent13_0[var0]) => (Fluent14_0[var0])
/\ \A var0 \in FinNat : \E var1 \in FinNat : (Fluent15_0[var0]) => (~(var0 <= var1))
/\ \A var0 \in FinNat : \A var1 \in FinNat : (Fluent17_0[var1]) => ((var0 <= var1) => (~(Fluent16_0[var0])))
/\ \A var0 \in FinNat : \A var1 \in Server : \A var2 \in FinNat : (Fluent18_2[var2]) => ((Fluent19_2[var1][var0]) => (var2 <= var0))
/\ \A var0 \in FinNat : \A var1 \in Server : (Fluent20_16[var1][var0]) => (Fluent21_16[var1][var0])
/\ \A var0 \in Server : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent22_1[var0][var2]) => (var2 = var1)
/\ \A var0 \in FinNat : \E var1 \in Quorums : \A var2 \in Server : (Fluent23_17[var0][var2]) => (~(var2 \in var1))
/\ \A var0 \in Server : (Fluent25_12[var0]) => (~(Fluent24_12[var0]))
/\ \A var0 \in Server : (Fluent27_5[var0]) => (Fluent26_5[var0])

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
/\ Fluent22_1' = [Fluent22_1 EXCEPT ![i][curTerm] = TRUE]
/\ Fluent20_16' = [Fluent20_16 EXCEPT ![i][curTerm] = TRUE]
/\ Fluent27_5' = [Fluent27_5 EXCEPT ![i] = TRUE]
/\ Fluent7_1' = [Fluent7_1 EXCEPT ![i] = TRUE]
/\ Fluent17_0' = [Fluent17_0 EXCEPT ![curTerm] = TRUE]
/\ Fluent16_0' = [x0 \in FinNat |-> FALSE]
/\ Fluent4_7' = [Fluent4_7 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent9_14, Fluent12_18, Fluent10_14, Fluent5_17, Fluent26_5, Fluent24_12, Fluent11_18, Fluent3_7, Fluent8_1, Fluent13_0, Fluent6_17, Fluent15_0, Fluent21_16, Fluent14_0, Fluent23_17, Fluent19_2, Fluent18_2, Fluent25_12>>
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
/\ Fluent27_5' = [Fluent27_5 EXCEPT ![i] = FALSE]
/\ Fluent26_5' = [Fluent26_5 EXCEPT ![i] = FALSE]
/\ Fluent24_12' = [Fluent24_12 EXCEPT ![i] = TRUE]
/\ Fluent25_12' = [Fluent25_12 EXCEPT ![i] = FALSE]
/\ UNCHANGED<<Fluent9_14, Fluent12_18, Fluent10_14, Fluent5_17, Fluent22_1, Fluent20_16, Fluent11_18, Fluent3_7, Fluent8_1, Fluent7_1, Fluent13_0, Fluent6_17, Fluent15_0, Fluent21_16, Fluent14_0, Fluent17_0, Fluent23_17, Fluent16_0, Fluent19_2, Fluent18_2, Fluent4_7>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

RollbackEntries(i,j) ==
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED<<Fluent9_14, Fluent12_18, Fluent10_14, Fluent5_17, Fluent22_1, Fluent20_16, Fluent27_5, Fluent26_5, Fluent24_12, Fluent11_18, Fluent3_7, Fluent8_1, Fluent7_1, Fluent13_0, Fluent6_17, Fluent15_0, Fluent21_16, Fluent14_0, Fluent17_0, Fluent23_17, Fluent16_0, Fluent19_2, Fluent18_2, Fluent25_12, Fluent4_7>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ UNCHANGED <<log>>
/\ Fluent12_18' = [Fluent12_18 EXCEPT ![i] = TRUE]
/\ Fluent5_17' = [Fluent5_17 EXCEPT ![newTerm] = TRUE]
/\ Fluent22_1' = [x0 \in Server |-> [x1 \in FinNat |-> FALSE]]
/\ Fluent26_5' = [Fluent26_5 EXCEPT ![i] = TRUE]
/\ Fluent24_12' = [Fluent24_12 EXCEPT ![i] = FALSE]
/\ Fluent3_7' = [Fluent3_7 EXCEPT ![newTerm] = TRUE]
/\ Fluent8_1' = [Fluent8_1 EXCEPT ![i] = TRUE]
/\ Fluent13_0' = [x0 \in FinNat |-> FALSE]
/\ Fluent15_0' = [Fluent15_0 EXCEPT ![newTerm] = TRUE]
/\ Fluent21_16' = [Fluent21_16 EXCEPT ![i][newTerm] = TRUE]
/\ Fluent14_0' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ Fluent23_17' = [Fluent23_17 EXCEPT ![newTerm][i] = TRUE]
/\ Fluent16_0' = [Fluent16_0 EXCEPT ![newTerm] = TRUE]
/\ Fluent19_2' = [[x0 \in Server |-> [x1 \in FinNat |-> FALSE]] EXCEPT ![i][newTerm] = TRUE]
/\ Fluent18_2' = [Fluent18_2 EXCEPT ![newTerm] = TRUE]
/\ UNCHANGED<<Fluent9_14, Fluent10_14, Fluent20_16, Fluent27_5, Fluent11_18, Fluent7_1, Fluent6_17, Fluent17_0, Fluent25_12, Fluent4_7>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm,minQTerm) ==
/\ ind = Len(log[i])
/\ ind > 0
/\ log[i][ind] = curTerm
/\ (\A s \in commitQuorum : (Len(log[s]) >= ind /\ InLog(<<ind,curTerm>>,s)))
/\ UNCHANGED <<log>>
/\ Fluent9_14' = [Fluent9_14 EXCEPT ![minQTerm] = TRUE]
/\ Fluent10_14' = [Fluent10_14 EXCEPT ![curTerm] = TRUE]
/\ Fluent11_18' = [Fluent11_18 EXCEPT ![i] = TRUE]
/\ Fluent13_0' = [Fluent13_0 EXCEPT ![minQTerm] = TRUE]
/\ Fluent6_17' = [Fluent6_17 EXCEPT ![minQTerm] = TRUE]
/\ Fluent25_12' = [Fluent25_12 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent12_18, Fluent5_17, Fluent22_1, Fluent20_16, Fluent27_5, Fluent26_5, Fluent24_12, Fluent3_7, Fluent8_1, Fluent7_1, Fluent15_0, Fluent21_16, Fluent14_0, Fluent17_0, Fluent23_17, Fluent16_0, Fluent19_2, Fluent18_2, Fluent4_7>>
/\ CandSep'
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ UNCHANGED<<>>
/\ CandSep'

Init ==
/\ log = [i \in Server |-> <<>>]
/\ Fluent9_14 = [ x0 \in FinNat |-> FALSE]
/\ Fluent12_18 = [ x0 \in Server |-> FALSE]
/\ Fluent10_14 = [ x0 \in FinNat |-> FALSE]
/\ Fluent5_17 = [ x0 \in FinNat |-> FALSE]
/\ Fluent22_1 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent20_16 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent27_5 = [ x0 \in Server |-> FALSE]
/\ Fluent26_5 = [ x0 \in Server |-> FALSE]
/\ Fluent24_12 = [ x0 \in Server |-> FALSE]
/\ Fluent11_18 = [ x0 \in Server |-> FALSE]
/\ Fluent3_7 = [ x0 \in FinNat |-> FALSE]
/\ Fluent8_1 = [ x0 \in Server |-> FALSE]
/\ Fluent7_1 = [ x0 \in Server |-> FALSE]
/\ Fluent13_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent6_17 = [ x0 \in FinNat |-> FALSE]
/\ Fluent15_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent21_16 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent14_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent17_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent23_17 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent16_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent19_2 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent18_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent25_12 = [ x0 \in Server |-> FALSE]
/\ Fluent4_7 = [ x0 \in FinNat |-> FALSE]
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
