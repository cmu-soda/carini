--------------------------- MODULE C3_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent28_24, log, Fluent12_16, Fluent20_2, Fluent21_2, Fluent22_1, Fluent27_1, Fluent23_7, Fluent24_7, Fluent26_8, Fluent25_8, Fluent4_0, Fluent3_0, Fluent11_16, Fluent5_5, Fluent9_1, Fluent2, Fluent10_1, Fluent14_1, Fluent15_0, Fluent13_1, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6, Fluent8_4, Fluent6_5, Fluent7_4

vars == <<Fluent28_24, log, Fluent12_16, Fluent20_2, Fluent21_2, Fluent22_1, Fluent27_1, Fluent23_7, Fluent24_7, Fluent26_8, Fluent25_8, Fluent4_0, Fluent3_0, Fluent11_16, Fluent5_5, Fluent9_1, Fluent2, Fluent10_1, Fluent14_1, Fluent15_0, Fluent13_1, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6, Fluent8_4, Fluent6_5, Fluent7_4>>

CandSep ==
/\ \A var0 \in FinNat : (Fluent3_0[var0]) => (Fluent4_0[var0])
/\ \A var0 \in Server : (Fluent5_5[var0]) => (Fluent6_5[var0])
/\ \A var0 \in FinNat : (Fluent7_4[var0]) => (Fluent8_4[var0])
/\ \A var0 \in Server : (Fluent9_1[var0]) => (Fluent10_1[var0])
/\ \A var0 \in FinNat : (Fluent12_16[var0]) => (Fluent11_16[var0])
/\ \A var0 \in Server : (Fluent14_1[var0]) => (Fluent13_1[var0])
/\ \A var0 \in FinNat : \E var1 \in FinNat : (var0 <= var1) => (~(Fluent15_0[var0]))
/\ \A var0 \in FinNat : \A var1 \in FinNat : (Fluent17_6[var0]) => ((Fluent16_6[var1]) => (var0 <= var1))
/\ \A var0 \in FinNat : \A var1 \in Server : (Fluent18_2[var0][var1]) => (Fluent19_2[var0][var1])
/\ \A var0 \in FinNat : (Fluent20_2[var0]) => (Fluent21_2[var0])
/\ \A var0 \in Server : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent22_1[var0][var2]) => (var1 = var2)
/\ \A var0 \in FinNat : (Fluent24_7[var0]) => (~(Fluent23_7[var0]))
/\ \A var0 \in Server : (Fluent26_8[var0]) => (Fluent25_8[var0])
/\ \A var0 \in Server : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent27_1[var0][var2]) => (var1 = var2)
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
/\ Fluent22_1' = [Fluent22_1 EXCEPT ![i][curTerm] = TRUE]
/\ Fluent27_1' = [Fluent27_1 EXCEPT ![i][curTerm] = TRUE]
/\ Fluent23_7' = [x0 \in FinNat |-> FALSE]
/\ Fluent24_7' = [Fluent24_7 EXCEPT ![curTerm] = TRUE]
/\ Fluent26_8' = [Fluent26_8 EXCEPT ![i] = TRUE]
/\ Fluent3_0' = [Fluent3_0 EXCEPT ![curTerm] = TRUE]
/\ Fluent5_5' = [Fluent5_5 EXCEPT ![i] = TRUE]
/\ Fluent18_2' = [Fluent18_2 EXCEPT ![curTerm][i] = TRUE]
/\ UNCHANGED<<Fluent28_24, Fluent12_16, Fluent20_2, Fluent21_2, Fluent25_8, Fluent4_0, Fluent11_16, Fluent9_1, Fluent10_1, Fluent14_1, Fluent15_0, Fluent13_1, Fluent19_2, Fluent17_6, Fluent16_6, Fluent8_4, Fluent6_5, Fluent7_4>>
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
/\ Fluent26_8' = [x0 \in Server |-> FALSE]
/\ Fluent25_8' = [Fluent25_8 EXCEPT ![i] = FALSE]
/\ UNCHANGED<<Fluent28_24, Fluent12_16, Fluent20_2, Fluent21_2, Fluent22_1, Fluent27_1, Fluent23_7, Fluent24_7, Fluent4_0, Fluent3_0, Fluent11_16, Fluent5_5, Fluent9_1, Fluent10_1, Fluent14_1, Fluent15_0, Fluent13_1, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6, Fluent8_4, Fluent6_5, Fluent7_4>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

RollbackEntries(i,j) ==
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED<<Fluent28_24, Fluent12_16, Fluent20_2, Fluent21_2, Fluent22_1, Fluent27_1, Fluent23_7, Fluent24_7, Fluent26_8, Fluent25_8, Fluent4_0, Fluent3_0, Fluent11_16, Fluent5_5, Fluent9_1, Fluent10_1, Fluent14_1, Fluent15_0, Fluent13_1, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6, Fluent8_4, Fluent6_5, Fluent7_4>>
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
/\ Fluent22_1' = [x0 \in Server |-> [x1 \in FinNat |-> FALSE]]
/\ Fluent27_1' = [Fluent27_1 EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ Fluent23_7' = [Fluent23_7 EXCEPT ![newTerm] = TRUE]
/\ Fluent25_8' = [Fluent25_8 EXCEPT ![i] = TRUE]
/\ Fluent4_0' = [Fluent4_0 EXCEPT ![newTerm] = TRUE]
/\ Fluent10_1' = [Fluent10_1 EXCEPT ![i] = TRUE]
/\ Fluent14_1' = [x0 \in Server |-> FALSE]
/\ Fluent15_0' = [Fluent15_0 EXCEPT ![newTerm] = TRUE]
/\ Fluent13_1' = [[x0 \in Server |-> FALSE] EXCEPT ![i] = TRUE]
/\ Fluent19_2' = [Fluent19_2 EXCEPT ![newTerm][i] = TRUE]
/\ Fluent17_6' = [Fluent17_6 EXCEPT ![newTerm] = TRUE]
/\ Fluent16_6' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ Fluent8_4' = [Fluent8_4 EXCEPT ![newTerm] = TRUE]
/\ Fluent6_5' = [Fluent6_5 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent12_16, Fluent24_7, Fluent26_8, Fluent3_0, Fluent11_16, Fluent5_5, Fluent9_1, Fluent18_2, Fluent7_4>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm,minQTerm) ==
/\ ind = Len(log[i])
/\ ind > 0
/\ log[i][ind] = curTerm
/\ (\A s \in commitQuorum : (Len(log[s]) >= ind /\ InLog(<<ind,curTerm>>,s)))
/\ UNCHANGED <<log>>
/\ Fluent12_16' = [Fluent12_16 EXCEPT ![curTerm] = TRUE]
/\ Fluent20_2' = [Fluent20_2 EXCEPT ![curTerm] = TRUE]
/\ Fluent11_16' = [Fluent11_16 EXCEPT ![minQTerm] = TRUE]
/\ Fluent9_1' = [Fluent9_1 EXCEPT ![i] = TRUE]
/\ Fluent14_1' = [Fluent14_1 EXCEPT ![i] = TRUE]
/\ Fluent7_4' = [Fluent7_4 EXCEPT ![minQTerm] = TRUE]
/\ UNCHANGED<<Fluent28_24, Fluent21_2, Fluent22_1, Fluent27_1, Fluent23_7, Fluent24_7, Fluent26_8, Fluent25_8, Fluent4_0, Fluent3_0, Fluent5_5, Fluent10_1, Fluent15_0, Fluent13_1, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6, Fluent8_4, Fluent6_5>>
/\ CandSep'
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ UNCHANGED<<>>
/\ CandSep'

Init ==
/\ log = [i \in Server |-> <<>>]
/\ Fluent28_24 = [ x0 \in FinNat |-> [ x1 \in Quorums |-> FALSE]]
/\ Fluent12_16 = [ x0 \in FinNat |-> FALSE]
/\ Fluent20_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent21_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent22_1 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent27_1 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent23_7 = [ x0 \in FinNat |-> FALSE]
/\ Fluent24_7 = [ x0 \in FinNat |-> FALSE]
/\ Fluent26_8 = [ x0 \in Server |-> FALSE]
/\ Fluent25_8 = [ x0 \in Server |-> FALSE]
/\ Fluent4_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent3_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent11_16 = [ x0 \in FinNat |-> FALSE]
/\ Fluent5_5 = [ x0 \in Server |-> FALSE]
/\ Fluent9_1 = [ x0 \in Server |-> FALSE]
/\ Fluent10_1 = [ x0 \in Server |-> FALSE]
/\ Fluent14_1 = [ x0 \in Server |-> FALSE]
/\ Fluent15_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent13_1 = [ x0 \in Server |-> FALSE]
/\ Fluent19_2 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent18_2 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent17_6 = [ x0 \in FinNat |-> FALSE]
/\ Fluent16_6 = [ x0 \in FinNat |-> FALSE]
/\ Fluent8_4 = [ x0 \in FinNat |-> FALSE]
/\ Fluent6_5 = [ x0 \in Server |-> FALSE]
/\ Fluent7_4 = [ x0 \in FinNat |-> FALSE]
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
