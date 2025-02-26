--------------------------- MODULE C3_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent33_18, log, Fluent7_19, Fluent15_24, Fluent16_16, Fluent5_19, Fluent26_1, Fluent23_7, Fluent22_7, Fluent29_5, Fluent24_15, Fluent34_18, Fluent4_2, Fluent5_2, Fluent6_19, Fluent2, Fluent17_16, Fluent30_5, Fluent8_19, Fluent13_0, Fluent10_2, Fluent14_24, Fluent13_4, Fluent12_4, Fluent9_2, Fluent23_15

vars == <<Fluent33_18, log, Fluent7_19, Fluent15_24, Fluent16_16, Fluent5_19, Fluent26_1, Fluent23_7, Fluent22_7, Fluent29_5, Fluent24_15, Fluent34_18, Fluent4_2, Fluent5_2, Fluent6_19, Fluent2, Fluent17_16, Fluent30_5, Fluent8_19, Fluent13_0, Fluent10_2, Fluent14_24, Fluent13_4, Fluent12_4, Fluent9_2, Fluent23_15>>

CandSep ==
/\ \A var0 \in Server : \E var1 \in Quorums : \A var2 \in FinNat : (Fluent34_18[var0][var2]) => (Fluent33_18[var0][var2][var1])
/\ \A var0 \in FinNat : \A var1 \in Server : (Fluent17_16[var1][var0]) => (Fluent16_16[var1][var0])
/\ \A var0 \in FinNat : (Fluent12_4[var0]) => (Fluent13_4[var0])
/\ \A var0 \in FinNat : (Fluent10_2[var0]) => (Fluent9_2[var0])
/\ \A var0 \in Server : (Fluent8_19[var0]) => (Fluent7_19[var0])
/\ \A var0 \in FinNat : (Fluent23_15[var0]) => (Fluent24_15[var0])
/\ \A var0 \in FinNat : (Fluent4_2[var0]) => (Fluent5_2[var0])
/\ \A var0 \in Server : (Fluent6_19[var0]) => (Fluent5_19[var0])
/\ \A var0 \in FinNat : (Fluent14_24[var0]) => (~(Fluent15_24[var0]))
/\ \A var0 \in FinNat : \A var1 \in FinNat : (Fluent22_7[var0]) => ((Fluent23_7[var1]) => (var1 <= var0))
/\ \A var0 \in FinNat : \E var1 \in FinNat : (Fluent13_0[var0]) => (~(var0 <= var1))
/\ \A var0 \in Server : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent26_1[var2][var0]) => (var2 = var1)
/\ \A var0 \in Server : (Fluent29_5[var0]) => (~(Fluent30_5[var0]))

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

Symmetry == Permutations(Server)

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
/\ Fluent34_18' = [Fluent34_18 EXCEPT ![i][curTerm] = TRUE]
/\ Fluent4_2' = [Fluent4_2 EXCEPT ![curTerm] = TRUE]
/\ Fluent6_19' = [Fluent6_19 EXCEPT ![i] = TRUE]
/\ Fluent17_16' = [Fluent17_16 EXCEPT ![i][curTerm] = TRUE]
/\ Fluent15_24' = [Fluent15_24 EXCEPT ![curTerm] = TRUE]
/\ Fluent14_24' = [x0 \in FinNat |-> FALSE]
/\ Fluent26_1' = [Fluent26_1 EXCEPT ![curTerm][i] = TRUE]
/\ Fluent29_5' = [Fluent29_5 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent33_18, Fluent5_2, Fluent7_19, Fluent16_16, Fluent5_19, Fluent30_5, Fluent8_19, Fluent13_0, Fluent10_2, Fluent13_4, Fluent12_4, Fluent23_7, Fluent22_7, Fluent9_2, Fluent23_15, Fluent24_15>>
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
/\ Fluent30_5' = [Fluent30_5 EXCEPT ![i] = TRUE]
/\ Fluent29_5' = [Fluent29_5 EXCEPT ![i] = FALSE]
/\ UNCHANGED<<Fluent34_18, Fluent4_2, Fluent33_18, Fluent5_2, Fluent7_19, Fluent6_19, Fluent17_16, Fluent15_24, Fluent16_16, Fluent5_19, Fluent8_19, Fluent13_0, Fluent10_2, Fluent14_24, Fluent13_4, Fluent12_4, Fluent26_1, Fluent23_7, Fluent22_7, Fluent9_2, Fluent23_15, Fluent24_15>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

RollbackEntries(i,j) ==
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED<<Fluent34_18, Fluent4_2, Fluent33_18, Fluent5_2, Fluent7_19, Fluent6_19, Fluent17_16, Fluent15_24, Fluent16_16, Fluent5_19, Fluent30_5, Fluent8_19, Fluent13_0, Fluent10_2, Fluent14_24, Fluent13_4, Fluent12_4, Fluent26_1, Fluent23_7, Fluent22_7, Fluent29_5, Fluent9_2, Fluent23_15, Fluent24_15>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ UNCHANGED <<log>>
/\ Fluent34_18' = [Fluent34_18 EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ Fluent33_18' = [Fluent33_18 EXCEPT ![i][newTerm][voteQuorum] = TRUE]
/\ Fluent5_2' = [Fluent5_2 EXCEPT ![newTerm] = TRUE]
/\ Fluent7_19' = [Fluent7_19 EXCEPT ![i] = TRUE]
/\ Fluent16_16' = [Fluent16_16 EXCEPT ![i][newTerm] = TRUE]
/\ Fluent5_19' = [Fluent5_19 EXCEPT ![i] = TRUE]
/\ Fluent30_5' = [x0 \in Server |-> FALSE]
/\ Fluent13_0' = [Fluent13_0 EXCEPT ![newTerm] = TRUE]
/\ Fluent14_24' = [Fluent14_24 EXCEPT ![newTerm] = TRUE]
/\ Fluent13_4' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ Fluent12_4' = [x0 \in FinNat |-> FALSE]
/\ Fluent26_1' = [x0 \in FinNat |-> [x1 \in Server |-> FALSE]]
/\ Fluent23_7' = [Fluent23_7 EXCEPT ![newTerm] = TRUE]
/\ Fluent22_7' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ UNCHANGED<<Fluent4_2, Fluent6_19, Fluent17_16, Fluent15_24, Fluent8_19, Fluent10_2, Fluent29_5, Fluent9_2, Fluent23_15, Fluent24_15>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm,minQTerm) ==
/\ ind = Len(log[i])
/\ ind > 0
/\ log[i][ind] = curTerm
/\ (\A s \in commitQuorum : (Len(log[s]) >= ind /\ InLog(<<ind,curTerm>>,s)))
/\ UNCHANGED <<log>>
/\ Fluent8_19' = [Fluent8_19 EXCEPT ![i] = TRUE]
/\ Fluent10_2' = [Fluent10_2 EXCEPT ![curTerm] = TRUE]
/\ Fluent12_4' = [Fluent12_4 EXCEPT ![minQTerm] = TRUE]
/\ Fluent9_2' = [Fluent9_2 EXCEPT ![minQTerm] = TRUE]
/\ Fluent23_15' = [Fluent23_15 EXCEPT ![minQTerm] = TRUE]
/\ Fluent24_15' = [Fluent24_15 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent34_18, Fluent4_2, Fluent33_18, Fluent5_2, Fluent7_19, Fluent6_19, Fluent17_16, Fluent15_24, Fluent16_16, Fluent5_19, Fluent30_5, Fluent13_0, Fluent14_24, Fluent13_4, Fluent26_1, Fluent23_7, Fluent22_7, Fluent29_5>>
/\ CandSep'
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ UNCHANGED<<>>
/\ CandSep'

Init ==
/\ log = [i \in Server |-> <<>>]
/\ Fluent34_18 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent4_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent33_18 = [ x0 \in Server |-> [ x1 \in FinNat |-> [ x2 \in Quorums |-> FALSE]]]
/\ Fluent5_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent7_19 = [ x0 \in Server |-> FALSE]
/\ Fluent6_19 = [ x0 \in Server |-> FALSE]
/\ Fluent17_16 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent15_24 = [ x0 \in FinNat |-> FALSE]
/\ Fluent16_16 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent5_19 = [ x0 \in Server |-> FALSE]
/\ Fluent30_5 = [ x0 \in Server |-> FALSE]
/\ Fluent8_19 = [ x0 \in Server |-> FALSE]
/\ Fluent13_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent10_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent14_24 = [ x0 \in FinNat |-> FALSE]
/\ Fluent13_4 = [ x0 \in FinNat |-> FALSE]
/\ Fluent12_4 = [ x0 \in FinNat |-> FALSE]
/\ Fluent26_1 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent23_7 = [ x0 \in FinNat |-> FALSE]
/\ Fluent22_7 = [ x0 \in FinNat |-> FALSE]
/\ Fluent29_5 = [ x0 \in Server |-> FALSE]
/\ Fluent9_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent23_15 = [ x0 \in FinNat |-> FALSE]
/\ Fluent24_15 = [ x0 \in FinNat |-> FALSE]
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
