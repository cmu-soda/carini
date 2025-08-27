--------------------------- MODULE C3_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES log, Fluent60_4, Fluent41_1, Fluent2, Fluent52_5, Fluent33_2, Fluent31_7, Fluent32_7, Fluent20_14, Fluent34_2, Fluent53_5, Fluent21_17, Fluent22_17, Fluent19_4, Fluent18_4

vars == <<log, Fluent60_4, Fluent41_1, Fluent2, Fluent52_5, Fluent33_2, Fluent31_7, Fluent32_7, Fluent20_14, Fluent34_2, Fluent53_5, Fluent21_17, Fluent22_17, Fluent19_4, Fluent18_4>>

CandSep ==
/\ \A var0 \in Server : \A var1 \in Server : \A var2 \in FinNat : (var0 = var1) => ((Fluent52_5[var0][var2]) => (Fluent53_5[var0][var2]))
/\ \A var0 \in FinNat : \E var1 \in Server : \A var2 \in Server : (Fluent60_4[var2][var0]) => (var2 = var1)
/\ \A var0 \in FinNat : (Fluent33_2[var0]) => (Fluent34_2[var0])
/\ \A var0 \in Server : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent41_1[var0][var2]) => (var1 = var2)
/\ \A var0 \in FinNat : (Fluent19_4[var0]) => (~(Fluent18_4[var0]))
/\ \A var0 \in FinNat : \A var1 \in FinNat : (Fluent32_7[var0]) => ((Fluent31_7[var1]) => (var1 <= var0))
/\ \A var0 \in FinNat : (Fluent21_17[var0]) => (Fluent22_17[var0])
/\ \A var0 \in FinNat : \E var1 \in FinNat : (Fluent20_14[var0]) => (~(var0 <= var1))

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
/\ Fluent41_1' = [Fluent41_1 EXCEPT ![i][curTerm] = TRUE]
/\ Fluent52_5' = [Fluent52_5 EXCEPT ![i][curTerm] = TRUE]
/\ Fluent21_17' = [Fluent21_17 EXCEPT ![curTerm] = TRUE]
/\ Fluent22_17' = [x0 \in FinNat |-> TRUE]
/\ UNCHANGED<<Fluent60_4, Fluent33_2, Fluent31_7, Fluent32_7, Fluent20_14, Fluent34_2, Fluent53_5, Fluent19_4, Fluent18_4>>
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
/\ Fluent52_5' = [x0 \in Server |-> [x1 \in FinNat |-> FALSE]]
/\ Fluent53_5' = [Fluent53_5 EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ UNCHANGED<<Fluent60_4, Fluent41_1, Fluent33_2, Fluent31_7, Fluent32_7, Fluent20_14, Fluent34_2, Fluent21_17, Fluent22_17, Fluent19_4, Fluent18_4>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

RollbackEntries(i,j) ==
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED<<Fluent60_4, Fluent41_1, Fluent52_5, Fluent33_2, Fluent31_7, Fluent32_7, Fluent20_14, Fluent34_2, Fluent53_5, Fluent21_17, Fluent22_17, Fluent19_4, Fluent18_4>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ UNCHANGED <<log>>
/\ Fluent60_4' = [Fluent60_4 EXCEPT ![i][newTerm] = TRUE]
/\ Fluent41_1' = [Fluent41_1 EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ Fluent31_7' = [Fluent31_7 EXCEPT ![newTerm] = TRUE]
/\ Fluent32_7' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ Fluent20_14' = [Fluent20_14 EXCEPT ![newTerm] = TRUE]
/\ Fluent53_5' = [Fluent53_5 EXCEPT ![i][newTerm] = TRUE]
/\ Fluent22_17' = [Fluent22_17 EXCEPT ![newTerm] = FALSE]
/\ Fluent19_4' = [[x0 \in FinNat |-> TRUE] EXCEPT ![newTerm] = FALSE]
/\ Fluent18_4' = [x0 \in FinNat |-> FALSE]
/\ UNCHANGED<<Fluent52_5, Fluent33_2, Fluent34_2, Fluent21_17>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm,minQTerm) ==
/\ ind = Len(log[i])
/\ ind > 0
/\ log[i][ind] = curTerm
/\ (\A s \in commitQuorum : (Len(log[s]) >= ind /\ InLog(<<ind,curTerm>>,s)))
/\ UNCHANGED <<log>>
/\ Fluent33_2' = [Fluent33_2 EXCEPT ![minQTerm] = TRUE]
/\ Fluent34_2' = [Fluent34_2 EXCEPT ![curTerm] = TRUE]
/\ Fluent18_4' = [Fluent18_4 EXCEPT ![minQTerm] = TRUE]
/\ UNCHANGED<<Fluent60_4, Fluent41_1, Fluent52_5, Fluent31_7, Fluent32_7, Fluent20_14, Fluent53_5, Fluent21_17, Fluent22_17, Fluent19_4>>
/\ CandSep'
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ UNCHANGED<<>>
/\ CandSep'

Init ==
/\ log = [i \in Server |-> <<>>]
/\ Fluent60_4 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent41_1 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent52_5 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent33_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent31_7 = [ x0 \in FinNat |-> FALSE]
/\ Fluent32_7 = [ x0 \in FinNat |-> FALSE]
/\ Fluent20_14 = [ x0 \in FinNat |-> FALSE]
/\ Fluent34_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent53_5 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent21_17 = [ x0 \in FinNat |-> FALSE]
/\ Fluent22_17 = [ x0 \in FinNat |-> FALSE]
/\ Fluent19_4 = [ x0 \in FinNat |-> FALSE]
/\ Fluent18_4 = [ x0 \in FinNat |-> FALSE]
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
