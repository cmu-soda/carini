--------------------------- MODULE C3_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES log, Fluent2, Fluent31_1, Fluent20_3, Fluent35_3, Fluent36_3, Fluent34_3, Fluent28_2, Fluent37_3, Fluent16_5, Fluent29_2, Fluent15_5, Fluent19_3

vars == <<log, Fluent2, Fluent31_1, Fluent20_3, Fluent35_3, Fluent36_3, Fluent34_3, Fluent28_2, Fluent37_3, Fluent16_5, Fluent29_2, Fluent15_5, Fluent19_3>>

CandSep ==
/\ \A var0 \in Server : (Fluent37_3[var0]) => (Fluent36_3[var0])
/\ \A var0 \in Server : (Fluent34_3[var0]) => (Fluent35_3[var0])
/\ \A var0 \in FinNat : \E var1 \in FinNat : ((var0 <= var1) => (Fluent29_2[var1])) => (~(Fluent28_2[var0]))
/\ \A var0 \in FinNat : (Fluent16_5[var0]) => (Fluent15_5[var0])
/\ \A var0 \in Server : \A var1 \in FinNat : (Fluent19_3[var0][var1]) => (Fluent20_3[var0][var1])
/\ \A var0 \in Server : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent31_1[var0][var2]) => (var1 = var2)

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
/\ Fluent35_3' = [Fluent35_3 EXCEPT ![i] = FALSE]
/\ Fluent19_3' = [Fluent19_3 EXCEPT ![i][curTerm] = TRUE]
/\ Fluent31_1' = [Fluent31_1 EXCEPT ![i][curTerm] = TRUE]
/\ UNCHANGED<<Fluent36_3, Fluent34_3, Fluent28_2, Fluent37_3, Fluent16_5, Fluent29_2, Fluent15_5, Fluent20_3>>
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
/\ Fluent35_3' = [Fluent35_3 EXCEPT ![i] = TRUE]
/\ Fluent34_3' = [Fluent34_3 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent36_3, Fluent28_2, Fluent37_3, Fluent16_5, Fluent29_2, Fluent15_5, Fluent19_3, Fluent31_1, Fluent20_3>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

RollbackEntries(i,j) ==
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED<<Fluent35_3, Fluent36_3, Fluent34_3, Fluent28_2, Fluent37_3, Fluent16_5, Fluent29_2, Fluent15_5, Fluent19_3, Fluent31_1, Fluent20_3>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

BecomeLeader(i,newTerm) ==
/\ (\E voteQuorum \in Quorums : ((i \in voteQuorum) /\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm)) /\ UNCHANGED <<log>>))
/\ Fluent36_3' = [Fluent36_3 EXCEPT ![i] = TRUE]
/\ Fluent34_3' = [Fluent34_3 EXCEPT ![i] = FALSE]
/\ Fluent28_2' = [Fluent28_2 EXCEPT ![newTerm] = TRUE]
/\ Fluent16_5' = [x0 \in FinNat |-> FALSE]
/\ Fluent29_2' = [[x0 \in FinNat |-> TRUE] EXCEPT ![newTerm] = FALSE]
/\ Fluent15_5' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ Fluent31_1' = [Fluent31_1 EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ Fluent20_3' = [Fluent20_3 EXCEPT ![i][newTerm] = TRUE]
/\ UNCHANGED<<Fluent35_3, Fluent37_3, Fluent19_3>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

CommitEntry(i,ind,curTerm) ==
/\ (\E commitQuorum \in Quorums : (ind = Len(log[i]) /\ ind > 0 /\ log[i][ind] = curTerm /\ (\A s \in commitQuorum : (Len(log[s]) >= ind /\ InLog(<<ind,curTerm>>,s))) /\ UNCHANGED <<log>>))
/\ Fluent37_3' = [Fluent37_3 EXCEPT ![i] = TRUE]
/\ Fluent16_5' = [Fluent16_5 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent35_3, Fluent36_3, Fluent34_3, Fluent28_2, Fluent29_2, Fluent15_5, Fluent19_3, Fluent31_1, Fluent20_3>>
/\ CandSep'
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ UNCHANGED<<>>
/\ CandSep'

Init ==
/\ log = [i \in Server |-> <<>>]
/\ Fluent35_3 = [ x0 \in Server |-> FALSE]
/\ Fluent36_3 = [ x0 \in Server |-> FALSE]
/\ Fluent34_3 = [ x0 \in Server |-> FALSE]
/\ Fluent28_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent37_3 = [ x0 \in Server |-> FALSE]
/\ Fluent16_5 = [ x0 \in FinNat |-> FALSE]
/\ Fluent29_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent15_5 = [ x0 \in FinNat |-> FALSE]
/\ Fluent19_3 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent31_1 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent20_3 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent2 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s,t \in Server : GetEntries(s,t))
\/ (\E s,t \in Server : RollbackEntries(s,t))
\/ (\E s \in Server : (\E newTerm \in FinNat : BecomeLeader(s,newTerm)))
\/ (\E s \in Server : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,ind,curTerm))))

Spec == (Init /\ [][Next]_vars)

Safety ==
/\ \A var0 \in FinNat : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent2[var0][var2]) => (var2 = var1)
=============================================================================
