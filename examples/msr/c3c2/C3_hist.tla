--------------------------- MODULE C3_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent37_1, Fluent35_3, Fluent14_0, Fluent36_1, Fluent34_3, Fluent27_3, log, Fluent26_3, Fluent2, Fluent22_2, Fluent13_0, Fluent21_2

vars == <<Fluent37_1, Fluent35_3, Fluent14_0, Fluent36_1, Fluent34_3, Fluent27_3, log, Fluent26_3, Fluent2, Fluent22_2, Fluent13_0, Fluent21_2>>

CandSep ==
/\ \A var0 \in FinNat : \A var1 \in FinNat : (~(Fluent22_2[var0])) => ((Fluent21_2[var1]) => (var1 <= var0))
/\ \A var0 \in Server : \A var1 \in FinNat : (Fluent36_1[var1][var0]) => (~(Fluent37_1[var1][var0]))
/\ \A var0 \in Server : (Fluent26_3[var0]) => (Fluent27_3[var0])
/\ \A var0 \in FinNat : (Fluent13_0[var0]) => (Fluent14_0[var0])
/\ \A var0 \in Server : \A var1 \in FinNat : (Fluent34_3[var0][var1]) => (Fluent35_3[var0][var1])

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
/\ Fluent34_3' = [Fluent34_3 EXCEPT ![i][curTerm] = TRUE]
/\ Fluent27_3' = [Fluent27_3 EXCEPT ![i] = FALSE]
/\ UNCHANGED<<Fluent37_1, Fluent35_3, Fluent14_0, Fluent36_1, Fluent26_3, Fluent22_2, Fluent13_0, Fluent21_2>>
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
/\ Fluent27_3' = [Fluent27_3 EXCEPT ![i] = TRUE]
/\ Fluent26_3' = [Fluent26_3 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent37_1, Fluent35_3, Fluent14_0, Fluent36_1, Fluent34_3, Fluent22_2, Fluent13_0, Fluent21_2>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

RollbackEntries(i,j) ==
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED<<Fluent37_1, Fluent35_3, Fluent14_0, Fluent36_1, Fluent34_3, Fluent27_3, Fluent26_3, Fluent22_2, Fluent13_0, Fluent21_2>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

BecomeLeader(i,newTerm) ==
/\ (\E voteQuorum \in Quorums : ((i \in voteQuorum) /\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm)) /\ UNCHANGED <<log>>))
/\ Fluent37_1' = [Fluent37_1 EXCEPT ![newTerm][i] = TRUE]
/\ Fluent35_3' = [[Fluent35_3 EXCEPT ![i] = [x0 \in FinNat |-> FALSE]] EXCEPT ![i][newTerm] = TRUE]
/\ Fluent14_0' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ Fluent36_1' = [[Fluent36_1 EXCEPT ![newTerm] = [x0 \in Server |-> TRUE]] EXCEPT ![newTerm][i] = FALSE]
/\ Fluent34_3' = [Fluent34_3 EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ Fluent26_3' = [Fluent26_3 EXCEPT ![i] = FALSE]
/\ Fluent22_2' = [[x0 \in FinNat |-> TRUE] EXCEPT ![newTerm] = FALSE]
/\ Fluent13_0' = [x0 \in FinNat |-> FALSE]
/\ Fluent21_2' = [Fluent21_2 EXCEPT ![newTerm] = TRUE]
/\ UNCHANGED<<Fluent27_3>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

CommitEntry(i,ind,curTerm) ==
/\ (\E commitQuorum \in Quorums : (ind = Len(log[i]) /\ ind > 0 /\ log[i][ind] = curTerm /\ (\A s \in commitQuorum : (Len(log[s]) >= ind /\ InLog(<<ind,curTerm>>,s))) /\ UNCHANGED <<log>>))
/\ Fluent13_0' = [Fluent13_0 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent37_1, Fluent35_3, Fluent14_0, Fluent36_1, Fluent34_3, Fluent27_3, Fluent26_3, Fluent22_2, Fluent21_2>>
/\ CandSep'
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ UNCHANGED<<>>
/\ CandSep'

Init ==
/\ log = [i \in Server |-> <<>>]
/\ Fluent37_1 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent35_3 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent14_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent36_1 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent34_3 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent27_3 = [ x0 \in Server |-> FALSE]
/\ Fluent26_3 = [ x0 \in Server |-> FALSE]
/\ Fluent22_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent13_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent21_2 = [ x0 \in FinNat |-> FALSE]
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
