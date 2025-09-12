--------------------------- MODULE Log_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES log, Fluent40_1, Fluent45_0, Fluent42_3, Fluent46_0, Fluent52_4, Fluent51_4, Fluent41_3, Fluent21_2, Fluent33_5, Fluent55_6, Fluent32_5, Fluent39_1, Fluent56_6

vars == <<log, Fluent40_1, Fluent45_0, Fluent42_3, Fluent46_0, Fluent52_4, Fluent51_4, Fluent41_3, Fluent21_2, Fluent33_5, Fluent55_6, Fluent32_5, Fluent39_1, Fluent56_6>>

CandSep ==
/\ \A var0 \in Server : \A var1 \in FinNat : (Fluent39_1[var1][var0]) => (~(Fluent40_1[var1][var0]))
/\ \A var0 \in FinNat : (Fluent33_5[var0]) => (Fluent32_5[var0])
/\ \A var0 \in FinNat : \A var1 \in FinNat : (Fluent45_0[var0]) => ((Fluent46_0[var1]) => (var0 <= var1))
/\ \A var0 \in Server : (Fluent55_6[var0]) => (Fluent56_6[var0])
/\ \A var0 \in Server : \A var1 \in FinNat : (Fluent52_4[var0][var1]) => (Fluent51_4[var0][var1])
/\ \A var0 \in FinNat : \A var1 \in Server : (Fluent41_3[var0][var1]) => (Fluent42_3[var0][var1])

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
/\ Fluent56_6' = [Fluent56_6 EXCEPT ![i] = FALSE]
/\ Fluent51_4' = [Fluent51_4 EXCEPT ![i][curTerm] = FALSE]
/\ Fluent41_3' = [Fluent41_3 EXCEPT ![curTerm][i] = TRUE]
/\ UNCHANGED<<Fluent33_5, Fluent55_6, Fluent32_5, Fluent39_1, Fluent40_1, Fluent45_0, Fluent42_3, Fluent46_0, Fluent52_4>>
/\ CandSep'
/\ UNCHANGED<<Fluent21_2>>
/\ CandSep'

GetEntries(i,j) ==
/\ Len(log[j]) > Len(log[i])
/\ LET logOk == IF Empty(log[i]) THEN TRUE ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
  /\ logOk
  /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE (Len(log[i]) + 1)
      newEntry == log[j][newEntryIndex]
      newLog == Append(log[i],newEntry) IN
    /\ log' = [log EXCEPT![i] = newLog]
/\ Fluent55_6' = [Fluent55_6 EXCEPT ![i] = TRUE]
/\ Fluent56_6' = [Fluent56_6 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent33_5, Fluent32_5, Fluent39_1, Fluent40_1, Fluent45_0, Fluent42_3, Fluent46_0, Fluent52_4, Fluent51_4, Fluent41_3>>
/\ CandSep'
/\ UNCHANGED<<Fluent21_2>>
/\ CandSep'

RollbackEntries(i,j) ==
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED<<Fluent33_5, Fluent55_6, Fluent32_5, Fluent39_1, Fluent56_6, Fluent40_1, Fluent45_0, Fluent42_3, Fluent46_0, Fluent52_4, Fluent51_4, Fluent41_3>>
/\ CandSep'
/\ UNCHANGED<<Fluent21_2>>
/\ CandSep'

BecomeLeader(i,newTerm) ==
/\ (\E voteQuorum \in Quorums : ((i \in voteQuorum) /\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm)) /\ UNCHANGED <<log>>))
/\ Fluent33_5' = [x0 \in FinNat |-> FALSE]
/\ Fluent55_6' = [Fluent55_6 EXCEPT ![i] = FALSE]
/\ Fluent32_5' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ Fluent39_1' = [Fluent39_1 EXCEPT ![newTerm][i] = TRUE]
/\ Fluent40_1' = [[Fluent40_1 EXCEPT ![newTerm] = [x0 \in Server |-> TRUE]] EXCEPT ![newTerm][i] = FALSE]
/\ Fluent45_0' = [Fluent45_0 EXCEPT ![newTerm] = TRUE]
/\ Fluent42_3' = [Fluent42_3 EXCEPT ![newTerm][i] = TRUE]
/\ Fluent46_0' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ Fluent52_4' = [[Fluent52_4 EXCEPT ![i] = [x0 \in FinNat |-> TRUE]] EXCEPT ![i][newTerm] = FALSE]
/\ Fluent51_4' = [Fluent51_4 EXCEPT ![i] = [x0 \in FinNat |-> TRUE]]
/\ UNCHANGED<<Fluent56_6, Fluent41_3>>
/\ CandSep'
/\ UNCHANGED<<Fluent21_2>>
/\ CandSep'

CommitEntry(i,ind,curTerm) ==
/\ (\E commitQuorum \in Quorums : (ind = Len(log[i]) /\ ind > 0 /\ log[i][ind] = curTerm /\ (\A s \in commitQuorum : (Len(log[s]) >= ind /\ InLog(<<ind,curTerm>>,s))) /\ UNCHANGED <<log>>))
/\ Fluent33_5' = [Fluent33_5 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent55_6, Fluent32_5, Fluent39_1, Fluent56_6, Fluent40_1, Fluent45_0, Fluent42_3, Fluent46_0, Fluent52_4, Fluent51_4, Fluent41_3>>
/\ CandSep'
/\ Fluent21_2' = [Fluent21_2 EXCEPT ![curTerm][ind] = TRUE]
/\ UNCHANGED<<>>
/\ CandSep'

Init ==
/\ log = [i \in Server |-> <<>>]
/\ Fluent33_5 = [ x0 \in FinNat |-> FALSE]
/\ Fluent55_6 = [ x0 \in Server |-> FALSE]
/\ Fluent32_5 = [ x0 \in FinNat |-> FALSE]
/\ Fluent39_1 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent56_6 = [ x0 \in Server |-> FALSE]
/\ Fluent40_1 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent45_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent42_3 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent46_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent52_4 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent51_4 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent41_3 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent21_2 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s,t \in Server : GetEntries(s,t))
\/ (\E s,t \in Server : RollbackEntries(s,t))
\/ (\E s \in Server : (\E newTerm \in FinNat : BecomeLeader(s,newTerm)))
\/ (\E s \in Server : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,ind,curTerm))))

Spec == (Init /\ [][Next]_vars)

Safety ==
/\ \A var0 \in FinNat : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent21_2[var2][var0]) => (var1 = var2)
=============================================================================
