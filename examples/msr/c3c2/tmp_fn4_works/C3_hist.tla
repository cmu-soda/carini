--------------------------- MODULE C3_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent32_15, log, Fluent40_2, Fluent2, Fluent33_15, Fluent17_11, Fluent18_11, Fluent39_2, Fluent25_13, Fluent8_4, Fluent7_4, Fluent26_13, Fluent27_16, Fluent28_16

vars == <<Fluent32_15, log, Fluent40_2, Fluent2, Fluent33_15, Fluent17_11, Fluent18_11, Fluent39_2, Fluent25_13, Fluent8_4, Fluent7_4, Fluent26_13, Fluent27_16, Fluent28_16>>

CandSep ==
/\ \A var0 \in FinNat : (Fluent39_2[var0]) => (~(Fluent40_2[var0]))
/\ \A var0 \in FinNat : \A var1 \in Server : (Fluent28_16[var0][var1]) => (Fluent27_16[var0][var1])
/\ \A var0 \in FinNat : \A var1 \in FinNat : (~(Fluent25_13[var0])) => ((Fluent26_13[var1]) => (var1 <= var0))
/\ \A var0 \in Server : (Fluent17_11[var0]) => (Fluent18_11[var0])
/\ \A var0 \in FinNat : (Fluent32_15[var0]) => (Fluent33_15[var0])
/\ \A var0 \in FinNat : (Fluent7_4[var0]) => (Fluent8_4[var0])

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
/\ Fluent32_15' = [Fluent32_15 EXCEPT ![curTerm] = TRUE]
/\ Fluent28_16' = [Fluent28_16 EXCEPT ![curTerm][i] = TRUE]
/\ Fluent33_15' = [x0 \in FinNat |-> TRUE]
/\ UNCHANGED<<Fluent17_11, Fluent18_11, Fluent39_2, Fluent40_2, Fluent25_13, Fluent8_4, Fluent7_4, Fluent26_13, Fluent27_16>>
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
/\ UNCHANGED<<Fluent32_15, Fluent17_11, Fluent18_11, Fluent39_2, Fluent40_2, Fluent25_13, Fluent8_4, Fluent7_4, Fluent26_13, Fluent27_16, Fluent28_16, Fluent33_15>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

RollbackEntries(i,j) ==
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED<<Fluent32_15, Fluent17_11, Fluent18_11, Fluent39_2, Fluent40_2, Fluent25_13, Fluent8_4, Fluent7_4, Fluent26_13, Fluent27_16, Fluent28_16, Fluent33_15>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ UNCHANGED <<log>>
/\ Fluent17_11' = [[x0 \in Server |-> FALSE] EXCEPT ![i] = TRUE]
/\ Fluent18_11' = [[x0 \in Server |-> FALSE] EXCEPT ![i] = TRUE]
/\ Fluent39_2' = [[x0 \in FinNat |-> TRUE] EXCEPT ![newTerm] = FALSE]
/\ Fluent40_2' = [x0 \in FinNat |-> FALSE]
/\ Fluent25_13' = [[x0 \in FinNat |-> TRUE] EXCEPT ![newTerm] = FALSE]
/\ Fluent8_4' = [Fluent8_4 EXCEPT ![newTerm] = TRUE]
/\ Fluent26_13' = [Fluent26_13 EXCEPT ![newTerm] = TRUE]
/\ Fluent27_16' = [Fluent27_16 EXCEPT ![newTerm][i] = TRUE]
/\ Fluent33_15' = [Fluent33_15 EXCEPT ![newTerm] = FALSE]
/\ UNCHANGED<<Fluent32_15, Fluent7_4, Fluent28_16>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm,minQTerm) ==
/\ ind = Len(log[i])
/\ ind > 0
/\ log[i][ind] = curTerm
/\ (\A s \in commitQuorum : (Len(log[s]) >= ind /\ InLog(<<ind,curTerm>>,s)))
/\ UNCHANGED <<log>>
/\ Fluent17_11' = [Fluent17_11 EXCEPT ![i] = TRUE]
/\ Fluent40_2' = [Fluent40_2 EXCEPT ![curTerm] = TRUE]
/\ Fluent7_4' = [Fluent7_4 EXCEPT ![minQTerm] = TRUE]
/\ UNCHANGED<<Fluent32_15, Fluent18_11, Fluent39_2, Fluent25_13, Fluent8_4, Fluent26_13, Fluent27_16, Fluent28_16, Fluent33_15>>
/\ CandSep'
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ UNCHANGED<<>>
/\ CandSep'

Init ==
/\ log = [i \in Server |-> <<>>]
/\ Fluent32_15 = [ x0 \in FinNat |-> FALSE]
/\ Fluent17_11 = [ x0 \in Server |-> FALSE]
/\ Fluent18_11 = [ x0 \in Server |-> FALSE]
/\ Fluent39_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent40_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent25_13 = [ x0 \in FinNat |-> FALSE]
/\ Fluent8_4 = [ x0 \in FinNat |-> FALSE]
/\ Fluent7_4 = [ x0 \in FinNat |-> FALSE]
/\ Fluent26_13 = [ x0 \in FinNat |-> FALSE]
/\ Fluent27_16 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent28_16 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent33_15 = [ x0 \in FinNat |-> FALSE]
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
