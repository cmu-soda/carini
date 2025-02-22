--------------------------- MODULE C3 ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, Randomization

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent28_24, log, Fluent20_2, Fluent21_2, Fluent2, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6

vars == <<Fluent28_24, log, Fluent20_2, Fluent21_2, Fluent2, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6>>

Symmetry == Permutations(Server)
NextUnchanged == UNCHANGED vars

CandSep ==
/\ \A var0 \in FinNat : \A var1 \in FinNat : (Fluent17_6[var0]) => ((Fluent16_6[var1]) => (var0 <= var1))
/\ \A var0 \in FinNat : \A var1 \in Server : (Fluent18_2[var0][var1]) => (Fluent19_2[var0][var1])
/\ \A var0 \in FinNat : (Fluent20_2[var0]) => (Fluent21_2[var0])
/\ \A var0 \in FinNat : \E var1 \in Quorums : \A var2 \in Quorums : (Fluent28_24[var0][var2]) => (var2 = var1)

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

StateConstraint == (\A s \in Server : Len(log[s]) < 3)

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
/\ Fluent18_2' = [Fluent18_2 EXCEPT ![curTerm][i] = TRUE]
/\ UNCHANGED<<Fluent28_24, Fluent20_2, Fluent21_2, Fluent19_2, Fluent17_6, Fluent16_6>>
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
/\ UNCHANGED<<Fluent28_24, Fluent20_2, Fluent21_2, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

RollbackEntries(i,j) ==
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED<<Fluent28_24, Fluent20_2, Fluent21_2, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6>>
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
/\ Fluent19_2' = [Fluent19_2 EXCEPT ![newTerm][i] = TRUE]
/\ Fluent17_6' = [Fluent17_6 EXCEPT ![newTerm] = TRUE]
/\ Fluent16_6' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ UNCHANGED<<Fluent18_2>>
/\ CandSep'
/\ UNCHANGED<<Fluent2>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm,minQTerm) ==
/\ ind = Len(log[i])
/\ ind > 0
/\ log[i][ind] = curTerm
/\ (\A s \in commitQuorum : (Len(log[s]) >= ind /\ InLog(<<ind,curTerm>>,s)))
/\ UNCHANGED <<log>>
/\ Fluent20_2' = [Fluent20_2 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent28_24, Fluent21_2, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6>>
/\ CandSep'
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ UNCHANGED<<>>
/\ CandSep'

Init ==
/\ log = [i \in Server |-> <<>>]
/\ Fluent28_24 = [ x0 \in FinNat |-> [ x1 \in Quorums |-> FALSE]]
/\ Fluent20_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent21_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent19_2 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent18_2 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent17_6 = [ x0 \in FinNat |-> FALSE]
/\ Fluent16_6 = [ x0 \in FinNat |-> FALSE]
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


TypeOK ==
/\ log         \in [Server -> Seq(FinNat)]
/\ Fluent28_24 \in [FinNat -> [Quorums -> BOOLEAN]]
/\ Fluent20_2  \in [FinNat -> BOOLEAN]
/\ Fluent21_2  \in [FinNat -> BOOLEAN]
/\ Fluent19_2  \in [FinNat -> [Server -> BOOLEAN]]
/\ Fluent18_2  \in [FinNat -> [Server -> BOOLEAN]]
/\ Fluent17_6  \in [FinNat -> BOOLEAN]
/\ Fluent16_6  \in [FinNat -> BOOLEAN]
/\ Fluent2     \in [FinNat -> [FinNat -> BOOLEAN]]

FinSeq(S) == UNION {[1..n -> S] : n \in FinNat}

TypeOKRand ==
/\ log         \in RandomSubset(9, [Server -> FinSeq(FinNat)])
/\ Fluent28_24 \in RandomSubset(9, [FinNat -> [Quorums -> BOOLEAN]])
/\ Fluent20_2  \in RandomSubset(8, [FinNat -> BOOLEAN])
/\ Fluent21_2  \in RandomSubset(8, [FinNat -> BOOLEAN])
/\ Fluent19_2  \in RandomSubset(8, [FinNat -> [Server -> BOOLEAN]])
/\ Fluent18_2  \in RandomSubset(8, [FinNat -> [Server -> BOOLEAN]])
/\ Fluent17_6  \in RandomSubset(8, [FinNat -> BOOLEAN])
/\ Fluent16_6  \in RandomSubset(8, [FinNat -> BOOLEAN])
/\ Fluent2     \in RandomSubset(8, [FinNat -> [FinNat -> BOOLEAN]])
(*
TypeOKRand ==
/\ log         \in RandomSubset(13, [Server -> FinSeq(FinNat)])
/\ Fluent28_24 \in RandomSubset(13, [FinNat -> [Quorums -> BOOLEAN]])
/\ Fluent20_2  \in RandomSubset(11, [FinNat -> BOOLEAN])
/\ Fluent21_2  \in RandomSubset(11, [FinNat -> BOOLEAN])
/\ Fluent19_2  \in RandomSubset(11, [FinNat -> [Server -> BOOLEAN]])
/\ Fluent18_2  \in RandomSubset(11, [FinNat -> [Server -> BOOLEAN]])
/\ Fluent17_6  \in RandomSubset(11, [FinNat -> BOOLEAN])
/\ Fluent16_6  \in RandomSubset(11, [FinNat -> BOOLEAN])
/\ Fluent2     \in RandomSubset(11, [FinNat -> [FinNat -> BOOLEAN]])
*)


IndInv ==
    /\ TypeOK
    /\ Safety
    /\ CandSep
    (*
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (t4 \in DOMAIN log[s2] => log[s2][t4] = t2) \/ (~(Fluent2[t1][t2]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : ~(Fluent21_2[t3]) \/ (~(t4 < t1))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (t4 \in DOMAIN log[s4] => log[s4][t4] = t3) \/ (~(t2 \in DOMAIN log[s3]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (t4 \in DOMAIN log[s4] => log[s4][t4] = t2) \/ (~(Fluent19_2[t4][s3]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (Fluent17_6[t1]) \/ (~(Fluent19_2[t1][s2]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : ~(Fluent19_2[t3][s2]) \/ (~(Fluent2[t4][t2]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (Len(log[s1]) > 0) \/ (~(Fluent18_2[t2][s1]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (Fluent19_2[t2][s4]) \/ ((t4 \in DOMAIN log[s4] => log[s4][t4] = t3))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (t4 \in DOMAIN log[s3] => log[s3][t4] = t1) \/ (~(Fluent18_2[t1][s1]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (CanVoteForOplog(s2,s4,t2)) \/ (~(Fluent19_2[t3][s4]) \/ (~(Fluent21_2[t4]))) \/ ((t1 < t3))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (Fluent19_2[t2][s3]) \/ (~(Fluent28_24[t2][q3]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (Fluent18_2[t3][s3]) \/ (~(Len(log[s3]) > 0))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (s2 = s4) \/ (~(t3 \in DOMAIN log[s3]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (Fluent28_24[t2][q2]) \/ (~(Fluent19_2[t2][s2]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : ~(Fluent19_2[t3][s4]) \/ (~(Fluent20_2[t4]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (Fluent21_2[t1]) \/ (~(Fluent2[t2][t1]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (CanVoteForOplog(s4,s2,t1)) \/ (~(Fluent19_2[t3][s4])) \/ (~(t1 \in DOMAIN log[s3]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : ~(Fluent2[t2][t1]) \/ (~(Len(log[s3]) > 0))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (Fluent21_2[t2]) \/ (~(Fluent16_6[t2]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (Fluent21_2[t4]) \/ (~(Fluent20_2[t4]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (Fluent16_6[t3]) \/ (~(Fluent17_6[t2]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (Fluent17_6[t4]) \/ (~(Fluent16_6[t4]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (Fluent19_2[t4][s1]) \/ (~(Fluent18_2[t4][s1]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : ~(CanVoteForOplog(s1,s2,t2)) \/ (~(Fluent19_2[t2][s4])) \/ (~(Len(log[s4]) = t3))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (Fluent18_2[t3][s1]) \/ (~(Fluent19_2[t2][s1])) \/ ((t2 \in DOMAIN log[s3] => log[s3][t2] = t1))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (t1 \in DOMAIN log[s3] => log[s3][t1] = t2) \/ (~(Fluent19_2[t3][s1])) \/ (~(t2 \in DOMAIN log[s3]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (CanVoteForOplog(s4,s2,t2)) \/ (~(Fluent18_2[t1][s2])) \/ ((t1 < t4))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (Fluent28_24[t2][q2]) \/ (~(Fluent17_6[t2]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (t1 \in DOMAIN log[s1]) \/ (~(Len(log[s4]) = t3)) \/ (~(Fluent19_2[t1][s1]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : ~(Fluent19_2[t4][s3]) \/ (~(Len(log[s3]) = t1))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : ~(Fluent20_2[t1]) \/ (~(t4 \in DOMAIN log[s3]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (Fluent2[t4][t2]) \/ ((Len(log[s4]) = t3)) \/ (~(Len(log[s3]) > 0)) \/ (~(Fluent19_2[t2][s1]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (s1 \in q1) \/ (~(t1 = t2)) \/ (~(Fluent19_2[t3][s1])) \/ (~(Fluent28_24[t1][q1]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (Fluent19_2[t4][s2]) \/ ((t4 \in DOMAIN log[s3] => log[s3][t4] = t1) \/ (~(Fluent19_2[t1][s2])))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : ~(Fluent17_6[t3]) \/ (~(s1 \in q1)) \/ (~(t4 \in DOMAIN log[s1])) \/ (~(Len(log[s3]) > 0))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (Fluent18_2[t2][s3]) \/ ((s4 \in q3)) \/ ((t1 < t3)) \/ (~(t2 \in DOMAIN log[s3])) \/ (~(Fluent28_24[t1][q1]))
    /\ \A s1,s2 \in Server : \A t1,t2 \in FinNat : \A q1 \in Quorums : \E s3 \in Server : \E t3 \in FinNat : \E q2 \in Quorums : \A s4 \in Server : \A t4 \in FinNat : \A q3 \in Quorums : (t3 = t4) \/ (~(CanVoteForOplog(s4,s1,t1))) \/ (~(t4 \in DOMAIN log[s4] => log[s4][t4] = t2)) \/ (~(Fluent18_2[t2][s4])) \/ (~(s4 \in q2))
    *)

IndInvRand == TypeOKRand /\ IndInv

IISpec == IndInvRand /\ [][Next]_vars

=============================================================================
