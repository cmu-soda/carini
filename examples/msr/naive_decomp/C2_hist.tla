--------------------------- MODULE C2_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent9, currentTerm, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0

vars == <<Fluent9, currentTerm, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>

CandSep ==
/\ \A var0 \in Server : (Fluent3[var0]) => (Fluent4[var0])
/\ \A var0 \in FinNat : (Fluent5[var0][var0]) => (Fluent6[var0])
/\ \A var0 \in FinNat : (Fluent7[var0]) => (Fluent8[var0])
/\ \A var0 \in Server : (Fluent9[var0]) => (Fluent10[var0])

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

Empty(s) == Len(s) = 0

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

IsPrefix(s,t) == (Len(s) <= Len(t) /\ SubSeq(s,1,Len(s)) = SubSeq(t,1,Len(s)))

CanVoteForOplog(i,j,term) ==
/\ currentTerm[i] < term

UpdateTermsExpr(i,j) ==
/\ currentTerm[i] > currentTerm[j]
/\ currentTerm' = [currentTerm EXCEPT![j] = currentTerm[i]]

ClientRequest(i,curTerm) ==
/\ currentTerm[i] = curTerm
/\ UNCHANGED <<currentTerm>>
/\ Fluent9' = [Fluent9 EXCEPT ![i] = TRUE]
/\ Fluent8' = [Fluent8 EXCEPT ![curTerm] = TRUE]
/\ Fluent6' = [Fluent6 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent7, Fluent5, Fluent10, Fluent4, Fluent3>>
/\ CandSep'
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ CandSep'

BecomeLeader(i,voteQuorum,newTerm) ==
/\ newTerm = (currentTerm[i] + 1)
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]]
/\ Fluent10' = [Fluent10 EXCEPT ![i] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent3>>
/\ CandSep'
/\ Fluent1' = [Fluent1 EXCEPT ![newTerm] = TRUE]
/\ UNCHANGED<<Fluent2, Fluent0>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ curTerm = currentTerm[i]
/\ ind > 0
/\ UNCHANGED <<currentTerm>>
/\ Fluent7' = [Fluent7 EXCEPT ![curTerm] = TRUE]
/\ Fluent5' = [Fluent5 EXCEPT ![ind][curTerm] = TRUE]
/\ Fluent3' = [Fluent3 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent9, Fluent8, Fluent6, Fluent10, Fluent4>>
/\ CandSep'
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent1>>
/\ CandSep'

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED<<Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3>>
/\ CandSep'
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ CandSep'

Init ==
/\ currentTerm = [i \in Server |-> 0]
/\ Fluent9 = [ x0 \in Server |-> FALSE]
/\ Fluent8 = [ x0 \in FinNat |-> FALSE]
/\ Fluent7 = [ x0 \in FinNat |-> FALSE]
/\ Fluent6 = [ x0 \in FinNat |-> FALSE]
/\ Fluent5 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent10 = [ x0 \in Server |-> FALSE]
/\ Fluent4 = [ x0 \in Server |-> FALSE]
/\ Fluent3 = [ x0 \in Server |-> FALSE]
/\ Fluent2 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent1 = [ x0 \in FinNat |-> FALSE]
/\ Fluent0 = [ x0 \in FinNat |-> FALSE]

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)))))
\/ (\E s,t \in Server : UpdateTerms(s,t))

Spec == (Init /\ [][Next]_vars)

Safety ==
/\ \A var0 \in FinNat : (Fluent0[var0]) => (Fluent1[var0])
/\ \A var0 \in FinNat : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent2[var0][var2]) => (var2 = var1)
=============================================================================
