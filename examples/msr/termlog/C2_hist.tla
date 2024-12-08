--------------------------- MODULE C2_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent11, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, currentTerm

vars == <<Fluent11, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, currentTerm>>

CandSep ==
/\ \A var0 \in Server : (Fluent3[var0]) => (Fluent4[var0])
/\ \A var0 \in Server : (Fluent5[var0]) => (Fluent6[var0])
/\ \A var0 \in Server : (Fluent8[var0]) => (Fluent7[var0])
/\ \A var0 \in FinNat : (Fluent9[var0]) => (Fluent10[var0])
/\ \A var0 \in FinNat : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent11[var2][var0]) => (var1 = var2)

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
/\ Fluent8' = [Fluent8 EXCEPT ![i] = FALSE]
/\ Fluent6' = [Fluent6 EXCEPT ![i] = TRUE]
/\ Fluent10' = [Fluent10 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent9, Fluent7, Fluent5, Fluent4, Fluent3>>
/\ CandSep'
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ CandSep'

BecomeLeader(i,voteQuorum,newTerm) ==
/\ newTerm = (currentTerm[i] + 1)
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]]
/\ Fluent8' = [Fluent8 EXCEPT ![i] = TRUE]
/\ Fluent7' = [Fluent7 EXCEPT ![i] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent11, Fluent9, Fluent6, Fluent5, Fluent10, Fluent3>>
/\ CandSep'
/\ Fluent1' = [Fluent1 EXCEPT ![newTerm] = TRUE]
/\ UNCHANGED<<Fluent2, Fluent0>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ curTerm = currentTerm[i]
/\ ind > 0
/\ UNCHANGED <<currentTerm>>
/\ Fluent11' = [Fluent11 EXCEPT ![curTerm][ind] = TRUE]
/\ Fluent9' = [Fluent9 EXCEPT ![curTerm] = TRUE]
/\ Fluent7' = [Fluent7 EXCEPT ![i] = FALSE]
/\ Fluent5' = [Fluent5 EXCEPT ![i] = TRUE]
/\ Fluent3' = [Fluent3 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent8, Fluent6, Fluent10, Fluent4>>
/\ CandSep'
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent1>>
/\ CandSep'

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED<<Fluent11, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3>>
/\ CandSep'
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ CandSep'

Init ==
/\ currentTerm = [i \in Server |-> 0]
/\ Fluent11 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent9 = [ x0 \in FinNat |-> FALSE]
/\ Fluent8 = [ x0 \in Server |-> FALSE]
/\ Fluent7 = [ x0 \in Server |-> FALSE]
/\ Fluent6 = [ x0 \in Server |-> FALSE]
/\ Fluent5 = [ x0 \in Server |-> FALSE]
/\ Fluent10 = [ x0 \in FinNat |-> FALSE]
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