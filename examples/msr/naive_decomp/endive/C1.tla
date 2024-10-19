--------------------------- MODULE C1 ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent12, Fluent11, committed, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0

vars == <<Fluent12, Fluent11, committed, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>

CandSep ==
/\ \A var0 \in Server : (Fluent1[var0]) => (Fluent0[var0])
/\ \A var0 \in FinNat : (Fluent2[var0]) => (Fluent3[var0])
/\ \A var0 \in FinNat : \E var1 \in FinNat : \A var2 \in Quorums : (Fluent5[var0][var2][var1]) => (Fluent4[var0][var2])
/\ \A var0 \in FinNat : \A var1 \in FinNat : (Fluent6[var1][var0]) => ((Fluent8[var0][var0]) => (Fluent7[var0][var1]))
/\ \E var0 \in FinNat : Fluent9[var0]
/\ \A var0 \in FinNat : (Fluent10[var0][var0]) => ((Fluent12[var0]) => (Fluent11[var0]))

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

Empty(s) == Len(s) = 0

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

IsPrefix(s,t) == (Len(s) <= Len(t) /\ SubSeq(s,1,Len(s)) = SubSeq(t,1,Len(s)))

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ UNCHANGED <<committed>>
/\ Fluent9' = [Fluent9 EXCEPT![newTerm] = FALSE]
/\ Fluent2' = [Fluent2 EXCEPT![newTerm] = FALSE]
/\ Fluent1' = [Fluent1 EXCEPT![i] = FALSE]
/\ UNCHANGED<<Fluent12, Fluent11, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent0>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ ind > 0
/\ ~((\E c \in committed : c.entry = <<ind,curTerm>>))
/\ committed' = (committed \cup {[entry |-> <<ind,curTerm>>,term |-> curTerm]})
/\ Fluent12' = [Fluent12 EXCEPT![curTerm] = TRUE]
/\ Fluent11' = [Fluent11 EXCEPT![ind] = FALSE]
/\ Fluent9' = [Fluent9 EXCEPT![ind] = FALSE]
/\ Fluent8' = [Fluent8 EXCEPT![ind][curTerm] = TRUE]
/\ Fluent7' = [Fluent7 EXCEPT![ind][curTerm] = FALSE]
/\ Fluent6' = [Fluent6 EXCEPT![ind][curTerm] = FALSE]
/\ Fluent5' = [Fluent5 EXCEPT![ind][commitQuorum][curTerm] = FALSE]
/\ Fluent10' = [Fluent10 EXCEPT![curTerm][ind] = FALSE]
/\ Fluent4' = [Fluent4 EXCEPT![ind][commitQuorum] = FALSE]
/\ Fluent3' = [Fluent3 EXCEPT![curTerm] = FALSE]
/\ Fluent0' = [Fluent0 EXCEPT![i] = FALSE]
/\ UNCHANGED<<Fluent2, Fluent1>>
/\ CandSep'

Init ==
/\ committed = {}
/\ Fluent12 = [ x0 \in FinNat |-> FALSE]
/\ Fluent11 = [ x0 \in FinNat |-> TRUE]
/\ Fluent9 = [ x0 \in FinNat |-> TRUE]
/\ Fluent8 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent7 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> TRUE]]
/\ Fluent6 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> TRUE]]
/\ Fluent5 = [ x0 \in FinNat |-> [ x1 \in Quorums |-> [ x2 \in FinNat |-> TRUE]]]
/\ Fluent10 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> TRUE]]
/\ Fluent4 = [ x0 \in FinNat |-> [ x1 \in Quorums |-> TRUE]]
/\ Fluent3 = [ x0 \in FinNat |-> TRUE]
/\ Fluent2 = [ x0 \in FinNat |-> TRUE]
/\ Fluent1 = [ x0 \in Server |-> TRUE]
/\ Fluent0 = [ x0 \in Server |-> TRUE]

Next ==
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)))))

Spec == (Init /\ [][Next]_vars)

StateMachineSafety == (\A c1,c2 \in committed : (c1.entry[1] = c2.entry[1] => c1 = c2))
=============================================================================
