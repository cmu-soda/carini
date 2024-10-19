--------------------------- MODULE C1_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES committed, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0

vars == <<committed, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>

CandSep ==
/\ \A var0 \in Server : (Fluent1[var0]) => (Fluent0[var0])
/\ \A var0 \in FinNat : (Fluent2[var0][var0]) => (Fluent3[var0])
/\ \A var0 \in Server : \A var1 \in Server : \A var2 \in FinNat : (Fluent4[var2]) => (Fluent5[var2][var0])
/\ \A var0 \in FinNat : \E var1 \in Quorums : \A var2 \in FinNat : (Fluent7[var2][var0]) => (Fluent6[var1][var2])
/\ \A var0 \in FinNat : \A var1 \in FinNat : (Fluent9[var1][var0]) => ((Fluent10[var0][var1]) => (Fluent8[var0][var0]))

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
/\ Fluent4' = [Fluent4 EXCEPT![newTerm] = FALSE]
/\ Fluent3' = [Fluent3 EXCEPT![newTerm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT![i] = TRUE]
/\ UNCHANGED<<Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent2, Fluent1>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ ind > 0
/\ ~((\E c \in committed : c.entry = <<ind,curTerm>>))
/\ committed' = (committed \cup {[entry |-> <<ind,curTerm>>,term |-> curTerm]})
/\ Fluent9' = [Fluent9 EXCEPT![curTerm][ind] = TRUE]
/\ Fluent8' = [Fluent8 EXCEPT![curTerm][ind] = FALSE]
/\ Fluent7' = [Fluent7 EXCEPT![curTerm][ind] = TRUE]
/\ Fluent6' = [Fluent6 EXCEPT![commitQuorum][curTerm] = TRUE]
/\ Fluent5' = [Fluent5 EXCEPT![curTerm][i] = FALSE]
/\ Fluent10' = [Fluent10 EXCEPT![curTerm][ind] = FALSE]
/\ Fluent2' = [Fluent2 EXCEPT![ind][curTerm] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT![i] = TRUE]
/\ UNCHANGED<<Fluent4, Fluent3, Fluent0>>
/\ CandSep'

Init ==
/\ committed = {}
/\ Fluent9 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent8 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> TRUE]]
/\ Fluent7 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent6 = [ x0 \in Quorums |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent5 = [ x0 \in FinNat |-> [ x1 \in Server |-> TRUE]]
/\ Fluent10 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> TRUE]]
/\ Fluent4 = [ x0 \in FinNat |-> TRUE]
/\ Fluent3 = [ x0 \in FinNat |-> FALSE]
/\ Fluent2 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent1 = [ x0 \in Server |-> FALSE]
/\ Fluent0 = [ x0 \in Server |-> FALSE]

Next ==
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)))))

Spec == (Init /\ [][Next]_vars)

StateMachineSafety == (\A c1,c2 \in committed : (c1.entry[1] = c2.entry[1] => c1 = c2))
=============================================================================
