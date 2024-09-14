--------------------------- MODULE C1 ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES committed, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0

vars == <<committed, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>

CandSep ==
/\ \A var0 \in Server : (Fluent1[var0]) => (Fluent0[var0])
/\ \A var0 \in FinNat : (Fluent2[var0]) => (Fluent3[var0])
/\ (\E var0 \in FinNat : Fluent5[var0][var0]) => (\A var0 \in FinNat : (Fluent4[var0]) => (Fluent5[var0][var0]))
/\ \E var0 \in FinNat : \A var1 \in Server : Fluent6[var1][var0]
/\ \A var0 \in FinNat : (Fluent7[var0][var0]) => (\A var1 \in FinNat : (Fluent9[var1][var0]) => (Fluent8[var0][var1]))

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
/\ Fluent6' = [Fluent6 EXCEPT![i][newTerm] = FALSE]
/\ Fluent2' = [Fluent2 EXCEPT![newTerm] = FALSE]
/\ Fluent0' = [Fluent0 EXCEPT![i] = TRUE]
/\ UNCHANGED<<Fluent9, Fluent8, Fluent7, Fluent5, Fluent4, Fluent3, Fluent1>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ ind > 0
/\ ~((\E c \in committed : c.entry = <<ind,curTerm>>))
/\ committed' = (committed \cup {[entry |-> <<ind,curTerm>>,term |-> curTerm]})
/\ Fluent9' = [Fluent9 EXCEPT![curTerm][ind] = TRUE]
/\ Fluent8' = [Fluent8 EXCEPT![curTerm][ind] = TRUE]
/\ Fluent7' = [Fluent7 EXCEPT![curTerm][ind] = TRUE]
/\ Fluent6' = [Fluent6 EXCEPT![i][ind] = FALSE]
/\ Fluent5' = [Fluent5 EXCEPT![curTerm][ind] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT![curTerm] = TRUE]
/\ Fluent3' = [Fluent3 EXCEPT![curTerm] = FALSE]
/\ Fluent1' = [Fluent1 EXCEPT![i] = TRUE]
/\ UNCHANGED<<Fluent2, Fluent0>>
/\ CandSep'

Init ==
/\ committed = {}
/\ Fluent9 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent8 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent7 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent6 = [ x0 \in Server |-> [ x1 \in FinNat |-> TRUE]]
/\ Fluent5 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent4 = [ x0 \in FinNat |-> FALSE]
/\ Fluent3 = [ x0 \in FinNat |-> TRUE]
/\ Fluent2 = [ x0 \in FinNat |-> TRUE]
/\ Fluent1 = [ x0 \in Server |-> FALSE]
/\ Fluent0 = [ x0 \in Server |-> FALSE]

Next ==
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)))))

Spec == (Init /\ [][Next]_vars)

StateMachineSafety == (\A c1,c2 \in committed : (c1.entry[1] = c2.entry[1] => c1 = c2))
=============================================================================
