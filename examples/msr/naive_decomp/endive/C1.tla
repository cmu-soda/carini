--------------------------- MODULE C1 ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES committed, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0

vars == <<committed, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>

CandSep ==
/\ \A var0 \in FinNat : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent4[var0][var2]) => (var1 = var2)

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
/\ Fluent3' = [Fluent3 EXCEPT ![newTerm] = FALSE]
/\ Fluent1' = [Fluent1 EXCEPT ![newTerm] = FALSE]
/\ UNCHANGED<<Fluent2, Fluent0, Fluent4>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ ind > 0
/\ ~((\E c \in committed : c.entry = <<ind,curTerm>>))
/\ committed' = (committed \cup {[entry |-> <<ind,curTerm>>,term |-> curTerm]})
/\ Fluent2' = [Fluent2 EXCEPT ![curTerm] = FALSE]
/\ Fluent0' = [Fluent0 EXCEPT ![ind][curTerm] = FALSE]
/\ Fluent4' = [Fluent4 EXCEPT ![ind][curTerm] = TRUE]
/\ UNCHANGED<<Fluent3, Fluent1>>
/\ CandSep'

Init ==
/\ committed = {}
/\ Fluent3 = [ x0 \in FinNat |-> TRUE]
/\ Fluent2 = [ x0 \in FinNat |-> TRUE]
/\ Fluent1 = [ x0 \in FinNat |-> TRUE]
/\ Fluent0 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> TRUE]]
/\ Fluent4 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]

Next ==
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)))))

Spec == (Init /\ [][Next]_vars)

StateMachineSafety == (\A c1,c2 \in committed : (c1.entry[1] = c2.entry[1] => c1 = c2))
=============================================================================
