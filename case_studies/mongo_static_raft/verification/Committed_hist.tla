--------------------------- MODULE Committed_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES committed, Fluent21_2

vars == <<committed, Fluent21_2>>

CandSep ==
/\ \A var0 \in FinNat : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent21_2[var2][var0]) => (var1 = var2)

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

StateConstraint == TRUE

Empty(s) == Len(s) = 0

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

IsPrefix(s,t) == (Len(s) <= Len(t) /\ SubSeq(s,1,Len(s)) = SubSeq(t,1,Len(s)))

BecomeLeader(i,newTerm) ==
/\ (\E voteQuorum \in Quorums : ((i \in voteQuorum) /\ UNCHANGED <<committed>>))
/\ UNCHANGED<<Fluent21_2>>
/\ CandSep'

CommitEntry(i,ind,curTerm) ==
/\ (\E commmitQuorum \in Quorums : (ind > 0 /\ ~((\E c \in committed : c.entry = <<ind,curTerm>>)) /\ committed' = (committed \cup {[entry |-> <<ind,curTerm>>,term |-> curTerm]})))
/\ Fluent21_2' = [Fluent21_2 EXCEPT ![curTerm][ind] = TRUE]
/\ UNCHANGED<<>>
/\ CandSep'

Init ==
/\ committed = {}
/\ Fluent21_2 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]

Next ==
\/ (\E s \in Server : (\E newTerm \in FinNat : BecomeLeader(s,newTerm)))
\/ (\E s \in Server : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,ind,curTerm))))

Spec == (Init /\ [][Next]_vars)

StateMachineSafety == (\A c1,c2 \in committed : (c1.entry[1] = c2.entry[1] => c1 = c2))
=============================================================================
