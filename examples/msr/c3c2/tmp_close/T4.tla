--------------------------- MODULE T4 ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

VARIABLES config

CONSTANTS Server, Quorums, FinNat

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

vars == <<config>>

Empty(s) == Len(s) = 0

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

IsPrefix(s,t) == (Len(s) <= Len(t) /\ SubSeq(s,1,Len(s)) = SubSeq(t,1,Len(s)))

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ UNCHANGED <<config>>

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ ind > 0
/\ UNCHANGED <<config>>

Init ==
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))

Next ==
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)))))

Spec == (Init /\ [][Next]_vars)
=============================================================================
