--------------------------- MODULE C1 ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

VARIABLES committed, FluentCommitInd, FluentCommitIndTerm

CONSTANTS Server, Quorums, FinNat

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

vars == <<committed, FluentCommitInd, FluentCommitIndTerm>>

CandSep ==
/\ \A i \in FinNat : \A t1,t2 \in FinNat : FluentCommitInd[i] => (FluentCommitIndTerm[i][t1] => (FluentCommitIndTerm[i][t2] => t1=t2))

\*/\ \A i \in FinNat : FluentCommitInd[i] => \A t1,t2 \in FinNat : (FluentCommitIndTerm[i][t1] /\ FluentCommitIndTerm[i][t2]) => t1=t2

Empty(s) == Len(s) = 0

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

IsPrefix(s,t) == (Len(s) <= Len(t) /\ SubSeq(s,1,Len(s)) = SubSeq(t,1,Len(s)))

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ UNCHANGED <<committed, FluentCommitInd, FluentCommitIndTerm>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ FluentCommitIndTerm' = [FluentCommitIndTerm EXCEPT![ind][curTerm] = TRUE]
/\ FluentCommitInd' = [FluentCommitInd EXCEPT![ind] = TRUE]
/\ ind > 0
/\ ~((\E c \in committed : c.entry = <<ind,curTerm>>))
/\ committed' = (committed \cup {[entry |-> <<ind,curTerm>>,term |-> curTerm]})
/\ CandSep'

Init ==
/\ committed = {}
/\ FluentCommitInd = [x0 \in FinNat |-> FALSE]
/\ FluentCommitIndTerm = [ x0 \in FinNat |-> [x1 \in FinNat |-> FALSE]]

Next ==
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)))))

Spec == (Init /\ [][Next]_vars)

StateMachineSafety == (\A c1,c2 \in committed : (c1.entry[1] = c2.entry[1] => c1 = c2))
=============================================================================
