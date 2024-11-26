--------------------------- MODULE C1 ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

VARIABLES committed, FluentLeaderTerm, FluentCommitInfo, FluentCommitInd, FluentJustCommittedInd, FluentJustCommittedTerm, FluentCommitIdxTerm

CONSTANTS Server, Quorums, FinNat

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

vars == <<committed, FluentLeaderTerm, FluentCommitInfo, FluentCommitInd, FluentJustCommittedInd, FluentJustCommittedTerm, FluentCommitIdxTerm>>

CandSep ==
/\ \A i \in FinNat : FluentCommitInd[i] => \A t1,t2 \in FinNat : (FluentCommitIdxTerm[i][t1] /\ FluentCommitIdxTerm[i][t2]) => t1=t2

\* if a node n commits at term 'term' then it must have been elected leader in that term
\*/\ \A n \in Server : \A term \in FinNat : FluentCommitInfo[n][term] => FluentLeaderTerm[n][term]
\* right after a commit in term i, there must not exist a leader in a higher term j
\*/\ \A i \in FinNat : FluentJustCommittedTerm[i] => \A j \in FinNat : j > i => ~(\E n \in Server : FluentLeaderTerm[n][j])


\*/\ \A i \in FinNat : FluentJustCommittedInd[i] => \A j \in FinNat : j > i => ~FluentCommitInd[j]

\*/\ \A i \in FinNat : \E t \in FinNat : FluentCommitIdxTerm[i][t] => \A t2 \in FinNat : FluentCommitIdxTerm[i][t2] => t = t2

\*/\ \A i \in FinNat : FluentCommitInd[i] => \A j \in FinNat : j < i => FluentCommitInd[j]


Empty(s) == Len(s) = 0

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

IsPrefix(s,t) == (Len(s) <= Len(t) /\ SubSeq(s,1,Len(s)) = SubSeq(t,1,Len(s)))

BecomeLeader(i,voteQuorum,newTerm) ==
/\ FluentJustCommittedTerm' = [t \in FinNat |-> FALSE]
/\ FluentLeaderTerm' = [FluentLeaderTerm EXCEPT![i][newTerm] = TRUE]
/\ (i \in voteQuorum)
/\ UNCHANGED <<committed, FluentCommitInfo, FluentCommitInd, FluentJustCommittedInd, FluentCommitIdxTerm>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ FluentCommitIdxTerm' = [FluentCommitIdxTerm EXCEPT![ind][curTerm] = TRUE]
/\ FluentJustCommittedTerm' = [t \in FinNat |-> IF t = curTerm THEN TRUE ELSE FALSE]
/\ FluentJustCommittedInd' = [j \in FinNat |-> IF j = ind THEN TRUE ELSE FALSE]
/\ FluentCommitInfo' = [FluentCommitInfo EXCEPT![i][curTerm] = TRUE]
/\ FluentCommitInd' = [FluentCommitInd EXCEPT![ind] = TRUE]
/\ ind > 0
/\ ~((\E c \in committed : c.entry = <<ind,curTerm>>))
/\ committed' = (committed \cup {[entry |-> <<ind,curTerm>>,term |-> curTerm]})
/\ UNCHANGED <<FluentLeaderTerm>>
/\ CandSep'

Init ==
/\ committed = {}
/\ FluentLeaderTerm = [ x0 \in Server |-> [x1 \in FinNat |-> FALSE]]
/\ FluentCommitInfo = [ x0 \in Server |-> [x1 \in FinNat |-> FALSE]]
/\ FluentCommitInd = [x0 \in FinNat |-> FALSE]
/\ FluentJustCommittedInd = [x0 \in FinNat |-> FALSE]
/\ FluentJustCommittedTerm = [x0 \in FinNat |-> FALSE]
/\ FluentCommitIdxTerm = [ x0 \in FinNat |-> [x1 \in FinNat |-> FALSE]]

Next ==
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)))))

Spec == (Init /\ [][Next]_vars)

StateMachineSafety == (\A c1,c2 \in committed : (c1.entry[1] = c2.entry[1] => c1 = c2))
=============================================================================
