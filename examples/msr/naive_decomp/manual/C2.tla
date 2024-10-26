--------------------------- MODULE C2 ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

VARIABLES currentTerm
VARIABLES FluentCommitInd, FluentCommitIndTerm

CONSTANTS Server, Quorums, FinNat

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

vars == <<currentTerm, FluentCommitInd, FluentCommitIndTerm>>

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
/\ UNCHANGED <<FluentCommitInd, FluentCommitIndTerm>>

BecomeLeader(i,voteQuorum,newTerm) ==
/\ newTerm = (currentTerm[i] + 1)
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]]
/\ UNCHANGED <<FluentCommitInd, FluentCommitIndTerm>>

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ FluentCommitIndTerm' = [FluentCommitIndTerm EXCEPT![ind][curTerm] = TRUE]
/\ FluentCommitInd' = [FluentCommitInd EXCEPT![ind] = TRUE]
/\ curTerm = currentTerm[i]
/\ ind > 0
/\ UNCHANGED <<currentTerm>>

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<FluentCommitInd, FluentCommitIndTerm>>

Init ==
/\ currentTerm = [i \in Server |-> 0]
/\ FluentCommitInd = [x0 \in FinNat |-> FALSE]
/\ FluentCommitIndTerm = [ x0 \in FinNat |-> [x1 \in FinNat |-> FALSE]]

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)))))
\/ (\E s,t \in Server : UpdateTerms(s,t))

Spec == (Init /\ [][Next]_vars)

Safety ==
/\ \A i \in FinNat : \A t1,t2 \in FinNat : FluentCommitInd[i] => (FluentCommitIndTerm[i][t1] => (FluentCommitIndTerm[i][t2] => t1=t2))
=============================================================================
