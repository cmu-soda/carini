--------------------------- MODULE Term ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, Randomization

CONSTANTS Server, Quorums, FinNat

VARIABLES currentTerm, committedThisTerm, leaderAtTermServ, globalCurrentTerm, reqThisTerm, currentLeader

vars == <<currentTerm, committedThisTerm, leaderAtTermServ, globalCurrentTerm, reqThisTerm, currentLeader>>

Symmetry == Permutations(Server)
NextUnchanged == UNCHANGED vars

CanVoteForOplog(i,j,term) ==
/\ currentTerm[i] < term

UpdateTermsExpr(i,j) ==
/\ currentTerm[i] > currentTerm[j]
/\ currentTerm' = [currentTerm EXCEPT![j] = currentTerm[i]]
/\ UNCHANGED <<committedThisTerm, leaderAtTermServ, globalCurrentTerm, reqThisTerm, currentLeader>>

ClientRequest(i,curTerm) ==
/\ currentTerm[i] = curTerm
/\ UNCHANGED <<currentTerm>>
/\ reqThisTerm' = [reqThisTerm EXCEPT ![i][curTerm] = TRUE]
/\ UNCHANGED<<committedThisTerm, leaderAtTermServ, globalCurrentTerm, currentLeader>>

GetEntries(i,j) ==
/\ currentLeader' = [currentLeader EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ reqThisTerm' = [reqThisTerm EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ UNCHANGED <<currentTerm>>
/\ UNCHANGED<<committedThisTerm, leaderAtTermServ, globalCurrentTerm>>

RollbackEntries(i,j) ==
/\ currentLeader' = [currentLeader EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ reqThisTerm' = [reqThisTerm EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ UNCHANGED <<currentTerm>>
/\ UNCHANGED<<committedThisTerm, leaderAtTermServ, globalCurrentTerm>>

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]]
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ committedThisTerm' = [x0 \in FinNat |-> [x1 \in Server |-> FALSE]]
/\ leaderAtTermServ' = [leaderAtTermServ EXCEPT ![newTerm][i] = TRUE]
/\ globalCurrentTerm' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ reqThisTerm' = [x0 \in Server |-> [x1 \in FinNat |-> FALSE]]
/\ currentLeader' = [[currentLeader EXCEPT ![i] = [x0 \in FinNat |-> FALSE]] EXCEPT ![i][newTerm] = TRUE]

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ curTerm = currentTerm[i]
/\ (commitQuorum \in Quorums)
/\ ind > 0
/\ \A s \in commitQuorum :
    /\ currentTerm[s] = curTerm
/\ UNCHANGED <<currentTerm>>
/\ committedThisTerm' = [committedThisTerm EXCEPT ![curTerm][i] = TRUE]
/\ UNCHANGED<<leaderAtTermServ, globalCurrentTerm, reqThisTerm, currentLeader>>

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)

Init ==
/\ currentTerm = [i \in Server |-> 0]
/\ committedThisTerm = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ leaderAtTermServ = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ globalCurrentTerm = [ x0 \in FinNat |-> FALSE]
/\ reqThisTerm = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ currentLeader = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s,t \in Server : GetEntries(s,t))
\/ (\E s,t \in Server : RollbackEntries(s,t))
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)))))
\/ (\E s,t \in Server : UpdateTerms(s,t))

Spec == Init /\ [][Next]_vars

R3 ==
/\ \A t1 \in FinNat : \A t2 \in FinNat : \A node \in Server : (leaderAtTermServ[t1][node] /\ globalCurrentTerm[t2]) => (t1 <= t2)
/\ \A term \in FinNat : \A leader \in Server : currentLeader[leader][term] => leaderAtTermServ[term][leader]
/\ \A term \in FinNat : \A leader \in Server : (term>0 /\ reqThisTerm[leader][term]) => leaderAtTermServ[term][leader]

TypeOK ==
/\ currentTerm \in [Server -> FinNat]
/\ committedThisTerm  \in [FinNat -> [Server -> BOOLEAN]]
/\ leaderAtTermServ  \in [FinNat -> [Server -> BOOLEAN]]
/\ globalCurrentTerm  \in [FinNat -> BOOLEAN]
/\ reqThisTerm \in [Server -> [FinNat -> BOOLEAN]]
/\ currentLeader \in [Server -> [FinNat -> BOOLEAN]]

TypeOKRand ==
/\ currentTerm \in [Server -> FinNat]
/\ committedThisTerm  \in RandomSubset(13, [FinNat -> [Server -> BOOLEAN]])
/\ leaderAtTermServ  \in RandomSubset(13, [FinNat -> [Server -> BOOLEAN]])
/\ globalCurrentTerm  \in [FinNat -> BOOLEAN]
/\ reqThisTerm \in RandomSubset(13, [Server -> [FinNat -> BOOLEAN]])
/\ currentLeader \in RandomSubset(13, [Server -> [FinNat -> BOOLEAN]])

IndInv ==
/\ TypeOK
/\ R3

IndInvRand == TypeOKRand /\ IndInv

IISpec == IndInvRand /\ [][Next]_vars

=============================================================================
