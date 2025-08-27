--------------------------- MODULE State ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, Randomization

CONSTANTS Server, Quorums, FinNat

VARIABLES state, committedThisTerm, leaderAtTermServ, globalCurrentTerm, reqThisTerm, currentLeader

vars == <<state, committedThisTerm, leaderAtTermServ, globalCurrentTerm, reqThisTerm, currentLeader>>

Symmetry == Permutations(Server)
NextUnchanged == UNCHANGED vars

R3 ==
/\ \A t1 \in FinNat : \A t2 \in FinNat : \A node \in Server : (leaderAtTermServ[t1][node] /\ globalCurrentTerm[t2]) => (t1 <= t2)
/\ \A term \in FinNat : \A leader \in Server : currentLeader[leader][term] => leaderAtTermServ[term][leader]
/\ \A term \in FinNat : \A l1 \in Server : \E l2 \in Server : (term>0 /\ reqThisTerm[l1][term]) => leaderAtTermServ[term][l2]

Secondary == "secondary"
Primary == "primary"

UpdateTermsExpr(i,j) ==
/\ state' = [state EXCEPT![j] = Secondary]
/\ UNCHANGED <<committedThisTerm, leaderAtTermServ, globalCurrentTerm, reqThisTerm, currentLeader>>
/\ R3'

ClientRequest(i,curTerm) ==
/\ state[i] = Primary
/\ UNCHANGED <<state>>
/\ reqThisTerm' = [reqThisTerm EXCEPT ![i][curTerm] = TRUE]
/\ UNCHANGED<<committedThisTerm, leaderAtTermServ, globalCurrentTerm, currentLeader>>
/\ R3'

GetEntries(i,j) ==
/\ state[i] = Secondary
/\ currentLeader' = [currentLeader EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ reqThisTerm' = [reqThisTerm EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ UNCHANGED <<state>>
/\ UNCHANGED<<committedThisTerm, leaderAtTermServ, globalCurrentTerm>>
/\ R3'

RollbackEntries(i,j) ==
/\ state[i] = Secondary
/\ currentLeader' = [currentLeader EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ reqThisTerm' = [reqThisTerm EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ UNCHANGED <<state>>
/\ UNCHANGED<<committedThisTerm, leaderAtTermServ, globalCurrentTerm>>
/\ R3'

BecomeLeader(i,voteQuorum,newTerm) ==
\*/\ (i \in voteQuorum)
/\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]]
/\ committedThisTerm' = [x0 \in FinNat |-> [x1 \in Server |-> FALSE]]
/\ leaderAtTermServ' = [leaderAtTermServ EXCEPT ![newTerm][i] = TRUE]
/\ globalCurrentTerm' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ reqThisTerm' = [x0 \in Server |-> [x1 \in FinNat |-> FALSE]]
/\ currentLeader' = [[currentLeader EXCEPT ![i] = [x0 \in FinNat |-> FALSE]] EXCEPT ![i][newTerm] = TRUE]
/\ R3'

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ (commitQuorum \in Quorums)
/\ ind > 0
/\ state[i] = Primary
/\ committedThisTerm' = [committedThisTerm EXCEPT ![curTerm][i] = TRUE]
/\ UNCHANGED <<state>>
/\ UNCHANGED<<leaderAtTermServ, globalCurrentTerm, reqThisTerm, currentLeader>>
/\ R3'

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)

Init ==
/\ state = [i \in Server |-> Secondary]
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

R2 ==
/\ \A t1 \in FinNat : \A t2 \in FinNat : \A node \in Server : (leaderAtTermServ[t1][node] /\ globalCurrentTerm[t2]) => (t1 <= t2)
\*/\ \A term \in FinNat : \A leader \in Server : committedThisTerm[term][leader] => globalCurrentTerm[term]
/\ \A term \in FinNat : \A leader \in Server : reqThisTerm[leader][term] => currentLeader[leader][term]
\*/\ \A term \in FinNat : \A leader \in Server : committedThisTerm[term][leader] => currentLeader[leader][term]
/\ \A term \in FinNat : \A leader \in Server : currentLeader[leader][term] => leaderAtTermServ[term][leader]

TypeOK ==
/\ state \in [Server -> {Primary,Secondary}]
/\ committedThisTerm  \in [FinNat -> [Server -> BOOLEAN]]
/\ leaderAtTermServ  \in [FinNat -> [Server -> BOOLEAN]]
/\ globalCurrentTerm  \in [FinNat -> BOOLEAN]
/\ reqThisTerm \in [Server -> [FinNat -> BOOLEAN]]
/\ currentLeader \in [Server -> [FinNat -> BOOLEAN]]

TypeOKRand ==
/\ state \in RandomSubset(13, [Server -> {Primary,Secondary}])
/\ committedThisTerm  \in RandomSubset(13, [FinNat -> [Server -> BOOLEAN]])
/\ leaderAtTermServ  \in RandomSubset(13, [FinNat -> [Server -> BOOLEAN]])
/\ globalCurrentTerm  \in [FinNat -> BOOLEAN]
/\ reqThisTerm \in RandomSubset(13, [Server -> [FinNat -> BOOLEAN]])
/\ currentLeader \in RandomSubset(13, [Server -> [FinNat -> BOOLEAN]])

IndInv ==
/\ TypeOK
/\ R2
/\ R3

IndInvRand == TypeOKRand /\ IndInv

IISpec == IndInvRand /\ [][Next]_vars

=============================================================================
