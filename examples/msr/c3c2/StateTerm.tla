--------------------------- MODULE StateTerm ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, Randomization

CONSTANTS Server, Quorums, FinNat

VARIABLES state, currentTerm, committedThisTerm, leaderAtTermServ, globalCurrentTerm, reqThisTerm, currentLeader

vars == <<state, currentTerm, committedThisTerm, leaderAtTermServ, globalCurrentTerm, reqThisTerm, currentLeader>>

Symmetry == Permutations(Server)
NextUnchanged == UNCHANGED vars

Secondary == "secondary"
Primary == "primary"

CanVoteForOplog(i,j,term) ==
/\ currentTerm[i] < term

UpdateTermsExpr(i,j) ==
/\ state' = [state EXCEPT![j] = Secondary]
/\ currentTerm[i] > currentTerm[j]
/\ currentTerm' = [currentTerm EXCEPT![j] = currentTerm[i]]
/\ UNCHANGED <<committedThisTerm, leaderAtTermServ, globalCurrentTerm, reqThisTerm, currentLeader>>

ClientRequest(i,curTerm) ==
/\ state[i] = Primary
/\ currentTerm[i] = curTerm
/\ UNCHANGED <<state, currentTerm>>
/\ reqThisTerm' = [reqThisTerm EXCEPT ![i][curTerm] = TRUE]
/\ UNCHANGED<<committedThisTerm, leaderAtTermServ, globalCurrentTerm, currentLeader>>

GetEntries(i,j) ==
/\ state[i] = Secondary
/\ currentLeader' = [currentLeader EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ reqThisTerm' = [reqThisTerm EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ UNCHANGED <<state, currentTerm>>
/\ UNCHANGED<<committedThisTerm, leaderAtTermServ, globalCurrentTerm>>

RollbackEntries(i,j) ==
/\ state[i] = Secondary
/\ currentLeader' = [currentLeader EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ reqThisTerm' = [reqThisTerm EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ UNCHANGED <<state, currentTerm>>
/\ UNCHANGED<<committedThisTerm, leaderAtTermServ, globalCurrentTerm>>

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]]
/\ (voteQuorum \in Quorums)
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]]
/\ committedThisTerm' = [x0 \in FinNat |-> [x1 \in Server |-> FALSE]]
/\ leaderAtTermServ' = [leaderAtTermServ EXCEPT ![newTerm][i] = TRUE]
/\ globalCurrentTerm' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ reqThisTerm' = [x0 \in Server |-> [x1 \in FinNat |-> FALSE]]
/\ currentLeader' = [[currentLeader EXCEPT ![i] = [x0 \in FinNat |-> FALSE]] EXCEPT ![i][newTerm] = TRUE]

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ curTerm = currentTerm[i]
/\ (commitQuorum \in Quorums)
/\ ind > 0
/\ state[i] = Primary
/\ \A s \in commitQuorum :
    /\ currentTerm[s] = curTerm
/\ UNCHANGED <<state, currentTerm>>
/\ committedThisTerm' = [committedThisTerm EXCEPT ![curTerm][i] = TRUE]
/\ UNCHANGED<<leaderAtTermServ, globalCurrentTerm, reqThisTerm, currentLeader>>

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)

Init ==
/\ state = [i \in Server |-> Secondary]
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

R2 ==
/\ \A t1 \in FinNat : \A t2 \in FinNat : \A node \in Server : (leaderAtTermServ[t1][node] /\ globalCurrentTerm[t2]) => (t1 <= t2)
/\ \A term \in FinNat : \A leader \in Server : committedThisTerm[term][leader] => globalCurrentTerm[term]
/\ \A term \in FinNat : \A leader \in Server : reqThisTerm[leader][term] => currentLeader[leader][term]
/\ \A term \in FinNat : \A leader \in Server : committedThisTerm[term][leader] => currentLeader[leader][term]
/\ \A term \in FinNat : \A leader \in Server : currentLeader[leader][term] => leaderAtTermServ[term][leader]

TypeOK ==
/\ state \in [Server -> {Primary,Secondary}]
/\ currentTerm \in [Server -> FinNat]
/\ committedThisTerm  \in [FinNat -> [Server -> BOOLEAN]]
/\ leaderAtTermServ  \in [FinNat -> [Server -> BOOLEAN]]
/\ globalCurrentTerm  \in [FinNat -> BOOLEAN]
/\ reqThisTerm \in [Server -> [FinNat -> BOOLEAN]]
/\ currentLeader \in [Server -> [FinNat -> BOOLEAN]]

RandNum == 9 \* 13
TypeOKRand ==
/\ state \in RandomSubset(RandNum, [Server -> {Primary,Secondary}])
/\ currentTerm \in [Server -> FinNat]
/\ committedThisTerm  \in RandomSubset(RandNum, [FinNat -> [Server -> BOOLEAN]])
/\ leaderAtTermServ  \in RandomSubset(RandNum, [FinNat -> [Server -> BOOLEAN]])
/\ globalCurrentTerm  \in [FinNat -> BOOLEAN]
/\ reqThisTerm \in RandomSubset(RandNum, [Server -> [FinNat -> BOOLEAN]])
/\ currentLeader \in RandomSubset(RandNum, [Server -> [FinNat -> BOOLEAN]])

IndInv ==
/\ TypeOK
/\ R2
/\ \A s \in Server : \A sTerm,gTerm \in FinNat : (leaderAtTermServ[sTerm][s] /\ globalCurrentTerm[gTerm]) => (sTerm <= gTerm)
/\ \A t \in FinNat : \A s \in Server : committedThisTerm[t][s] => globalCurrentTerm[t]
/\ \A t \in FinNat : \A s \in Server : reqThisTerm[s][t] => leaderAtTermServ[t][s]
/\ \A t \in FinNat : \A s1,s2 \in Server : (leaderAtTermServ[t][s1] /\ leaderAtTermServ[t][s2]) => s1=s2
/\ \A t \in FinNat : \A s \in Server : currentLeader[s][t] => leaderAtTermServ[t][s]
/\ \A s \in Server : \E t \in FinNat : state[s] = Primary <=> currentLeader[s][t]
/\ \A t1 \in FinNat : \E t2 \in FinNat : \E s \in Server : globalCurrentTerm[t1] => currentLeader[s][t2]
/\ \A t \in FinNat : \A s \in Server : (currentLeader[s][t] /\ state[s] = Primary) => currentTerm[s] = t

(*
/\ \A s \in Server : \A sTerm,gTerm \in FinNat : (leaderAtTermServ[sTerm][s] /\ globalCurrentTerm[gTerm]) => (sTerm <= gTerm)
/\ \A t \in FinNat : \A q1 \in Quorums : ((\E r \in Server : state[r] = Primary) /\ (\A s \in q1 : currentTerm[s] = t)) => globalCurrentTerm[t]
/\ \A t \in FinNat : \A s \in Server : committedThisTerm[t][s] => globalCurrentTerm[t]
/\ \A t \in FinNat : \A s \in Server : state[s] = Secondary => ~committedThisTerm[t][s]
/\ \A n1 \in FinNat : \A r2 \in Server : (currentLeader[r2][n1]) \/ (~(state[r2] = Primary)) \/ (~(currentTerm[r2] = n1))
/\ \A t \in FinNat : \A s \in Server : reqThisTerm[s][t] => leaderAtTermServ[t][s]
/\ \A q \in Quorums : \A t \in FinNat : ((\E s \in Server : state[s] = Primary) /\ (\A s \in q : currentTerm[s] = t)) => globalCurrentTerm[t]
/\ \E t \in FinNat : \E Q \in Quorums: \A s2 \in Server : (\A s \in Q : currentTerm[s] = t) /\ currentTerm[s2] <= t
*)

(*
/\ \A s \in Server : \A sTerm,gTerm \in FinNat : (leaderAtTermServ[sTerm][s] /\ globalCurrentTerm[gTerm]) => (sTerm <= gTerm)
/\ \A t \in FinNat : \A q1 \in Quorums : (t>0 /\ \A s \in q1 : currentTerm[s] = t) => globalCurrentTerm[t]
/\ \E r \in Server : \A t \in FinNat : \A q1 \in Quorums : (state[r] = Primary /\ \A s \in q1 : currentTerm[s] = t) => globalCurrentTerm[t]
/\ \A t \in FinNat : \A q1 \in Quorums : ((\E r \in Server : state[r] = Primary) /\ (\A s \in q1 : currentTerm[s] = t)) => globalCurrentTerm[t]
/\ \A t \in FinNat : \A s \in Server : committedThisTerm[t][s] => globalCurrentTerm[t]
/\ \A t \in FinNat : \A s \in Server : state[s] = Secondary => ~committedThisTerm[t][s]
/\ \A t \in FinNat : \A s \in Server : reqThisTerm[s][t] => leaderAtTermServ[t][s]
/\ \A q \in Quorums : \A t \in FinNat : ((\E s \in Server : state[s] = Primary) /\ (\A s \in q : currentTerm[s] = t)) => globalCurrentTerm[t]
/\ \E t \in FinNat : \E Q \in Quorums: \A s2 \in Server : (\A s \in Q : currentTerm[s] = t) /\ currentTerm[s2] <= t
*)

\*/\ \A t \in FinNat : \E q \in Quorums : globalCurrentTerm[t] => (\A s \in q : currentTerm[s] = t)

IndInvRand == TypeOKRand /\ IndInv

IISpec == IndInvRand /\ [][Next]_vars

=============================================================================
