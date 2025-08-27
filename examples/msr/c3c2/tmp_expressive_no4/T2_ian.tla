--------------------------- MODULE T2_ian ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES currentTerm, Fluent2, Fluent1, state, Fluent0, config, Fluent10_12, Fluent11_12, Fluent9_6, CurCommitEntry

vars == <<currentTerm, Fluent2, Fluent1, state, Fluent0, config, Fluent10_12, Fluent11_12, Fluent9_6, CurCommitEntry>>

CandSep ==
\A var0 \in FinNat : \A var1 \in FinNat : Fluent9_6[var0] => (CurCommitEntry[var1] => (var0 = var1))

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

MinTerm(Q) == (CHOOSE t \in FinNat : ((\A n \in Q : t <= currentTerm[n]) /\ (\E n \in Q : t = currentTerm[n])))

Empty(s) == Len(s) = 0

IsPrefix(s,t) == (Len(s) <= Len(t) /\ SubSeq(s,1,Len(s)) = SubSeq(t,1,Len(s)))

CanVoteForOplog(i,j,term) ==
/\ currentTerm[i] < term

UpdateTermsExpr(i,j) ==
/\ state' = [state EXCEPT![j] = Secondary]
/\ currentTerm[i] > currentTerm[j]
/\ currentTerm' = [currentTerm EXCEPT![j] = currentTerm[i]]

ClientRequest(i,curTerm) ==
/\ state[i] = Primary
/\ currentTerm[i] = curTerm
/\ UNCHANGED <<state,config,currentTerm>>
/\ Fluent11_12' = [[x0 \in Server |-> FALSE] EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent10_12>>
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ UNCHANGED<<CurCommitEntry, Fluent9_6>>

GetEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED<<Fluent10_12, Fluent11_12>>
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ UNCHANGED<<CurCommitEntry, Fluent9_6>>

RollbackEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED<<Fluent10_12, Fluent11_12>>
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ UNCHANGED<<CurCommitEntry, Fluent9_6>>

BecomeLeader(i,voteQuorum,newTerm) ==
/\ newTerm = (currentTerm[i] + 1)
/\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]]
/\ (voteQuorum \in Quorums)
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]]
/\ UNCHANGED <<config>>
/\ Fluent11_12' = [Fluent11_12 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent10_12>>
/\ Fluent1' = [Fluent1 EXCEPT ![newTerm] = TRUE]
/\ UNCHANGED<<Fluent2, Fluent0>>
/\ Fluent9_6' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ CurCommitEntry' = [x0 \in FinNat |-> FALSE]

CommitEntry(i,commitQuorum,ind,curTerm,minQTerm) ==
/\ minQTerm = MinTerm(commitQuorum)
/\ curTerm = currentTerm[i]
/\ (commitQuorum \in Quorums)
/\ ind > 0
/\ state[i] = Primary
/\ (\A s \in commitQuorum : currentTerm[s] = curTerm)
/\ UNCHANGED <<state,config,currentTerm>>
/\ Fluent10_12' = [Fluent10_12 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent11_12>>
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent1>>
/\ CurCommitEntry' = [CurCommitEntry EXCEPT ![minQTerm] = TRUE]
/\ UNCHANGED<<Fluent9_6>>

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<config>>
/\ UNCHANGED<<Fluent10_12, Fluent11_12>>
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ UNCHANGED<<CurCommitEntry, Fluent9_6>>

Init ==
/\ state = [i \in Server |-> Secondary]
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))
/\ currentTerm = [i \in Server |-> 0]
/\ Fluent10_12 = [ x0 \in Server |-> FALSE]
/\ Fluent11_12 = [ x0 \in Server |-> FALSE]
/\ Fluent2 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent1 = [ x0 \in FinNat |-> FALSE]
/\ Fluent0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent9_6 = [ x0 \in FinNat |-> FALSE]
/\ CurCommitEntry = [ x0 \in FinNat |-> FALSE]

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s,t \in Server : GetEntries(s,t))
\/ (\E s,t \in Server : RollbackEntries(s,t))
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : (\E minQTerm \in FinNat : CommitEntry(s,Q,ind,curTerm,minQTerm))))))
\/ (\E s,t \in Server : UpdateTerms(s,t))

Spec == (Init /\ [][Next]_vars)
=============================================================================
