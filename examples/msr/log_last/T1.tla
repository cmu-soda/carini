--------------------------- MODULE T1 ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES committed, currentTerm, state, config

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

vars == <<committed,state,currentTerm,config>>

StateConstraint == TRUE

Empty(s) == Len(s) = 0

IsPrefix(s,t) == (Len(s) <= Len(t) /\ SubSeq(s,1,Len(s)) = SubSeq(t,1,Len(s)))

CanVoteForOplog(i,j,term) ==
/\ currentTerm[i] < term

UpdateTermsExpr(i,j) ==
/\ state' = [state EXCEPT![j] = Secondary]
/\ currentTerm[i] > currentTerm[j]
/\ currentTerm' = [currentTerm EXCEPT![j] = currentTerm[i]]

ClientRequest(i,curTerm,idx) ==
/\ state[i] = Primary
/\ currentTerm[i] = curTerm
/\ UNCHANGED <<committed,state,config,currentTerm>>

GetEntries(i,j,idx) ==
/\ state[i] = Secondary
/\ UNCHANGED <<committed,state,config,currentTerm>>

RollbackEntries(i,j,idx) ==
/\ state[i] = Secondary
/\ UNCHANGED <<committed,state,config,currentTerm>>

BecomeLeader(i,voteQuorum,newTerm,idx) ==
/\ newTerm = (currentTerm[i] + 1)
/\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]]
/\ (voteQuorum \in Quorums)
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]]
/\ UNCHANGED <<committed,config>>

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ curTerm = currentTerm[i]
/\ (commitQuorum \in Quorums)
/\ ind > 0
/\ state[i] = Primary
/\ \A s \in commitQuorum :
    /\ currentTerm[s] = curTerm  \* they are in the same term as the log entry. 
/\ ~((\E c \in committed : c.entry = <<ind,curTerm>>))
/\ committed' = (committed \cup {[entry |-> <<ind,curTerm>>,term |-> curTerm]})
/\ UNCHANGED <<state,config,currentTerm>>

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<committed,config>>

Init ==
/\ state = [i \in Server |-> Secondary]
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))
/\ currentTerm = [i \in Server |-> 0]
/\ committed = {}

Next ==
\/ (\E s \in Server : (\E t,idx \in FinNat : ClientRequest(s,t,idx)))
\/ (\E s,t \in Server : (\E idx \in FinNat : GetEntries(s,t,idx)))
\/ (\E s,t \in Server : (\E idx \in FinNat : RollbackEntries(s,t,idx)))
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm,idx \in FinNat : BecomeLeader(s,Q,newTerm,idx))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)))))
\/ (\E s,t \in Server : UpdateTerms(s,t))

Spec == (Init /\ [][Next]_vars)

StateMachineSafety == (\A c1,c2 \in committed : (c1.entry[1] = c2.entry[1] => c1 = c2))
=============================================================================
