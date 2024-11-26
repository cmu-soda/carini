--------------------------- MODULE tmp ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES log, state, config

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

vars == <<state,log,config>>

Empty(s) == Len(s) = 0

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

IsPrefix(s,t) == (Len(s) <= Len(t) /\ SubSeq(s,1,Len(s)) = SubSeq(t,1,Len(s)))

UpdateTermsExpr(i,j) ==
/\ state' = [state EXCEPT![j] = Secondary]

ClientRequest(i,curTerm) ==
/\ state[i] = Primary
/\ log' = [log EXCEPT![i] = Append(log[i],curTerm)]
/\ UNCHANGED <<state,config>>

GetEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<log,state,config>>

RollbackEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<log,state,config>>

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (voteQuorum \in Quorums)
/\ (i \in voteQuorum)
/\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]]
/\ UNCHANGED <<log,config>>

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ (commitQuorum \in Quorums)
/\ ind > 0
/\ state[i] = Primary
/\ UNCHANGED <<state,log,config>>

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<log,config>>

Init ==
/\ state = [i \in Server |-> Secondary]
/\ log = [i \in Server |-> <<>>]
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s,t \in Server : GetEntries(s,t))
\/ (\E s,t \in Server : RollbackEntries(s,t))
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)))))
\/ (\E s,t \in Server : UpdateTerms(s,t))

Spec == (Init /\ [][Next]_vars)
=============================================================================
