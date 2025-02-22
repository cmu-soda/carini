---- MODULE T1 ----
\*
\* Basic, static version of MongoDB Raft protocol. No reconfiguration is allowed.
\*

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

CONSTANTS Server, Quorums, FinNat

Secondary == "secondary"
Primary == "primary"
Nil == "nil"

VARIABLE state

vars == <<state>>

StateConstraint == TRUE

\*
\* Helper operators.
\*

\* Helper operator for actions that propagate the term between two nodes.
UpdateTermsExpr(i, j) ==
    /\ state' = [state EXCEPT ![j] = Secondary] 

--------------------------------------------------------------------------------

\*
\* Next state actions.
\*

\* Node 'i', a primary, handles a new client request and places the entry 
\* in its log.    
ClientRequest(i, curTerm) ==
    \*/\ state[i] = Primary
    /\ UNCHANGED <<state>>

\* Node 'i' gets a new log entry from node 'j'.
GetEntries(i, j) ==
    \*/\ state[i] = Secondary
    /\ UNCHANGED <<state>>

\*  Node 'i' rolls back against the log of node 'j'.  
RollbackEntries(i, j) ==
    \*/\ state[i] = Secondary
    /\ UNCHANGED <<state>>

\* Node 'i' gets elected as a primary.
BecomeLeader(i, voteQuorum, newTerm) == 
    /\ state' = [s \in Server |->
                    IF s = i THEN Primary
                    ELSE IF s \in voteQuorum THEN Secondary \* All voters should revert to secondary state.
                    ELSE state[s]]
            
\* Primary 'i' commits its latest log entry.
CommitEntry(i, commitQuorum, ind, curTerm) ==
    /\ state[i] = Primary
    /\ UNCHANGED <<state>>

\* Action that exchanges terms between two nodes and step down the primary if
\* needed. This can be safely specified as a separate action, rather than
\* occurring atomically on other replication actions that involve communication
\* between two nodes. This makes it clearer to see where term propagation is
\* strictly necessary for guaranteeing safety.
UpdateTerms(i, j) == 
    /\ UpdateTermsExpr(i, j)

Init == 
    /\ state       = [i \in Server |-> Secondary]

Next == 
    \/ \E s \in Server : \E t \in FinNat : ClientRequest(s,t)
    \/ \E s, t \in Server : GetEntries(s, t)
    \/ \E s, t \in Server : RollbackEntries(s, t)
    \/ \E s \in Server : \E Q \in Quorums : \E newTerm \in FinNat : BecomeLeader(s, Q, newTerm)
    \/ \E s \in Server :  \E Q \in Quorums : \E ind \in FinNat : \E curTerm \in FinNat : CommitEntry(s, Q, ind, curTerm)
    \/ \E s,t \in Server : UpdateTerms(s, t)

Spec == Init /\ [][Next]_vars

=============================================================================
