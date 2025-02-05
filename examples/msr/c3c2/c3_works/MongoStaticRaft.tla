---- MODULE MongoStaticRaft ----
\*
\* Basic, static version of MongoDB Raft protocol. No reconfiguration is allowed.
\*

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

CONSTANTS Server, Quorums, FinNat

Secondary == "secondary"
Primary == "primary"
Nil == "nil"

VARIABLE currentTerm
VARIABLE state
VARIABLE log
VARIABLE config

VARIABLE committed

vars == <<currentTerm, state, log, committed, config>>

StateConstraint == \A s \in Server : Len(log[s]) < 4

\*
\* Helper operators.
\*
MinTerm(Q) == CHOOSE t \in FinNat : (\A n \in Q : t <= currentTerm[n]) /\ (\E n \in Q : t = currentTerm[n])

Empty(s) == Len(s) = 0

\* Is log entry e = <<index, term>> in the log of node 'i'.
InLog(e, i) == \E x \in DOMAIN log[i] : x = e[1] /\ log[i][x] = e[2]

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]
LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

IsPrefix(s, t) ==
  (**************************************************************************)
  (* TRUE iff the sequence s is a prefix of the sequence t, s.t.            *)
  (* \E u \in Seq(Range(t)) : t = s \o u. In other words, there exists      *)
  (* a suffix u that with s prepended equals t.                             *)
  (**************************************************************************)
  Len(s) <= Len(t) /\ SubSeq(s, 1, Len(s)) = SubSeq(t, 1, Len(s))

CanRollback(i, j) ==
    /\ LastTerm(log[i]) < LastTerm(log[j])
    /\ ~IsPrefix(log[i],log[j])

\* Can node 'i' currently cast a vote for node 'j' in term 'term'.
CanVoteForOplog(i, j, term) ==
    LET logOk ==
        \/ LastTerm(log[j]) > LastTerm(log[i])
        \/ /\ LastTerm(log[j]) = LastTerm(log[i])
           /\ Len(log[j]) >= Len(log[i]) IN
    /\ currentTerm[i] < term
    /\ logOk

\* Is a log entry 'e'=<<i, t>> immediately committed in term 't' with a quorum 'Q'.
ImmediatelyCommitted(e, Q) == 
    LET eind == e[1] 
        eterm == e[2] IN
    \A s \in Q :
        /\ Len(log[s]) >= eind
        /\ InLog(e, s) \* they have the entry.
        /\ currentTerm[s] = eterm  \* they are in the same term as the log entry. 

\* Helper operator for actions that propagate the term between two nodes.
UpdateTermsExpr(i, j) ==
    /\ currentTerm[i] > currentTerm[j]
    /\ currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
    /\ state' = [state EXCEPT ![j] = Secondary] 

--------------------------------------------------------------------------------

\*
\* Next state actions.
\*

\* Node 'i', a primary, handles a new client request and places the entry 
\* in its log.    
ClientRequest(i, curTerm) ==
    /\ state[i] = Primary
    /\ currentTerm[i] = curTerm
    /\ log' = [log EXCEPT ![i] = Append(log[i], curTerm)]
    /\ UNCHANGED <<currentTerm, state, committed, config>>

\* Node 'i' gets a new log entry from node 'j'.
GetEntries(i, j) ==
    /\ state[i] = Secondary
    \* Node j must have more entries than node i.
    /\ Len(log[j]) > Len(log[i])
       \* Ensure that the entry at the last index of node i's log must match the entry at
       \* the same index in node j's log. If the log of node i is empty, then the check
       \* trivially passes. This is the essential 'log consistency check'.
    /\ LET logOk == IF Empty(log[i])
                        THEN TRUE
                        ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
       /\ logOk \* log consistency check
       \* If the log of node i is empty, then take the first entry from node j's log.
       \* Otherwise take the entry following the last index of node i.
       /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE Len(log[i]) + 1
              newEntry      == log[j][newEntryIndex]
              newLog        == Append(log[i], newEntry) IN
              /\ log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<committed, currentTerm, state, config>>

\*  Node 'i' rolls back against the log of node 'j'.  
RollbackEntries(i, j) ==
    /\ state[i] = Secondary
    /\ CanRollback(i, j)
    \* Roll back one log entry.
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i])-1)]
    /\ UNCHANGED <<committed, currentTerm, state, config>>

\* Node 'i' gets elected as a primary.
BecomeLeader(i, voteQuorum, newTerm) == 
    \* Primaries make decisions based on their current configuration.
    /\ newTerm = currentTerm[i] + 1
    /\ i \in voteQuorum \* The new leader should vote for itself.
    /\ \A v \in voteQuorum : CanVoteForOplog(v, i, newTerm)
    \* Update the terms of each voter.
    /\ currentTerm' = [s \in Server |-> IF s \in voteQuorum THEN newTerm ELSE currentTerm[s]]
    /\ state' = [s \in Server |->
                    IF s = i THEN Primary
                    ELSE IF s \in voteQuorum THEN Secondary \* All voters should revert to secondary state.
                    ELSE state[s]]
    /\ UNCHANGED <<log, config, committed>>   
            
\* Primary 'i' commits its latest log entry.
CommitEntry(i, commitQuorum, ind, curTerm, minQTerm) ==
    /\ minQTerm = MinTerm(commitQuorum)
    /\ curTerm = currentTerm[i]
    /\ ind = Len(log[i])
    \* Must have some entries to commit.
    /\ ind > 0
    \* This node is leader.
    /\ state[i] = Primary
    \* The entry was written by this leader.
    /\ log[i][ind] = curTerm
    \* all nodes have this log entry and are in the term of the leader.
    \*/\ ImmediatelyCommitted(<<ind,curTerm>>, commitQuorum)
    /\ \A s \in commitQuorum :
        /\ Len(log[s]) >= ind
        /\ InLog(<<ind,curTerm>>, s) \* they have the entry.
        /\ currentTerm[s] = curTerm  \* they are in the same term as the log entry. 
    \* Don't mark an entry as committed more than once.
    /\ ~\E c \in committed : c.entry = <<ind, curTerm>>
    /\ committed' = committed \cup
            {[ entry  |-> <<ind, curTerm>>,
               term  |-> curTerm]}
    /\ UNCHANGED <<currentTerm, state, log, config>>

\* Action that exchanges terms between two nodes and step down the primary if
\* needed. This can be safely specified as a separate action, rather than
\* occurring atomically on other replication actions that involve communication
\* between two nodes. This makes it clearer to see where term propagation is
\* strictly necessary for guaranteeing safety.
UpdateTerms(i, j) == 
    /\ UpdateTermsExpr(i, j)
    /\ UNCHANGED <<log, config, committed>>

Init == 
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Secondary]
    /\ log = [i \in Server |-> <<>>]
    /\ \E initConfig \in SUBSET Server : 
        /\ initConfig # {} \* configs should be non-empty.
        /\ config = [i \in Server |-> initConfig]
    /\ committed = {}

Next == 
    \/ \E s \in Server : \E t \in FinNat : ClientRequest(s,t)
    \/ \E s, t \in Server : GetEntries(s, t)
    \/ \E s, t \in Server : RollbackEntries(s, t)
    \/ \E s \in Server : \E Q \in Quorums : \E newTerm \in FinNat : BecomeLeader(s, Q, newTerm)
    \/ \E s \in Server :  \E Q \in Quorums : \E ind \in FinNat : \E curTerm \in FinNat : \E minQTerm \in FinNat : CommitEntry(s, Q, ind, curTerm, minQTerm)
    \/ \E s,t \in Server : UpdateTerms(s, t)

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------------

\*
\* Correctness properties
\*

(*
OnePrimaryPerTerm == 
    \A s,t \in Server :
        (/\ state[s] = Primary 
         /\ state[t] = Primary
         /\ currentTerm[s] = currentTerm[t]) => (s = t)

LeaderAppendOnly == 
    [][\A s \in Server : state[s] = Primary => Len(log'[s]) >= Len(log[s])]_vars

\* <<index, term>> pairs uniquely identify log prefixes.
LogMatching == 
    \A s,t \in Server : 
    \A i \in DOMAIN log[s] :
        (\E j \in DOMAIN log[t] : i = j /\ log[s][i] = log[t][j]) => 
        (SubSeq(log[s],1,i) = SubSeq(log[t],1,i)) \* prefixes must be the same.

\* When a node gets elected as primary it contains all entries committed in previous terms.
LeaderCompleteness == 
    \A s \in Server : (state[s] = Primary) => 
        \A c \in committed : (c.term < currentTerm[s] => InLog(c.entry, s))
*)

\* If two entries are committed at the same index, they must be the same entry.
StateMachineSafety == 
    \A c1, c2 \in committed : (c1.entry[1] = c2.entry[1]) => (c1 = c2)

=============================================================================
