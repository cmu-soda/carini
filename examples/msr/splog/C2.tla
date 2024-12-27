---- MODULE C2 ----
\*
\* Basic, static version of MongoDB Raft protocol. No reconfiguration is allowed.
\*

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

CONSTANTS Server, Quorums, FinNat

Secondary == "secondary"
Primary == "primary"
Nil == "nil"

VARIABLE log
VARIABLE logLen
VARIABLE logLastTerm

vars == <<log, logLen, logLastTerm>>

StateConstraint == \A s \in Server : Len(log[s]) < 3

\*
\* Helper operators.
\*
\* Is log entry e = <<index, term>> in the log of node 'i'.
InLog(e, i) == \E x \in DOMAIN log[i] : x = e[1] /\ log[i][x] = e[2]

IsPrefix(s, t) ==
  (**************************************************************************)
  (* TRUE iff the sequence s is a prefix of the sequence t, s.t.            *)
  (* \E u \in Seq(Range(t)) : t = s \o u. In other words, there exists      *)
  (* a suffix u that with s prepended equals t.                             *)
  (**************************************************************************)
  Len(s) <= Len(t) /\ SubSeq(s, 1, Len(s)) = SubSeq(t, 1, Len(s))

\* Can node 'i' currently cast a vote for node 'j' in term 'term'.
CanVoteForOplog(i, j, term) ==
    LET logOk ==
        \/ logLastTerm[j] > logLastTerm[i]
        \/ /\ logLastTerm[j] = logLastTerm[i]
           /\ logLen[j] >= logLen[i] IN
    /\ logOk

--------------------------------------------------------------------------------

\*
\* Next state actions.
\*

\* Node 'i', a primary, handles a new client request and places the entry 
\* in its log.    
ClientRequest(i, curTerm) ==
    /\ log' = [log EXCEPT ![i] = Append(log[i], curTerm)]
    /\ logLen' = [logLen EXCEPT ![i] = logLen[i]+1]
    /\ logLastTerm' = [logLastTerm EXCEPT ![i] = curTerm]

\* Node 'i' gets a new log entry from node 'j'.
GetEntries(i, j, iLogLen, jLogLen) ==
    /\ iLogLen = logLen[i]
    /\ jLogLen = logLen[j]
    \* Node j must have more entries than node i.
    /\ jLogLen > iLogLen
       \* Ensure that the entry at the last index of node i's log must match the entry at
       \* the same index in node j's log. If the log of node i is empty, then the check
       \* trivially passes. This is the essential 'log consistency check'.
    /\ LET logOk == IF iLogLen = 0
                        THEN TRUE
                        ELSE log[j][iLogLen] = log[i][iLogLen] IN
       /\ logOk \* log consistency check
       \* If the log of node i is empty, then take the first entry from node j's log.
       \* Otherwise take the entry following the last index of node i.
       /\ LET newEntryIndex == IF iLogLen = 0 THEN 1 ELSE iLogLen + 1
              newEntry      == log[j][newEntryIndex]
              newLog        == Append(log[i], newEntry) IN
              /\ log' = [log EXCEPT ![i] = newLog]
              /\ logLen' = [logLen EXCEPT ![i] = newEntryIndex]
              /\ logLastTerm' = [logLastTerm EXCEPT ![i] = newEntry]

\*  Node 'i' rolls back against the log of node 'j'.  
RollbackEntries(i, j) ==
    /\ logLastTerm[i] < logLastTerm[j]
    /\ ~IsPrefix(log[i],log[j])
    \* Roll back one log entry.
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i])-1)]
    /\ logLen' = [logLen EXCEPT ![i] = logLen[i]-1]
    /\ LET prevTerm == IF logLen[i] > 1 THEN log[i][logLen[i]-1] ELSE 0 IN
       logLastTerm' = [logLastTerm EXCEPT ![i] = prevTerm]

\* Node 'i' gets elected as a primary.
BecomeLeader(i, voteQuorum, newTerm) == 
    \* Primaries make decisions based on their current configuration.
    /\ i \in voteQuorum \* The new leader should vote for itself.
    /\ \A v \in voteQuorum : CanVoteForOplog(v, i, newTerm)
    \* Update the terms of each voter.
    /\ UNCHANGED <<log, logLen, logLastTerm>>
            
\* Primary 'i' commits its latest log entry.
CommitEntry(i, commitQuorum, ind, curTerm) ==
    /\ ind = logLen[i]
    /\ ind > 0
    /\ log[i][ind] = curTerm
    /\ \A s \in commitQuorum :
        /\ logLen[s] >= ind
        /\ InLog(<<ind,curTerm>>, s) \* they have the entry.
    /\ UNCHANGED <<log, logLen, logLastTerm>>

Init == 
    /\ log = [i \in Server |-> <<>>]
    /\ logLen = [i \in Server |-> 0]
    /\ logLastTerm = [i \in Server |-> 0]

Next == 
    \/ \E s \in Server : \E t \in FinNat : ClientRequest(s,t)
    \/ \E s, t \in Server : \E ls, lt \in FinNat : GetEntries(s, t, ls, lt)
    \/ \E s, t \in Server : RollbackEntries(s, t)
    \/ \E s \in Server : \E Q \in Quorums : \E newTerm \in FinNat : BecomeLeader(s, Q, newTerm)
    \/ \E s \in Server :  \E Q \in Quorums : \E ind \in FinNat : \E curTerm \in FinNat : CommitEntry(s, Q, ind, curTerm)

Spec == Init /\ [][Next]_vars

=============================================================================
