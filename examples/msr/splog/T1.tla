--------------------------- MODULE T1 ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

VARIABLES currentTerm, log, state, config

Server == {"n1","n2"}

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

FinNat == ..(0,5)

vars == <<currentTerm,state,log,config>>

Quorums(S) == { i \in SUBSET(S) : (Cardinality(i) * 2) > Cardinality(S) }

Empty(s) == Len(s) = 0

InLog(e,i) ==
\E x \in DOMAIN(log[i]) :
/\ x = e[1]
/\ log[i][x] = e[2]

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

IsPrefix(s,t) == (Len(s) <= Len(t) /\ SubSeq(s,1,Len(s)) = SubSeq(t,1,Len(s)))

CanRollback(i,j) ==
/\ LastTerm(log[i]) < LastTerm(log[j])
/\ ~(IsPrefix(log[i],log[j]))

CanVoteForOplog(i,j,term) ==
LET logOk == (LastTerm(log[j]) > LastTerm(log[i]) \/ (LastTerm(log[j]) = LastTerm(log[i]) /\ Len(log[j]) >= Len(log[i]))) IN
  /\ currentTerm[i] < term
  /\ logOk

ImmediatelyCommitted(e,Q) ==
LET eind == e[1]
    eterm == e[2] IN
  \A s \in Q :
  /\ Len(log[s]) >= eind
  /\ InLog(e,s)
  /\ currentTerm[s] = eterm

UpdateTermsExpr(i,j) ==
/\ currentTerm[i] > currentTerm[j]
/\ currentTerm' = [currentTerm EXCEPT![j] = currentTerm[i]]
/\ state' = [state EXCEPT![j] = Secondary]

ClientRequest(i,curTerm) ==
/\ state[i] = Primary
/\ currentTerm[i] = curTerm
/\ log' = [log EXCEPT![i] = Append(log[i],curTerm)]
/\ UNCHANGED <<currentTerm,state,config>>

GetEntries(i,j) ==
/\ state[i] = Secondary
/\ Len(log[j]) > Len(log[i])
/\ LET logOk == IF Empty(log[i]) THEN TRUE ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
  /\ logOk
  /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE (Len(log[i]) + 1)
      newEntry == log[j][newEntryIndex]
      newLog == Append(log[i],newEntry) IN
    /\ log' = [log EXCEPT![i] = newLog]
/\ UNCHANGED <<currentTerm,state,config>>

RollbackEntries(i,j) ==
/\ state[i] = Secondary
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED <<currentTerm,state,config>>

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (voteQuorum \in Quorums(config[i]))
/\ newTerm = (currentTerm[i] + 1)
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]]
/\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]]
/\ UNCHANGED <<log,config>>

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ (commitQuorum \in Quorums(config[i]))
/\ curTerm = currentTerm[i]
/\ ind = Len(log[i])
/\ ind > 0
/\ state[i] = Primary
/\ log[i][ind] = curTerm
/\ ImmediatelyCommitted(<<ind,curTerm>>,commitQuorum)
/\ UNCHANGED <<currentTerm,state,log,config>>

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<log,config>>

Init ==
/\ currentTerm = [i \in Server |-> 0]
/\ state = [i \in Server |-> Secondary]
/\ log = [i \in Server |-> <<>>]
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s,t \in Server : GetEntries(s,t))
\/ (\E s,t \in Server : RollbackEntries(s,t))
\/ (\E s \in Server : (\E Q \in SUBSET(Server) : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in SUBSET(Server) : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)))))
\/ (\E s,t \in Server : UpdateTerms(s,t))

Spec == (Init /\ [][Next]_vars)
=============================================================================
