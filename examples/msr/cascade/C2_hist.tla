--------------------------- MODULE C2_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, Randomization

CONSTANTS Server, Quorums, FinNat

VARIABLES currentTerm, log, Fluent2, Fluent1, state, Fluent0, config

vars == <<currentTerm, log, Fluent2, Fluent1, state, Fluent0, config>>

CandSep ==
TRUE

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

FinSeq(S) == UNION({ [..(1,n) -> S] : n \in FinNat })

StateConstraint == (\A s \in Server : Len(log[s]) < 4)

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
/\ UNCHANGED<<>>
/\ CandSep'
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ CandSep'

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
/\ UNCHANGED<<>>
/\ CandSep'
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ CandSep'

RollbackEntries(i,j) ==
/\ state[i] = Secondary
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED <<currentTerm,state,config>>
/\ UNCHANGED<<>>
/\ CandSep'
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ CandSep'

BecomeLeader(i,voteQuorum,newTerm) ==
/\ newTerm = (currentTerm[i] + 1)
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]]
/\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]]
/\ UNCHANGED <<log,config>>
/\ UNCHANGED<<>>
/\ CandSep'
/\ Fluent1' = [Fluent1 EXCEPT ![newTerm] = TRUE]
/\ UNCHANGED<<Fluent2, Fluent0>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ curTerm = currentTerm[i]
/\ ind = Len(log[i])
/\ ind > 0
/\ state[i] = Primary
/\ log[i][ind] = curTerm
/\ (\A s \in commitQuorum : (Len(log[s]) >= ind /\ currentTerm[s] = curTerm))
/\ UNCHANGED <<currentTerm,state,log,config>>
/\ UNCHANGED<<>>
/\ CandSep'
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent1>>
/\ CandSep'

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<log,config>>
/\ UNCHANGED<<>>
/\ CandSep'
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>
/\ CandSep'

Init ==
/\ currentTerm = [i \in Server |-> 0]
/\ state = [i \in Server |-> Secondary]
/\ log = [i \in Server |-> <<>>]
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))
/\ Fluent2 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent1 = [ x0 \in FinNat |-> FALSE]
/\ Fluent0 = [ x0 \in FinNat |-> FALSE]

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s,t \in Server : GetEntries(s,t))
\/ (\E s,t \in Server : RollbackEntries(s,t))
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)))))
\/ (\E s,t \in Server : UpdateTerms(s,t))

Spec == (Init /\ [][Next]_vars)

Safety ==
/\ \A var0 \in FinNat : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent2[var0][var2]) => (var2 = var1)
=============================================================================
