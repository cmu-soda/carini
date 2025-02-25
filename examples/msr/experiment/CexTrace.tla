--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS n1, n2, Server, n3, Quorums, NUM2, NUM3, NUM0, NUM1, _n2n3_, _n1n2n3_, FinNat, _n1n3_, _n1n2_

VARIABLES Fluent9, currentTerm, log, Fluent10, Fluent2, Fluent1, state, Fluent0, config, cexTraceIdx

vars == <<Fluent9, currentTerm, log, Fluent10, Fluent2, Fluent1, state, Fluent0, config, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ Fluent10 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ log = (n1 :> <<>> @@ n2 :> <<>> @@ n3 :> <<>>)
  /\ state = (n1 :> "secondary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ Fluent0 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
  /\ Fluent1 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
  /\ Fluent9 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ config = (n1 :> {n1, n2, n3} @@ n2 :> {n1, n2, n3} @@ n3 :> {n1, n2, n3})
  /\ currentTerm = (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0)

/\ cexTraceIdx = 1 =>
  /\ Fluent10 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ log = (n1 :> <<>> @@ n2 :> <<>> @@ n3 :> <<>>)
  /\ state = (n1 :> "primary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ Fluent0 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
  /\ Fluent1 = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
  /\ Fluent9 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ config = (n1 :> {n1, n2, n3} @@ n2 :> {n1, n2, n3} @@ n3 :> {n1, n2, n3})
  /\ currentTerm = (n1 :> 1 @@ n2 :> 1 @@ n3 :> 0)

/\ cexTraceIdx = 2 =>
  /\ Fluent10 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ log = (n1 :> <<1>> @@ n2 :> <<>> @@ n3 :> <<>>)
  /\ state = (n1 :> "primary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ Fluent0 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
  /\ Fluent1 = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
  /\ Fluent9 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ config = (n1 :> {n1, n2, n3} @@ n2 :> {n1, n2, n3} @@ n3 :> {n1, n2, n3})
  /\ currentTerm = (n1 :> 1 @@ n2 :> 1 @@ n3 :> 0)

/\ cexTraceIdx = 3 =>
  /\ Fluent10 = (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE)
  /\ log = (n1 :> <<1>> @@ n2 :> <<>> @@ n3 :> <<>>)
  /\ state = (n1 :> "primary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ Fluent0 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
  /\ Fluent1 = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
  /\ Fluent9 = (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE)
  /\ config = (n1 :> {n1, n2, n3} @@ n2 :> {n1, n2, n3} @@ n3 :> {n1, n2, n3})
  /\ currentTerm = (n1 :> 1 @@ n2 :> 1 @@ n3 :> 0)

/\ cexTraceIdx = 4 =>
  /\ Fluent10 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ log = (n1 :> <<1>> @@ n2 :> <<1>> @@ n3 :> <<>>)
  /\ state = (n1 :> "primary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ Fluent0 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
  /\ Fluent1 = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
  /\ Fluent9 = (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE)
  /\ config = (n1 :> {n1, n2, n3} @@ n2 :> {n1, n2, n3} @@ n3 :> {n1, n2, n3})
  /\ currentTerm = (n1 :> 1 @@ n2 :> 1 @@ n3 :> 0)


CandSep == (\A var0 \in Server : (Fluent9[var0] => Fluent10[var0]))

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

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
/\ UNCHANGED <<Fluent9,Fluent10>>
/\ UNCHANGED <<Fluent2,Fluent1,Fluent0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

GetEntries(i,j) ==
/\ state[i] = Secondary
/\ Len(log[j]) > Len(log[i])
/\ LET logOk == IF Empty(log[i]) THEN TRUE ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
  /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE (Len(log[i]) + 1)
      newEntry == log[j][newEntryIndex]
      newLog == Append(log[i],newEntry) IN
    /\ log' = [log EXCEPT![i] = newLog]
/\ UNCHANGED <<currentTerm,state,config>>
/\ Fluent10' = [Fluent10 EXCEPT![i] = FALSE]
/\ UNCHANGED <<Fluent9>>
/\ UNCHANGED <<Fluent2,Fluent1,Fluent0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RollbackEntries(i,j) ==
/\ state[i] = Secondary
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED <<currentTerm,state,config>>
/\ Fluent9' = [Fluent9 EXCEPT![i] = TRUE]
/\ Fluent10' = [Fluent10 EXCEPT![i] = TRUE]
/\ UNCHANGED <<>>
/\ UNCHANGED <<Fluent2,Fluent1,Fluent0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

BecomeLeader(i,voteQuorum,newTerm) ==
/\ newTerm = (currentTerm[i] + 1)
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]]
/\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]]
/\ UNCHANGED <<log,config>>
/\ UNCHANGED <<Fluent9,Fluent10>>
/\ Fluent1' = [Fluent1 EXCEPT![newTerm] = TRUE]
/\ UNCHANGED <<Fluent2,Fluent0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ curTerm = currentTerm[i]
/\ ind = Len(log[i])
/\ ind > 0
/\ state[i] = Primary
/\ (\A s \in commitQuorum : (Len(log[s]) >= ind /\ currentTerm[s] = curTerm))
/\ UNCHANGED <<currentTerm,state,log,config>>
/\ UNCHANGED <<Fluent9,Fluent10>>
/\ Fluent2' = [Fluent2 EXCEPT![ind][curTerm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT![curTerm] = TRUE]
/\ UNCHANGED <<Fluent1>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<log,config>>
/\ UNCHANGED <<Fluent9,Fluent10>>
/\ UNCHANGED <<Fluent2,Fluent1,Fluent0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Init ==
/\ currentTerm = [i \in Server |-> 0]
/\ state = [i \in Server |-> Secondary]
/\ log = [i \in Server |-> <<>>]
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))
/\ Fluent9 = [x0 \in Server |-> FALSE]
/\ Fluent10 = [x0 \in Server |-> FALSE]
/\ Fluent2 = [x0 \in FinNat |-> [x1 \in FinNat |-> FALSE]]
/\ Fluent1 = [x0 \in FinNat |-> FALSE]
/\ Fluent0 = [x0 \in FinNat |-> FALSE]
/\ cexTraceIdx = 0
/\ TraceConstraint

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s,t \in Server : GetEntries(s,t))
\/ (\E s,t \in Server : RollbackEntries(s,t))
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)))))
\/ (\E s,t \in Server : UpdateTerms(s,t))

Spec == (Init /\ [][Next]_vars)
=============================================================================
