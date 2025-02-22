--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS n1, n2, Server, n3, Quorums, NUM2, NUM3, NUM0, NUM1, _n2n3_, _n1n2n3_, FinNat, _n1n3_, _n1n2_

VARIABLES Fluent11_16, currentTerm, log, state, Fluent12_16, config, cexTraceIdx

vars == <<Fluent11_16, currentTerm, log, state, Fluent12_16, config, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ log = (n1 :> <<>> @@ n2 :> <<>> @@ n3 :> <<>>)
  /\ state = (n1 :> "secondary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ Fluent12_16 = ( 0 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ config = (n1 :> {n2} @@ n2 :> {n2} @@ n3 :> {n2})
  /\ Fluent11_16 = ( {n1, n2} :> FALSE @@
    {n1, n3} :> FALSE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ currentTerm = (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0)

/\ cexTraceIdx = 1 =>
  /\ log = (n1 :> <<>> @@ n2 :> <<>> @@ n3 :> <<>>)
  /\ state = (n1 :> "primary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ Fluent12_16 = ( 0 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ config = (n1 :> {n2} @@ n2 :> {n2} @@ n3 :> {n2})
  /\ Fluent11_16 = ( {n1, n2} :> FALSE @@
    {n1, n3} :> TRUE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ currentTerm = (n1 :> 1 @@ n2 :> 0 @@ n3 :> 1)

/\ cexTraceIdx = 2 =>
  /\ log = (n1 :> <<1>> @@ n2 :> <<>> @@ n3 :> <<>>)
  /\ state = (n1 :> "primary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ Fluent12_16 = ( 0 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ config = (n1 :> {n2} @@ n2 :> {n2} @@ n3 :> {n2})
  /\ Fluent11_16 = ( {n1, n2} :> FALSE @@
    {n1, n3} :> TRUE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ currentTerm = (n1 :> 1 @@ n2 :> 0 @@ n3 :> 1)

/\ cexTraceIdx = 3 =>
  /\ log = (n1 :> <<1>> @@ n2 :> <<>> @@ n3 :> <<1>>)
  /\ state = (n1 :> "primary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ Fluent12_16 = ( 0 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ config = (n1 :> {n2} @@ n2 :> {n2} @@ n3 :> {n2})
  /\ Fluent11_16 = ( {n1, n2} :> FALSE @@
    {n1, n3} :> TRUE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ currentTerm = (n1 :> 1 @@ n2 :> 0 @@ n3 :> 1)

/\ cexTraceIdx = 4 =>
  /\ log = (n1 :> <<1>> @@ n2 :> <<>> @@ n3 :> <<1>>)
  /\ state = (n1 :> "primary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ Fluent12_16 = ( 0 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    1 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ config = (n1 :> {n2} @@ n2 :> {n2} @@ n3 :> {n2})
  /\ Fluent11_16 = ( {n1, n2} :> FALSE @@
    {n1, n3} :> TRUE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ currentTerm = (n1 :> 1 @@ n2 :> 0 @@ n3 :> 1)

/\ cexTraceIdx = 5 =>
  /\ log = (n1 :> <<1>> @@ n2 :> <<>> @@ n3 :> <<1>>)
  /\ state = (n1 :> "primary" @@ n2 :> "secondary" @@ n3 :> "primary")
  /\ Fluent12_16 = ( 0 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    1 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ config = (n1 :> {n2} @@ n2 :> {n2} @@ n3 :> {n2})
  /\ Fluent11_16 = ( {n1, n2} :> FALSE @@
    {n1, n3} :> TRUE @@
    {n2, n3} :> TRUE @@
    {n1, n2, n3} :> FALSE )
  /\ currentTerm = (n1 :> 1 @@ n2 :> 2 @@ n3 :> 2)


CandSep == (\A var0 \in FinNat : (\A var1 \in Server : (\A var2 \in Quorums : (Fluent11_16[var2] => (Fluent12_16[var0][var1] => (var1 \in var2))))))

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

StateConstraint == (\A s \in Server : Len(log[s]) < 4)

MinTerm(Q) == (CHOOSE t \in FinNat : ((\A n \in Q : t <= currentTerm[n]) /\ (\E n \in Q : t = currentTerm[n])))

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
/\ UNCHANGED <<Fluent11_16,Fluent12_16>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

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
/\ UNCHANGED <<Fluent11_16,Fluent12_16>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RollbackEntries(i,j) ==
/\ state[i] = Secondary
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED <<currentTerm,state,config>>
/\ UNCHANGED <<Fluent11_16,Fluent12_16>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (voteQuorum \in Quorums)
/\ newTerm = (currentTerm[i] + 1)
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]]
/\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]]
/\ UNCHANGED <<log,config>>
/\ Fluent11_16' = [Fluent11_16 EXCEPT![voteQuorum] = TRUE]
/\ UNCHANGED <<Fluent12_16>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

CommitEntry(i,commitQuorum,ind,curTerm,minQTerm) ==
/\ minQTerm = MinTerm(commitQuorum)
/\ (commitQuorum \in Quorums)
/\ curTerm = currentTerm[i]
/\ ind = Len(log[i])
/\ ind > 0
/\ state[i] = Primary
/\ log[i][ind] = curTerm
/\ ImmediatelyCommitted(<<ind,curTerm>>,commitQuorum)
/\ UNCHANGED <<currentTerm,state,log,config>>
/\ Fluent12_16' = [Fluent12_16 EXCEPT![minQTerm][i] = TRUE]
/\ UNCHANGED <<Fluent11_16>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<log,config>>
/\ UNCHANGED <<Fluent11_16,Fluent12_16>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Init ==
/\ currentTerm = [i \in Server |-> 0]
/\ state = [i \in Server |-> Secondary]
/\ log = [i \in Server |-> <<>>]
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))
/\ Fluent11_16 = [x0 \in Quorums |-> FALSE]
/\ Fluent12_16 = [x0 \in FinNat |-> [x1 \in Server |-> FALSE]]
/\ cexTraceIdx = 0
/\ TraceConstraint

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s,t \in Server : GetEntries(s,t))
\/ (\E s,t \in Server : RollbackEntries(s,t))
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : (\E minQTerm \in FinNat : CommitEntry(s,Q,ind,curTerm,minQTerm))))))
\/ (\E s,t \in Server : UpdateTerms(s,t))

Spec == (Init /\ [][Next]_vars)
=============================================================================
