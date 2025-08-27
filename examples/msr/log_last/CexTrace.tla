--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS n1, n2, Server, n3, Quorums, NUM2, NUM3, NUM0, NUM1, _n2n3_, _n1n2n3_, FinNat, _n1n3_, _n1n2_

VARIABLES log, Fluent19_20, Fluent20_20, cexTraceIdx

vars == <<log, Fluent19_20, Fluent20_20, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ Fluent20_20 = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
  /\ log = (n1 :> <<>> @@ n2 :> <<>> @@ n3 :> <<>>)
  /\ Fluent19_20 = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )

/\ cexTraceIdx = 1 =>
  /\ Fluent20_20 = ( n1 :> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
  /\ log = (n1 :> <<2>> @@ n2 :> <<>> @@ n3 :> <<>>)
  /\ Fluent19_20 = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )

/\ cexTraceIdx = 2 =>
  /\ Fluent20_20 = ( n1 :> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
  /\ log = (n1 :> <<2>> @@ n2 :> <<2>> @@ n3 :> <<>>)
  /\ Fluent19_20 = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )

/\ cexTraceIdx = 3 =>
  /\ Fluent20_20 = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
  /\ log = (n1 :> <<2>> @@ n2 :> <<2>> @@ n3 :> <<>>)
  /\ Fluent19_20 = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )

/\ cexTraceIdx = 4 =>
  /\ Fluent20_20 = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
  /\ log = (n1 :> <<2>> @@ n2 :> <<2>> @@ n3 :> <<>>)
  /\ Fluent19_20 = ( n1 :> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE) @@
    n2 :> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE) @@
    n3 :> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE) )


CandSep == (\A var0 \in Quorums : (\A var1 \in FinNat : (\E var2 \in Server : (Fluent19_20[var2][var1] => ((var2 \in var0) => Fluent20_20[var2][var1])))))

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
/\ ~(IsPrefix(log[i],log[j]))

CanVoteForOplog(i,j,term) ==
LET logOk == (LastTerm(log[j]) > LastTerm(log[i]) \/ (LastTerm(log[j]) = LastTerm(log[i]) /\ Len(log[j]) >= Len(log[i]))) IN
  /\ logOk

ClientRequest(i,curTerm,idx) ==
/\ idx = (Len(log[i]) + 1)
/\ log' = [log EXCEPT![i] = Append(log[i],curTerm)]
/\ Fluent20_20' = [Fluent20_20 EXCEPT![i] = [x0 \in FinNat |-> TRUE]]
/\ UNCHANGED <<Fluent19_20>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

GetEntries(i,j,idx) ==
/\ Len(log[j]) > Len(log[i])
/\ LET logOk == IF Empty(log[i]) THEN TRUE ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
  /\ logOk
  /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE (Len(log[i]) + 1)
      newEntry == log[j][newEntryIndex]
      newLog == Append(log[i],newEntry) IN
    /\ log' = [log EXCEPT![i] = newLog]
    /\ idx = Len(newLog)
/\ UNCHANGED <<Fluent19_20,Fluent20_20>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RollbackEntries(i,j,idx) ==
/\ idx = Len(log[i])
/\ CanRollback(i,j)
/\ log' = [log EXCEPT![i] = SubSeq(log[i],1,(Len(log[i]) - 1))]
/\ UNCHANGED <<Fluent19_20,Fluent20_20>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

BecomeLeader(i,voteQuorum,newTerm,idx) ==
/\ idx = (Len(log[i]) + 1)
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ UNCHANGED <<log>>
/\ Fluent19_20' = [Fluent19_20 EXCEPT![i][idx] = FALSE]
/\ Fluent20_20' = [Fluent20_20 EXCEPT![i][newTerm] = FALSE]
/\ UNCHANGED <<>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ ind = Len(log[i])
/\ ind > 0
/\ log[i][ind] = curTerm
/\ (\A s \in commitQuorum : (Len(log[s]) >= ind /\ InLog(<<ind,curTerm>>,s)))
/\ UNCHANGED <<log>>
/\ Fluent19_20' = [x0 \in Server |-> [x1 \in FinNat |-> TRUE]]
/\ UNCHANGED <<Fluent20_20>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Init ==
/\ log = [i \in Server |-> <<>>]
/\ Fluent19_20 = [x0 \in Server |-> [x1 \in FinNat |-> FALSE]]
/\ Fluent20_20 = [x0 \in Server |-> [x1 \in FinNat |-> FALSE]]
/\ cexTraceIdx = 0
/\ TraceConstraint

Next ==
\/ (\E s \in Server : (\E t,idx \in FinNat : ClientRequest(s,t,idx)))
\/ (\E s,t \in Server : (\E idx \in FinNat : GetEntries(s,t,idx)))
\/ (\E s,t \in Server : (\E idx \in FinNat : RollbackEntries(s,t,idx)))
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm,idx \in FinNat : BecomeLeader(s,Q,newTerm,idx))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)))))

Spec == (Init /\ [][Next]_vars)
=============================================================================
