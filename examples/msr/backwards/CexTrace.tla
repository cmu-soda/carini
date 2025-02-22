--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS n1, n2, Server, n3, Quorums, NUM2, NUM3, NUM0, NUM1, _n2n3_, _n1n2n3_, FinNat, _n1n3_, _n1n2_

VARIABLES Fluent3, Fluent2, state, cexTraceIdx

vars == <<Fluent3, Fluent2, state, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ state = (n1 :> "secondary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ Fluent2 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ Fluent3 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)

/\ cexTraceIdx = 1 =>
  /\ state = (n1 :> "secondary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ Fluent2 = (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ Fluent3 = (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE)

/\ cexTraceIdx = 2 =>
  /\ state = (n1 :> "primary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ Fluent2 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ Fluent3 = (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE)


CandSep == (\A var0 \in Server : (Fluent3[var0] => Fluent2[var0]))

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

StateConstraint == TRUE

UpdateTermsExpr(i,j) ==
/\ state' = [state EXCEPT![j] = Secondary]

ClientRequest(i,curTerm) ==
/\ UNCHANGED <<state>>
/\ UNCHANGED <<Fluent3,Fluent2>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

GetEntries(i,j) ==
/\ UNCHANGED <<state>>
/\ UNCHANGED <<Fluent3,Fluent2>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RollbackEntries(i,j) ==
/\ UNCHANGED <<state>>
/\ Fluent3' = [Fluent3 EXCEPT![i] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT![i] = TRUE]
/\ UNCHANGED <<>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

BecomeLeader(i,voteQuorum,newTerm) ==
/\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]]
/\ Fluent2' = [Fluent2 EXCEPT![i] = FALSE]
/\ UNCHANGED <<Fluent3>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ state[i] = Primary
/\ UNCHANGED <<state>>
/\ UNCHANGED <<Fluent3,Fluent2>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<Fluent3,Fluent2>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Init ==
/\ state = [i \in Server |-> Secondary]
/\ Fluent3 = [x0 \in Server |-> FALSE]
/\ Fluent2 = [x0 \in Server |-> FALSE]
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
