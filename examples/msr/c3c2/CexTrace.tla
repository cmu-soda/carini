--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS n1, n2, Server, n3, Quorums, NUM2, NUM3, NUM0, NUM1, _n2n3_, _n1n2n3_, FinNat, _n1n3_, _n1n2_

VARIABLES currentTerm, Fluent8, Fluent7, Fluent2, Fluent1, state, Fluent0, config, cexTraceIdx

vars == <<currentTerm, Fluent8, Fluent7, Fluent2, Fluent1, state, Fluent0, config, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ state = (n1 :> "secondary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ currentTerm = (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0)
  /\ config = (n1 :> {n1, n3} @@ n2 :> {n1, n3} @@ n3 :> {n1, n3})
  /\ Fluent0 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
  /\ Fluent1 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
  /\ Fluent7 = ( {n1, n2} :> FALSE @@
    {n1, n3} :> FALSE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ Fluent8 = ( {n1, n2} :> FALSE @@
    {n1, n3} :> FALSE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )

/\ cexTraceIdx = 1 =>
  /\ state = (n1 :> "primary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ currentTerm = (n1 :> 1 @@ n2 :> 1 @@ n3 :> 0)
  /\ config = (n1 :> {n1, n3} @@ n2 :> {n1, n3} @@ n3 :> {n1, n3})
  /\ Fluent0 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE)
  /\ Fluent1 = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
  /\ Fluent7 = ( {n1, n2} :> TRUE @@
    {n1, n3} :> FALSE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ Fluent8 = ( {n1, n2} :> FALSE @@
    {n1, n3} :> FALSE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )

/\ cexTraceIdx = 2 =>
  /\ state = (n1 :> "primary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ currentTerm = (n1 :> 1 @@ n2 :> 1 @@ n3 :> 0)
  /\ config = (n1 :> {n1, n3} @@ n2 :> {n1, n3} @@ n3 :> {n1, n3})
  /\ Fluent0 = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)
  /\ Fluent1 = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )
  /\ Fluent7 = ( {n1, n2} :> TRUE @@
    {n1, n3} :> FALSE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ Fluent8 = ( {n1, n2} :> FALSE @@
    {n1, n3} :> TRUE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )


CandSep == (\A var0 \in Quorums : (Fluent8[var0] => Fluent7[var0]))

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

Empty(s) == Len(s) = 0

IsPrefix(s,t) == (Len(s) <= Len(t) /\ SubSeq(s,1,Len(s)) = SubSeq(t,1,Len(s)))

CanVoteForOplog(i,j,term) ==
/\ currentTerm[i] < term

UpdateTermsExpr(i,j) ==
/\ state' = [state EXCEPT![j] = Secondary]
/\ currentTerm[i] > currentTerm[j]
/\ currentTerm' = [currentTerm EXCEPT![j] = currentTerm[i]]

ClientRequest(i,curTerm) ==
/\ state[i] = Primary
/\ currentTerm[i] = curTerm
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED <<Fluent8,Fluent7>>
/\ UNCHANGED <<Fluent2,Fluent1,Fluent0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

GetEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED <<Fluent8,Fluent7>>
/\ UNCHANGED <<Fluent2,Fluent1,Fluent0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RollbackEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED <<Fluent8,Fluent7>>
/\ UNCHANGED <<Fluent2,Fluent1,Fluent0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

BecomeLeader(i,voteQuorum,newTerm) ==
/\ newTerm = (currentTerm[i] + 1)
/\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]]
/\ (voteQuorum \in Quorums)
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]]
/\ UNCHANGED <<config>>
/\ Fluent7' = [Fluent7 EXCEPT![voteQuorum] = TRUE]
/\ UNCHANGED <<Fluent8>>
/\ Fluent1' = [Fluent1 EXCEPT![newTerm] = TRUE]
/\ UNCHANGED <<Fluent2,Fluent0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ curTerm = currentTerm[i]
/\ (commitQuorum \in Quorums)
/\ ind > 0
/\ state[i] = Primary
/\ UNCHANGED <<state,config,currentTerm>>
/\ Fluent8' = [Fluent8 EXCEPT![commitQuorum] = TRUE]
/\ UNCHANGED <<Fluent7>>
/\ Fluent2' = [Fluent2 EXCEPT![ind][curTerm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT![curTerm] = TRUE]
/\ UNCHANGED <<Fluent1>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<config>>
/\ UNCHANGED <<Fluent8,Fluent7>>
/\ UNCHANGED <<Fluent2,Fluent1,Fluent0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Init ==
/\ state = [i \in Server |-> Secondary]
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))
/\ currentTerm = [i \in Server |-> 0]
/\ Fluent8 = [x0 \in Quorums |-> FALSE]
/\ Fluent7 = [x0 \in Quorums |-> FALSE]
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
