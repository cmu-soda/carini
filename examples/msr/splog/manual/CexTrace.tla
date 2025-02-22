--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS n1, n2, Server, n3, NUM2, FinNat, NUM0, NUM1

VARIABLES Fluent12, CommitTerm, Fluent13, Fluent8, ActiveQuorum, Fluent2, Fluent1, Fluent0, CommitQuorum, BecLeaderTerm, currentTerm, ActiveTerm, ClReq, state, config, cexTraceIdx

vars == <<Fluent12, CommitTerm, Fluent13, Fluent8, ActiveQuorum, Fluent2, Fluent1, Fluent0, CommitQuorum, BecLeaderTerm, currentTerm, ActiveTerm, ClReq, state, config, cexTraceIdx>>

Quorums == { S \in SUBSET(Server) : (2 * Cardinality(S)) > Cardinality(Server) }

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ Fluent12 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ Fluent13 = ( n1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    n2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    n3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ CommitTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ state = (n1 :> "secondary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ CommitQuorum = ( {n1, n2} :> FALSE @@
    {n1, n3} :> FALSE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ Fluent0 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent1 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent8 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ ActiveQuorum = ( {n1, n2} :> FALSE @@
    {n1, n3} :> FALSE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ ActiveTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ BecLeaderTerm = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ config = (n1 :> {n1, n2} @@ n2 :> {n1, n2} @@ n3 :> {n1, n2})
  /\ currentTerm = (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0)
  /\ ClReq = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )

/\ cexTraceIdx = 1 =>
  /\ Fluent12 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ Fluent13 = ( n1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    n2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    n3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ CommitTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ state = (n1 :> "primary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ CommitQuorum = ( {n1, n2} :> FALSE @@
    {n1, n3} :> FALSE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ Fluent0 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent1 = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent8 = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ ActiveQuorum = ( {n1, n2} :> TRUE @@
    {n1, n3} :> FALSE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ ActiveTerm = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ BecLeaderTerm = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ config = (n1 :> {n1, n2} @@ n2 :> {n1, n2} @@ n3 :> {n1, n2})
  /\ currentTerm = (n1 :> 1 @@ n2 :> 1 @@ n3 :> 0)
  /\ ClReq = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )

/\ cexTraceIdx = 2 =>
  /\ Fluent12 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ Fluent13 = ( n1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    n2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    n3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ CommitTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ state = (n1 :> "primary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ CommitQuorum = ( {n1, n2} :> FALSE @@
    {n1, n3} :> FALSE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ Fluent0 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent1 = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent8 = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ ActiveQuorum = ( {n1, n2} :> TRUE @@
    {n1, n3} :> FALSE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ ActiveTerm = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ BecLeaderTerm = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ config = (n1 :> {n1, n2} @@ n2 :> {n1, n2} @@ n3 :> {n1, n2})
  /\ currentTerm = (n1 :> 1 @@ n2 :> 1 @@ n3 :> 1)
  /\ ClReq = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )

/\ cexTraceIdx = 3 =>
  /\ Fluent12 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ Fluent13 = ( n1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    n2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    n3 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ CommitTerm = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ state = (n1 :> "primary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ CommitQuorum = ( {n1, n2} :> FALSE @@
    {n1, n3} :> FALSE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ Fluent0 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent1 = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent8 = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ ActiveQuorum = ( {n1, n2} :> TRUE @@
    {n1, n3} :> FALSE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ ActiveTerm = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ BecLeaderTerm = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ config = (n1 :> {n1, n2} @@ n2 :> {n1, n2} @@ n3 :> {n1, n2})
  /\ currentTerm = (n1 :> 1 @@ n2 :> 1 @@ n3 :> 1)
  /\ ClReq = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )


CandSep ==
/\ (\A var0 \in Server : (\A var1 \in FinNat : (ClReq[var0][var1] => BecLeaderTerm[var0][var1])))

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
/\ ClReq' = [ClReq EXCEPT![i][curTerm] = TRUE]
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED <<Fluent12,Fluent13,ActiveQuorum,CommitQuorum,ActiveTerm,CommitTerm,Fluent8,BecLeaderTerm>>
/\ UNCHANGED <<Fluent2,Fluent1,Fluent0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

GetEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ Fluent12' = [Fluent12 EXCEPT![j] = TRUE]
/\ UNCHANGED <<Fluent13,ActiveQuorum,CommitQuorum,ActiveTerm,CommitTerm,Fluent8>>
/\ ClReq' = [ClReq EXCEPT![i] = [x1 \in FinNat |-> FALSE]]
/\ BecLeaderTerm' = [BecLeaderTerm EXCEPT![i] = [x1 \in FinNat |-> FALSE]]
/\ UNCHANGED <<Fluent2,Fluent1,Fluent0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RollbackEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ Fluent13' = [Fluent13 EXCEPT![j][i] = TRUE]
/\ UNCHANGED <<Fluent12,ActiveQuorum,CommitQuorum,ActiveTerm,CommitTerm,Fluent8>>
/\ ClReq' = [ClReq EXCEPT![i] = [x1 \in FinNat |-> FALSE]]
/\ BecLeaderTerm' = [BecLeaderTerm EXCEPT![i] = [x1 \in FinNat |-> FALSE]]
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
/\ UNCHANGED <<Fluent12,Fluent13>>
/\ ActiveQuorum' = [[q \in Quorums |-> FALSE] EXCEPT![voteQuorum] = TRUE]
/\ CommitQuorum' = [q \in Quorums |-> FALSE]
/\ ActiveTerm' = [[x \in FinNat |-> FALSE] EXCEPT![newTerm] = TRUE]
/\ CommitTerm' = [x \in FinNat |-> FALSE]
/\ ClReq' = [s \in Server |-> IF (s \in voteQuorum) THEN [x1 \in FinNat |-> FALSE] ELSE ClReq[s]]
/\ BecLeaderTerm' = [[s \in Server |-> IF (s \in voteQuorum) THEN [x1 \in FinNat |-> FALSE] ELSE BecLeaderTerm[s]] EXCEPT![i][newTerm] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT![newTerm] = TRUE]
/\ Fluent8' = [Fluent8 EXCEPT![newTerm] = TRUE]
/\ UNCHANGED <<Fluent2,Fluent0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ curTerm = currentTerm[i]
/\ (commitQuorum \in Quorums)
/\ ind > 0
/\ state[i] = Primary
/\ (\A s \in commitQuorum : currentTerm[s] = curTerm)
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED <<Fluent12,Fluent13>>
/\ CommitQuorum' = [CommitQuorum EXCEPT![commitQuorum] = TRUE]
/\ CommitTerm' = [CommitTerm EXCEPT![curTerm] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT![ind][curTerm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT![curTerm] = TRUE]
/\ UNCHANGED <<Fluent1,ActiveQuorum,ActiveTerm,Fluent8,ClReq,BecLeaderTerm>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<config>>
/\ ClReq' = [ClReq EXCEPT![i] = [x1 \in FinNat |-> FALSE]]
/\ BecLeaderTerm' = [BecLeaderTerm EXCEPT![i] = [x1 \in FinNat |-> FALSE]]
/\ UNCHANGED <<Fluent12,Fluent13,ActiveQuorum,CommitQuorum,Fluent8>>
/\ UNCHANGED <<Fluent2,Fluent1,Fluent0,ActiveTerm,CommitTerm>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Init ==
/\ state = [i \in Server |-> Secondary]
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))
/\ currentTerm = [i \in Server |-> 0]
/\ Fluent8 = [x0 \in FinNat |-> FALSE]
/\ Fluent12 = [x0 \in Server |-> FALSE]
/\ Fluent13 = [x0 \in Server |-> [x1 \in Server |-> FALSE]]
/\ Fluent2 = [x0 \in FinNat |-> [x1 \in FinNat |-> FALSE]]
/\ Fluent1 = [x0 \in FinNat |-> FALSE]
/\ Fluent0 = [x0 \in FinNat |-> FALSE]
/\ ActiveQuorum = [q \in Quorums |-> FALSE]
/\ CommitQuorum = [q \in Quorums |-> FALSE]
/\ ActiveTerm = [x \in FinNat |-> FALSE]
/\ CommitTerm = [x \in FinNat |-> FALSE]
/\ ClReq = [x0 \in Server |-> [x1 \in FinNat |-> FALSE]]
/\ BecLeaderTerm = [x0 \in Server |-> [x1 \in FinNat |-> FALSE]]
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
