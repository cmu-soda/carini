--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS n1, n2, Server, n3, Quorums, NUM2, NUM3, NUM0, NUM1, _n2n3_, _n1n2n3_, FinNat, _n1n3_, _n1n2_

VARIABLES Fluent28_21, currentTerm, Fluent2, state, config, cexTraceIdx

vars == <<Fluent28_21, currentTerm, Fluent2, state, config, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ state = (n1 :> "secondary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ Fluent28_21 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ currentTerm = (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0)
  /\ config = (n1 :> {n2} @@ n2 :> {n2} @@ n3 :> {n2})
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )

/\ cexTraceIdx = 1 =>
  /\ state = (n1 :> "secondary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ Fluent28_21 = (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ currentTerm = (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0)
  /\ config = (n1 :> {n2} @@ n2 :> {n2} @@ n3 :> {n2})
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )

/\ cexTraceIdx = 2 =>
  /\ state = (n1 :> "secondary" @@ n2 :> "primary" @@ n3 :> "secondary")
  /\ Fluent28_21 = (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> FALSE)
  /\ currentTerm = (n1 :> 0 @@ n2 :> 1 @@ n3 :> 1)
  /\ config = (n1 :> {n2} @@ n2 :> {n2} @@ n3 :> {n2})
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )

/\ cexTraceIdx = 3 =>
  /\ state = (n1 :> "secondary" @@ n2 :> "primary" @@ n3 :> "primary")
  /\ Fluent28_21 = (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE)
  /\ currentTerm = (n1 :> 2 @@ n2 :> 1 @@ n3 :> 2)
  /\ config = (n1 :> {n2} @@ n2 :> {n2} @@ n3 :> {n2})
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )


CandSep == (\A var0 \in Quorums : (\E var1 \in Server : ((var1 \in var0) => ~(Fluent28_21[var1]))))

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

StateConstraint == TRUE

MinTerm(Q) == (CHOOSE t \in FinNat : ((\A n \in Q : t <= currentTerm[n]) /\ (\E n \in Q : t = currentTerm[n])))

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
/\ UNCHANGED <<Fluent28_21>>
/\ UNCHANGED <<Fluent2>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

GetEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ Fluent28_21' = [[x0 \in Server |-> FALSE] EXCEPT![i] = TRUE]
/\ UNCHANGED <<>>
/\ UNCHANGED <<Fluent2>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RollbackEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED <<Fluent28_21>>
/\ UNCHANGED <<Fluent2>>
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
/\ Fluent28_21' = [Fluent28_21 EXCEPT![i] = TRUE]
/\ UNCHANGED <<>>
/\ UNCHANGED <<Fluent2>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

CommitEntry(i,commitQuorum,ind,curTerm,minQTerm) ==
/\ minQTerm = MinTerm(commitQuorum)
/\ curTerm = currentTerm[i]
/\ (commitQuorum \in Quorums)
/\ ind > 0
/\ state[i] = Primary
/\ (\A s \in commitQuorum : currentTerm[s] = curTerm)
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED <<Fluent28_21>>
/\ Fluent2' = [Fluent2 EXCEPT![ind][curTerm] = TRUE]
/\ UNCHANGED <<>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<config>>
/\ UNCHANGED <<Fluent28_21>>
/\ UNCHANGED <<Fluent2>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Init ==
/\ state = [i \in Server |-> Secondary]
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))
/\ currentTerm = [i \in Server |-> 0]
/\ Fluent28_21 = [x0 \in Server |-> FALSE]
/\ Fluent2 = [x0 \in FinNat |-> [x1 \in FinNat |-> FALSE]]
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
