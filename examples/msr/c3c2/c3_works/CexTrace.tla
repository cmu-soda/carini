--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS n1, n2, Server, n3, Quorums, NUM2, NUM3, NUM0, NUM1, _n2n3_, _n1n2n3_, FinNat, _n1n3_, _n1n2_

VARIABLES currentTerm, Fluent26_8, Fluent2, state, Fluent27_8, config, cexTraceIdx

vars == <<currentTerm, Fluent26_8, Fluent2, state, Fluent27_8, config, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ state = (n1 :> "secondary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ currentTerm = (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0)
  /\ config = (n1 :> {n1, n2, n3} @@ n2 :> {n1, n2, n3} @@ n3 :> {n1, n2, n3})
  /\ Fluent26_8 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ Fluent27_8 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )

/\ cexTraceIdx = 1 =>
  /\ state = (n1 :> "primary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ currentTerm = (n1 :> 1 @@ n2 :> 1 @@ n3 :> 0)
  /\ config = (n1 :> {n1, n2, n3} @@ n2 :> {n1, n2, n3} @@ n3 :> {n1, n2, n3})
  /\ Fluent26_8 = (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ Fluent27_8 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )

/\ cexTraceIdx = 2 =>
  /\ state = (n1 :> "primary" @@ n2 :> "secondary" @@ n3 :> "secondary")
  /\ currentTerm = (n1 :> 1 @@ n2 :> 1 @@ n3 :> 0)
  /\ config = (n1 :> {n1, n2, n3} @@ n2 :> {n1, n2, n3} @@ n3 :> {n1, n2, n3})
  /\ Fluent26_8 = (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ Fluent27_8 = (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )

/\ cexTraceIdx = 3 =>
  /\ state = (n1 :> "secondary" @@ n2 :> "primary" @@ n3 :> "secondary")
  /\ currentTerm = (n1 :> 2 @@ n2 :> 2 @@ n3 :> 0)
  /\ config = (n1 :> {n1, n2, n3} @@ n2 :> {n1, n2, n3} @@ n3 :> {n1, n2, n3})
  /\ Fluent26_8 = (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> FALSE)
  /\ Fluent27_8 = (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )

/\ cexTraceIdx = 4 =>
  /\ state = (n1 :> "secondary" @@ n2 :> "primary" @@ n3 :> "secondary")
  /\ currentTerm = (n1 :> 2 @@ n2 :> 2 @@ n3 :> 0)
  /\ config = (n1 :> {n1, n2, n3} @@ n2 :> {n1, n2, n3} @@ n3 :> {n1, n2, n3})
  /\ Fluent26_8 = (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE)
  /\ Fluent27_8 = (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ Fluent2 = ( 0 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) @@
    3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE) )


CandSep == (\A var0 \in Server : (Fluent27_8[var0] => Fluent26_8[var0]))

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

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
/\ Fluent27_8' = [Fluent27_8 EXCEPT![i] = TRUE]
/\ UNCHANGED <<Fluent26_8>>
/\ UNCHANGED <<Fluent2>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

GetEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ Fluent26_8' = [Fluent26_8 EXCEPT![i] = FALSE]
/\ UNCHANGED <<Fluent27_8>>
/\ UNCHANGED <<Fluent2>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RollbackEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED <<Fluent26_8,Fluent27_8>>
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
/\ Fluent26_8' = [Fluent26_8 EXCEPT![i] = TRUE]
/\ UNCHANGED <<Fluent27_8>>
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
/\ UNCHANGED <<Fluent26_8,Fluent27_8>>
/\ Fluent2' = [Fluent2 EXCEPT![ind][curTerm] = TRUE]
/\ UNCHANGED <<>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<config>>
/\ UNCHANGED <<Fluent26_8,Fluent27_8>>
/\ UNCHANGED <<Fluent2>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Init ==
/\ state = [i \in Server |-> Secondary]
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))
/\ currentTerm = [i \in Server |-> 0]
/\ Fluent26_8 = [x0 \in Server |-> FALSE]
/\ Fluent27_8 = [x0 \in Server |-> FALSE]
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
