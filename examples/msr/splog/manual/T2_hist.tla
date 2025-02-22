--------------------------- MODULE T2_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

\*CONSTANTS Server, Quorums, FinNat

CONSTANTS Server, FinNat
Quorums == {S \in SUBSET Server : 2*Cardinality(S) > Cardinality(Server)}

VARIABLES Fluent12, currentTerm, Fluent13, Fluent2, Fluent1, state, Fluent0, config, ActiveQuorum, CommitQuorum, ActiveTerm, CommitTerm, Fluent8, ClReq, BecLeaderTerm

vars == <<Fluent12, currentTerm, Fluent13, Fluent2, Fluent1, state, Fluent0, config, ActiveQuorum, CommitQuorum, ActiveTerm, CommitTerm, Fluent8, ClReq, BecLeaderTerm>>

CandSep ==
\*\A var0 \in Server : \A var1 \in Server : (Fluent12[var0]) => ((Fluent13[var0][var1]) => (var0 = var1))
/\ \A var0 \in Server : \A var1 \in FinNat : ClReq[var0][var1] => BecLeaderTerm[var0][var1]
\*/\ \A var0 \in Quorums : \A var1 \in Quorums : CommitQuorum[var0] => (ActiveQuorum[var1] => (var0 \cap var1 # {}))
\*/\ \A var0 \in FinNat : CommitTerm[var0] => ActiveTerm[var0]
\*/\ \A var0 \in FinNat : \A var1 \in FinNat : ActiveTerm[var0] => (Fluent8[var1] => (var1 <= var0))
/\ \A ind,t \in FinNat : (Fluent2[ind][t] /\ ActiveTerm[t]) => CommitTerm[t]
/\ \A t \in FinNat : ActiveTerm[t] => \E s \in Server : BecLeaderTerm[s][t]

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
/\ ClReq' = [ClReq EXCEPT ![i][curTerm] = TRUE]
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED<<Fluent12, Fluent13, ActiveQuorum, CommitQuorum, ActiveTerm, CommitTerm, Fluent8, BecLeaderTerm>>
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>

GetEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ Fluent12' = [Fluent12 EXCEPT ![j] = TRUE]
/\ UNCHANGED<<Fluent13, ActiveQuorum, CommitQuorum, ActiveTerm, CommitTerm, Fluent8>>
/\ ClReq' = [ClReq EXCEPT ![i] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ BecLeaderTerm' = [BecLeaderTerm EXCEPT ![i] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>

RollbackEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ Fluent13' = [Fluent13 EXCEPT ![j][i] = TRUE]
/\ UNCHANGED<<Fluent12, ActiveQuorum, CommitQuorum, ActiveTerm, CommitTerm, Fluent8>>
/\ ClReq' = [ClReq EXCEPT ![i] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ BecLeaderTerm' = [BecLeaderTerm EXCEPT ![i] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>

BecomeLeader(i,voteQuorum,newTerm) ==
/\ newTerm = (currentTerm[i] + 1)
/\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]]
/\ (voteQuorum \in Quorums)
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]]
/\ UNCHANGED <<config>>
/\ UNCHANGED<<Fluent12, Fluent13>>
/\ ActiveQuorum' = [[q \in Quorums |-> FALSE] EXCEPT ![voteQuorum] = TRUE]
/\ CommitQuorum' = [q \in Quorums |-> FALSE]
/\ ActiveTerm' = [[x \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ CommitTerm' = [x \in FinNat |-> FALSE]
/\ ClReq' = [s \in Server |-> IF (s \in voteQuorum) THEN [x1 \in FinNat |-> FALSE] ELSE ClReq[s]] \* specialized fluent
/\ BecLeaderTerm' = [[s \in Server |-> IF (s \in voteQuorum) THEN [x1 \in FinNat |-> FALSE] ELSE BecLeaderTerm[s]] EXCEPT![i][newTerm] = TRUE] \* specialized fluent
/\ Fluent1' = [Fluent1 EXCEPT ![newTerm] = TRUE]
/\ Fluent8' = [Fluent8 EXCEPT ![newTerm] = TRUE]
/\ UNCHANGED<<Fluent2, Fluent0>>

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ curTerm = currentTerm[i]
/\ (commitQuorum \in Quorums)
/\ ind > 0
/\ state[i] = Primary
/\ (\A s \in commitQuorum : currentTerm[s] = curTerm)
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED<<Fluent12, Fluent13>>
/\ CommitQuorum' = [CommitQuorum EXCEPT ![commitQuorum] = TRUE]
/\ CommitTerm' = [CommitTerm EXCEPT ![curTerm] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent1, ActiveQuorum, ActiveTerm, Fluent8, ClReq, BecLeaderTerm>>

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<config>>
/\ ClReq' = [ClReq EXCEPT ![j] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ BecLeaderTerm' = [BecLeaderTerm EXCEPT ![j] = [x1 \in FinNat |-> FALSE]] \* specialized fluent
/\ UNCHANGED<<Fluent12, Fluent13, ActiveQuorum, CommitQuorum, Fluent8>>
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0, ActiveTerm, CommitTerm>>

Init ==
/\ state = [i \in Server |-> Secondary]
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))
/\ currentTerm = [i \in Server |-> 0]
/\ Fluent8 = [ x0 \in FinNat |-> FALSE]
/\ Fluent12 = [ x0 \in Server |-> FALSE]
/\ Fluent13 = [ x0 \in Server |-> [ x1 \in Server |-> FALSE]]
/\ Fluent2 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent1 = [ x0 \in FinNat |-> FALSE]
/\ Fluent0 = [ x0 \in FinNat |-> FALSE]
/\ ActiveQuorum = [ q \in Quorums |-> FALSE]
/\ CommitQuorum = [ q \in Quorums |-> FALSE]
/\ ActiveTerm = [x \in FinNat |-> FALSE]
/\ CommitTerm = [x \in FinNat |-> FALSE]
/\ ClReq = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ BecLeaderTerm = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s,t \in Server : GetEntries(s,t))
\/ (\E s,t \in Server : RollbackEntries(s,t))
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)))))
\/ (\E s,t \in Server : UpdateTerms(s,t))

Spec == (Init /\ [][Next]_vars)
=============================================================================
