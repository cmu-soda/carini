--------------------------- MODULE T2_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent9, currentTerm, Fluent8, Fluent7, Fluent2, Fluent1, state, Fluent0, config

vars == <<Fluent9, currentTerm, Fluent8, Fluent7, Fluent2, Fluent1, state, Fluent0, config>>

CandSep ==
\A var0 \in Server : \E var1 \in Server : \A var2 \in Quorums : (Fluent9[var2][var0]) => ((Fluent7[var2]) => (Fluent8[var2][var1]))

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
/\ UNCHANGED<<Fluent9, Fluent8, Fluent7>>
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>

GetEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED<<Fluent9, Fluent8, Fluent7>>
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>

RollbackEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED<<Fluent9, Fluent8, Fluent7>>
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>

BecomeLeader(i,voteQuorum,newTerm) ==
/\ newTerm = (currentTerm[i] + 1)
/\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]]
/\ (voteQuorum \in Quorums)
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]]
/\ UNCHANGED <<config>>
/\ Fluent9' = [Fluent9 EXCEPT ![voteQuorum][i] = TRUE]
/\ Fluent7' = [Fluent7 EXCEPT ![voteQuorum] = FALSE]
/\ UNCHANGED<<Fluent8>>
/\ Fluent1' = [Fluent1 EXCEPT ![newTerm] = TRUE]
/\ UNCHANGED<<Fluent2, Fluent0>>

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ curTerm = currentTerm[i]
/\ (commitQuorum \in Quorums)
/\ ind > 0
/\ state[i] = Primary
/\ UNCHANGED <<state,config,currentTerm>>
/\ Fluent9' = [Fluent9 EXCEPT ![commitQuorum][i] = TRUE]
/\ Fluent8' = [Fluent8 EXCEPT ![commitQuorum][i] = TRUE]
/\ Fluent7' = [Fluent7 EXCEPT ![commitQuorum] = TRUE]
/\ UNCHANGED<<>>
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent1>>

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<config>>
/\ UNCHANGED<<Fluent9, Fluent8, Fluent7>>
/\ UNCHANGED<<Fluent2, Fluent1, Fluent0>>

Init ==
/\ state = [i \in Server |-> Secondary]
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))
/\ currentTerm = [i \in Server |-> 0]
/\ Fluent9 = [ x0 \in Quorums |-> [ x1 \in Server |-> FALSE]]
/\ Fluent8 = [ x0 \in Quorums |-> [ x1 \in Server |-> FALSE]]
/\ Fluent7 = [ x0 \in Quorums |-> FALSE]
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
=============================================================================
