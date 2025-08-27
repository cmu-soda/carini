--------------------------- MODULE T2_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent60_4, Fluent41_1, Fluent2, Fluent52_5, Fluent33_2, Fluent31_7, Fluent32_7, Fluent20_14, Fluent34_2, currentTerm, Fluent53_5, Fluent21_17, Fluent22_17, Fluent19_4, Fluent18_4, state, config

vars == <<Fluent60_4, Fluent41_1, Fluent2, Fluent52_5, Fluent33_2, Fluent31_7, Fluent32_7, Fluent20_14, Fluent34_2, currentTerm, Fluent53_5, Fluent21_17, Fluent22_17, Fluent19_4, Fluent18_4, state, config>>

CandSep ==
/\ \A var0 \in Server : \A var1 \in Server : \A var2 \in FinNat : (var0 = var1) => ((Fluent52_5[var0][var2]) => (Fluent53_5[var0][var2]))
/\ \A var0 \in FinNat : \E var1 \in Server : \A var2 \in Server : (Fluent60_4[var2][var0]) => (var2 = var1)
/\ \A var0 \in FinNat : (Fluent33_2[var0]) => (Fluent34_2[var0])
/\ \A var0 \in Server : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent41_1[var0][var2]) => (var1 = var2)
/\ \A var0 \in FinNat : (Fluent19_4[var0]) => (~(Fluent18_4[var0]))
/\ \A var0 \in FinNat : \A var1 \in FinNat : (Fluent32_7[var0]) => ((Fluent31_7[var1]) => (var1 <= var0))
/\ \A var0 \in FinNat : (Fluent21_17[var0]) => (Fluent22_17[var0])
/\ \A var0 \in FinNat : \E var1 \in FinNat : (Fluent20_14[var0]) => (~(var0 <= var1))

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
/\ Fluent41_1' = [Fluent41_1 EXCEPT ![i][curTerm] = TRUE]
/\ Fluent52_5' = [Fluent52_5 EXCEPT ![i][curTerm] = TRUE]
/\ Fluent21_17' = [Fluent21_17 EXCEPT ![curTerm] = TRUE]
/\ Fluent22_17' = [x0 \in FinNat |-> TRUE]
/\ UNCHANGED<<Fluent60_4, Fluent33_2, Fluent31_7, Fluent32_7, Fluent20_14, Fluent34_2, Fluent53_5, Fluent19_4, Fluent18_4>>
/\ UNCHANGED<<Fluent2>>

GetEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ Fluent52_5' = [x0 \in Server |-> [x1 \in FinNat |-> FALSE]]
/\ Fluent53_5' = [Fluent53_5 EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ UNCHANGED<<Fluent60_4, Fluent41_1, Fluent33_2, Fluent31_7, Fluent32_7, Fluent20_14, Fluent34_2, Fluent21_17, Fluent22_17, Fluent19_4, Fluent18_4>>
/\ UNCHANGED<<Fluent2>>

RollbackEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED<<Fluent60_4, Fluent41_1, Fluent52_5, Fluent33_2, Fluent31_7, Fluent32_7, Fluent20_14, Fluent34_2, Fluent53_5, Fluent21_17, Fluent22_17, Fluent19_4, Fluent18_4>>
/\ UNCHANGED<<Fluent2>>

BecomeLeader(i,voteQuorum,newTerm) ==
/\ newTerm = (currentTerm[i] + 1)
/\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]]
/\ (voteQuorum \in Quorums)
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]]
/\ UNCHANGED <<config>>
/\ Fluent60_4' = [Fluent60_4 EXCEPT ![i][newTerm] = TRUE]
/\ Fluent41_1' = [Fluent41_1 EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ Fluent31_7' = [Fluent31_7 EXCEPT ![newTerm] = TRUE]
/\ Fluent32_7' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ Fluent20_14' = [Fluent20_14 EXCEPT ![newTerm] = TRUE]
/\ Fluent53_5' = [Fluent53_5 EXCEPT ![i][newTerm] = TRUE]
/\ Fluent22_17' = [Fluent22_17 EXCEPT ![newTerm] = FALSE]
/\ Fluent19_4' = [[x0 \in FinNat |-> TRUE] EXCEPT ![newTerm] = FALSE]
/\ Fluent18_4' = [x0 \in FinNat |-> FALSE]
/\ UNCHANGED<<Fluent52_5, Fluent33_2, Fluent34_2, Fluent21_17>>
/\ UNCHANGED<<Fluent2>>

CommitEntry(i,commitQuorum,ind,curTerm,minQTerm) ==
/\ minQTerm = MinTerm(commitQuorum)
/\ curTerm = currentTerm[i]
/\ (commitQuorum \in Quorums)
/\ ind > 0
/\ state[i] = Primary
/\ (\A s \in commitQuorum : currentTerm[s] = curTerm)
/\ UNCHANGED <<state,config,currentTerm>>
/\ Fluent33_2' = [Fluent33_2 EXCEPT ![minQTerm] = TRUE]
/\ Fluent34_2' = [Fluent34_2 EXCEPT ![curTerm] = TRUE]
/\ Fluent18_4' = [Fluent18_4 EXCEPT ![minQTerm] = TRUE]
/\ UNCHANGED<<Fluent60_4, Fluent41_1, Fluent52_5, Fluent31_7, Fluent32_7, Fluent20_14, Fluent53_5, Fluent21_17, Fluent22_17, Fluent19_4>>
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ UNCHANGED<<>>

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<config>>
/\ UNCHANGED<<Fluent60_4, Fluent41_1, Fluent52_5, Fluent33_2, Fluent31_7, Fluent32_7, Fluent20_14, Fluent34_2, Fluent53_5, Fluent21_17, Fluent22_17, Fluent19_4, Fluent18_4>>
/\ UNCHANGED<<Fluent2>>

Init ==
/\ state = [i \in Server |-> Secondary]
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))
/\ currentTerm = [i \in Server |-> 0]
/\ Fluent60_4 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent41_1 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent52_5 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent33_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent31_7 = [ x0 \in FinNat |-> FALSE]
/\ Fluent32_7 = [ x0 \in FinNat |-> FALSE]
/\ Fluent20_14 = [ x0 \in FinNat |-> FALSE]
/\ Fluent34_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent53_5 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent21_17 = [ x0 \in FinNat |-> FALSE]
/\ Fluent22_17 = [ x0 \in FinNat |-> FALSE]
/\ Fluent19_4 = [ x0 \in FinNat |-> FALSE]
/\ Fluent18_4 = [ x0 \in FinNat |-> FALSE]
/\ Fluent2 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s,t \in Server : GetEntries(s,t))
\/ (\E s,t \in Server : RollbackEntries(s,t))
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : (\E minQTerm \in FinNat : CommitEntry(s,Q,ind,curTerm,minQTerm))))))
\/ (\E s,t \in Server : UpdateTerms(s,t))

Spec == (Init /\ [][Next]_vars)
=============================================================================
