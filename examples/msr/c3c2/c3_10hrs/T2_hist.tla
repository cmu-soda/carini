--------------------------- MODULE T2_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent2, Fluent31_1, Fluent20_3, Fluent35_3, Fluent36_3, currentTerm, Fluent34_3, Fluent28_2, Fluent37_3, Fluent16_5, Fluent29_2, Fluent15_5, Fluent19_3, state, config

vars == <<Fluent2, Fluent31_1, Fluent20_3, Fluent35_3, Fluent36_3, currentTerm, Fluent34_3, Fluent28_2, Fluent37_3, Fluent16_5, Fluent29_2, Fluent15_5, Fluent19_3, state, config>>

CandSep ==
/\ \A var0 \in Server : (Fluent37_3[var0]) => (Fluent36_3[var0])
/\ \A var0 \in Server : (Fluent34_3[var0]) => (Fluent35_3[var0])
/\ \A var0 \in FinNat : \E var1 \in FinNat : ((var0 <= var1) => (Fluent29_2[var1])) => (~(Fluent28_2[var0]))
/\ \A var0 \in FinNat : (Fluent16_5[var0]) => (Fluent15_5[var0])
/\ \A var0 \in Server : \A var1 \in FinNat : (Fluent19_3[var0][var1]) => (Fluent20_3[var0][var1])
/\ \A var0 \in Server : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent31_1[var0][var2]) => (var1 = var2)

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

StateConstraint == TRUE

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
/\ Fluent35_3' = [Fluent35_3 EXCEPT ![i] = FALSE]
/\ Fluent19_3' = [Fluent19_3 EXCEPT ![i][curTerm] = TRUE]
/\ Fluent31_1' = [Fluent31_1 EXCEPT ![i][curTerm] = TRUE]
/\ UNCHANGED<<Fluent36_3, Fluent34_3, Fluent28_2, Fluent37_3, Fluent16_5, Fluent29_2, Fluent15_5, Fluent20_3>>
/\ UNCHANGED<<Fluent2>>

GetEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ Fluent35_3' = [Fluent35_3 EXCEPT ![i] = TRUE]
/\ Fluent34_3' = [Fluent34_3 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent36_3, Fluent28_2, Fluent37_3, Fluent16_5, Fluent29_2, Fluent15_5, Fluent19_3, Fluent31_1, Fluent20_3>>
/\ UNCHANGED<<Fluent2>>

RollbackEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED<<Fluent35_3, Fluent36_3, Fluent34_3, Fluent28_2, Fluent37_3, Fluent16_5, Fluent29_2, Fluent15_5, Fluent19_3, Fluent31_1, Fluent20_3>>
/\ UNCHANGED<<Fluent2>>

BecomeLeader(i,newTerm) ==
/\ (\E voteQuorum \in Quorums : (newTerm = (currentTerm[i] + 1) /\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]] /\ (voteQuorum \in Quorums) /\ (i \in voteQuorum) /\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm)) /\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]] /\ UNCHANGED <<config>>))
/\ Fluent36_3' = [Fluent36_3 EXCEPT ![i] = TRUE]
/\ Fluent34_3' = [Fluent34_3 EXCEPT ![i] = FALSE]
/\ Fluent28_2' = [Fluent28_2 EXCEPT ![newTerm] = TRUE]
/\ Fluent16_5' = [x0 \in FinNat |-> FALSE]
/\ Fluent29_2' = [[x0 \in FinNat |-> TRUE] EXCEPT ![newTerm] = FALSE]
/\ Fluent15_5' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ Fluent31_1' = [Fluent31_1 EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ Fluent20_3' = [Fluent20_3 EXCEPT ![i][newTerm] = TRUE]
/\ UNCHANGED<<Fluent35_3, Fluent37_3, Fluent19_3>>
/\ UNCHANGED<<Fluent2>>

CommitEntry(i,ind,curTerm) ==
/\ (\E commitQuorum \in Quorums : (curTerm = currentTerm[i] /\ (commitQuorum \in Quorums) /\ ind > 0 /\ state[i] = Primary /\ (\A s \in commitQuorum : currentTerm[s] = curTerm) /\ UNCHANGED <<state,config,currentTerm>>))
/\ Fluent37_3' = [Fluent37_3 EXCEPT ![i] = TRUE]
/\ Fluent16_5' = [Fluent16_5 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent35_3, Fluent36_3, Fluent34_3, Fluent28_2, Fluent29_2, Fluent15_5, Fluent19_3, Fluent31_1, Fluent20_3>>
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ UNCHANGED<<>>

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<config>>
/\ UNCHANGED<<Fluent35_3, Fluent36_3, Fluent34_3, Fluent28_2, Fluent37_3, Fluent16_5, Fluent29_2, Fluent15_5, Fluent19_3, Fluent31_1, Fluent20_3>>
/\ UNCHANGED<<Fluent2>>

Init ==
/\ state = [i \in Server |-> Secondary]
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))
/\ currentTerm = [i \in Server |-> 0]
/\ Fluent35_3 = [ x0 \in Server |-> FALSE]
/\ Fluent36_3 = [ x0 \in Server |-> FALSE]
/\ Fluent34_3 = [ x0 \in Server |-> FALSE]
/\ Fluent28_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent37_3 = [ x0 \in Server |-> FALSE]
/\ Fluent16_5 = [ x0 \in FinNat |-> FALSE]
/\ Fluent29_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent15_5 = [ x0 \in FinNat |-> FALSE]
/\ Fluent19_3 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent31_1 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent20_3 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent2 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s,t \in Server : GetEntries(s,t))
\/ (\E s,t \in Server : RollbackEntries(s,t))
\/ (\E s \in Server : (\E newTerm \in FinNat : BecomeLeader(s,newTerm)))
\/ (\E s \in Server : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,ind,curTerm))))
\/ (\E s,t \in Server : UpdateTerms(s,t))

Spec == (Init /\ [][Next]_vars)
=============================================================================
