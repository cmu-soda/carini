--------------------------- MODULE T2_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent28_24, Fluent12_16, Fluent20_2, Fluent21_2, Fluent22_1, Fluent27_1, currentTerm, Fluent23_7, Fluent24_7, Fluent26_8, Fluent25_8, state, Fluent4_0, Fluent3_0, Fluent11_16, Fluent5_5, Fluent9_1, Fluent2, Fluent10_1, Fluent14_1, Fluent15_0, Fluent13_1, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6, Fluent8_4, Fluent6_5, Fluent7_4, config

vars == <<Fluent28_24, Fluent12_16, Fluent20_2, Fluent21_2, Fluent22_1, Fluent27_1, currentTerm, Fluent23_7, Fluent24_7, Fluent26_8, Fluent25_8, state, Fluent4_0, Fluent3_0, Fluent11_16, Fluent5_5, Fluent9_1, Fluent2, Fluent10_1, Fluent14_1, Fluent15_0, Fluent13_1, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6, Fluent8_4, Fluent6_5, Fluent7_4, config>>

CandSep ==
/\ \A var0 \in FinNat : (Fluent3_0[var0]) => (Fluent4_0[var0])
/\ \A var0 \in Server : (Fluent5_5[var0]) => (Fluent6_5[var0])
/\ \A var0 \in FinNat : (Fluent7_4[var0]) => (Fluent8_4[var0])
/\ \A var0 \in Server : (Fluent9_1[var0]) => (Fluent10_1[var0])
/\ \A var0 \in FinNat : (Fluent12_16[var0]) => (Fluent11_16[var0])
/\ \A var0 \in Server : (Fluent14_1[var0]) => (Fluent13_1[var0])
/\ \A var0 \in FinNat : \E var1 \in FinNat : (var0 <= var1) => (~(Fluent15_0[var0]))
/\ \A var0 \in FinNat : \A var1 \in FinNat : (Fluent17_6[var0]) => ((Fluent16_6[var1]) => (var0 <= var1))
/\ \A var0 \in FinNat : \A var1 \in Server : (Fluent18_2[var0][var1]) => (Fluent19_2[var0][var1])
/\ \A var0 \in FinNat : (Fluent20_2[var0]) => (Fluent21_2[var0])
/\ \A var0 \in Server : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent22_1[var0][var2]) => (var1 = var2)
/\ \A var0 \in FinNat : (Fluent24_7[var0]) => (~(Fluent23_7[var0]))
/\ \A var0 \in Server : (Fluent26_8[var0]) => (Fluent25_8[var0])
/\ \A var0 \in Server : \E var1 \in FinNat : \A var2 \in FinNat : (Fluent27_1[var0][var2]) => (var1 = var2)
/\ \A var0 \in FinNat : \E var1 \in Quorums : \A var2 \in Quorums : (Fluent28_24[var0][var2]) => (var2 = var1)

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
/\ Fluent22_1' = [Fluent22_1 EXCEPT ![i][curTerm] = TRUE]
/\ Fluent27_1' = [Fluent27_1 EXCEPT ![i][curTerm] = TRUE]
/\ Fluent23_7' = [x0 \in FinNat |-> FALSE]
/\ Fluent24_7' = [Fluent24_7 EXCEPT ![curTerm] = TRUE]
/\ Fluent26_8' = [Fluent26_8 EXCEPT ![i] = TRUE]
/\ Fluent3_0' = [Fluent3_0 EXCEPT ![curTerm] = TRUE]
/\ Fluent5_5' = [Fluent5_5 EXCEPT ![i] = TRUE]
/\ Fluent18_2' = [Fluent18_2 EXCEPT ![curTerm][i] = TRUE]
/\ UNCHANGED<<Fluent28_24, Fluent12_16, Fluent20_2, Fluent21_2, Fluent25_8, Fluent4_0, Fluent11_16, Fluent9_1, Fluent10_1, Fluent14_1, Fluent15_0, Fluent13_1, Fluent19_2, Fluent17_6, Fluent16_6, Fluent8_4, Fluent6_5, Fluent7_4>>
/\ UNCHANGED<<Fluent2>>

GetEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ Fluent26_8' = [x0 \in Server |-> FALSE]
/\ Fluent25_8' = [Fluent25_8 EXCEPT ![i] = FALSE]
/\ UNCHANGED<<Fluent28_24, Fluent12_16, Fluent20_2, Fluent21_2, Fluent22_1, Fluent27_1, Fluent23_7, Fluent24_7, Fluent4_0, Fluent3_0, Fluent11_16, Fluent5_5, Fluent9_1, Fluent10_1, Fluent14_1, Fluent15_0, Fluent13_1, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6, Fluent8_4, Fluent6_5, Fluent7_4>>
/\ UNCHANGED<<Fluent2>>

RollbackEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED<<Fluent28_24, Fluent12_16, Fluent20_2, Fluent21_2, Fluent22_1, Fluent27_1, Fluent23_7, Fluent24_7, Fluent26_8, Fluent25_8, Fluent4_0, Fluent3_0, Fluent11_16, Fluent5_5, Fluent9_1, Fluent10_1, Fluent14_1, Fluent15_0, Fluent13_1, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6, Fluent8_4, Fluent6_5, Fluent7_4>>
/\ UNCHANGED<<Fluent2>>

BecomeLeader(i,voteQuorum,newTerm) ==
/\ newTerm = (currentTerm[i] + 1)
/\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]]
/\ (voteQuorum \in Quorums)
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]]
/\ UNCHANGED <<config>>
/\ Fluent28_24' = [Fluent28_24 EXCEPT ![newTerm][voteQuorum] = TRUE]
/\ Fluent20_2' = [x0 \in FinNat |-> FALSE]
/\ Fluent21_2' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ Fluent22_1' = [x0 \in Server |-> [x1 \in FinNat |-> FALSE]]
/\ Fluent27_1' = [Fluent27_1 EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ Fluent23_7' = [Fluent23_7 EXCEPT ![newTerm] = TRUE]
/\ Fluent25_8' = [Fluent25_8 EXCEPT ![i] = TRUE]
/\ Fluent4_0' = [Fluent4_0 EXCEPT ![newTerm] = TRUE]
/\ Fluent10_1' = [Fluent10_1 EXCEPT ![i] = TRUE]
/\ Fluent14_1' = [x0 \in Server |-> FALSE]
/\ Fluent15_0' = [Fluent15_0 EXCEPT ![newTerm] = TRUE]
/\ Fluent13_1' = [[x0 \in Server |-> FALSE] EXCEPT ![i] = TRUE]
/\ Fluent19_2' = [Fluent19_2 EXCEPT ![newTerm][i] = TRUE]
/\ Fluent17_6' = [Fluent17_6 EXCEPT ![newTerm] = TRUE]
/\ Fluent16_6' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ Fluent8_4' = [Fluent8_4 EXCEPT ![newTerm] = TRUE]
/\ Fluent6_5' = [Fluent6_5 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent12_16, Fluent24_7, Fluent26_8, Fluent3_0, Fluent11_16, Fluent5_5, Fluent9_1, Fluent18_2, Fluent7_4>>
/\ UNCHANGED<<Fluent2>>

CommitEntry(i,commitQuorum,ind,curTerm,minQTerm) ==
/\ minQTerm = MinTerm(commitQuorum)
/\ curTerm = currentTerm[i]
/\ (commitQuorum \in Quorums)
/\ ind > 0
/\ state[i] = Primary
/\ (\A s \in commitQuorum : currentTerm[s] = curTerm)
/\ UNCHANGED <<state,config,currentTerm>>
/\ Fluent12_16' = [Fluent12_16 EXCEPT ![curTerm] = TRUE]
/\ Fluent20_2' = [Fluent20_2 EXCEPT ![curTerm] = TRUE]
/\ Fluent11_16' = [Fluent11_16 EXCEPT ![minQTerm] = TRUE]
/\ Fluent9_1' = [Fluent9_1 EXCEPT ![i] = TRUE]
/\ Fluent14_1' = [Fluent14_1 EXCEPT ![i] = TRUE]
/\ Fluent7_4' = [Fluent7_4 EXCEPT ![minQTerm] = TRUE]
/\ UNCHANGED<<Fluent28_24, Fluent21_2, Fluent22_1, Fluent27_1, Fluent23_7, Fluent24_7, Fluent26_8, Fluent25_8, Fluent4_0, Fluent3_0, Fluent5_5, Fluent10_1, Fluent15_0, Fluent13_1, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6, Fluent8_4, Fluent6_5>>
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ UNCHANGED<<>>

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<config>>
/\ UNCHANGED<<Fluent28_24, Fluent12_16, Fluent20_2, Fluent21_2, Fluent22_1, Fluent27_1, Fluent23_7, Fluent24_7, Fluent26_8, Fluent25_8, Fluent4_0, Fluent3_0, Fluent11_16, Fluent5_5, Fluent9_1, Fluent10_1, Fluent14_1, Fluent15_0, Fluent13_1, Fluent19_2, Fluent18_2, Fluent17_6, Fluent16_6, Fluent8_4, Fluent6_5, Fluent7_4>>
/\ UNCHANGED<<Fluent2>>

Init ==
/\ state = [i \in Server |-> Secondary]
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))
/\ currentTerm = [i \in Server |-> 0]
/\ Fluent28_24 = [ x0 \in FinNat |-> [ x1 \in Quorums |-> FALSE]]
/\ Fluent12_16 = [ x0 \in FinNat |-> FALSE]
/\ Fluent20_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent21_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent22_1 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent27_1 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent23_7 = [ x0 \in FinNat |-> FALSE]
/\ Fluent24_7 = [ x0 \in FinNat |-> FALSE]
/\ Fluent26_8 = [ x0 \in Server |-> FALSE]
/\ Fluent25_8 = [ x0 \in Server |-> FALSE]
/\ Fluent4_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent3_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent11_16 = [ x0 \in FinNat |-> FALSE]
/\ Fluent5_5 = [ x0 \in Server |-> FALSE]
/\ Fluent9_1 = [ x0 \in Server |-> FALSE]
/\ Fluent10_1 = [ x0 \in Server |-> FALSE]
/\ Fluent14_1 = [ x0 \in Server |-> FALSE]
/\ Fluent15_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent13_1 = [ x0 \in Server |-> FALSE]
/\ Fluent19_2 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent18_2 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent17_6 = [ x0 \in FinNat |-> FALSE]
/\ Fluent16_6 = [ x0 \in FinNat |-> FALSE]
/\ Fluent8_4 = [ x0 \in FinNat |-> FALSE]
/\ Fluent6_5 = [ x0 \in Server |-> FALSE]
/\ Fluent7_4 = [ x0 \in FinNat |-> FALSE]
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
