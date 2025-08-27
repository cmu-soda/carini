--------------------------- MODULE T2_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent2, Fluent22_2, Fluent13_0, Fluent21_2, Fluent37_1, Fluent35_3, Fluent14_0, currentTerm, Fluent36_1, Fluent34_3, Fluent27_3, Fluent26_3, state, config

vars == <<Fluent2, Fluent22_2, Fluent13_0, Fluent21_2, Fluent37_1, Fluent35_3, Fluent14_0, currentTerm, Fluent36_1, Fluent34_3, Fluent27_3, Fluent26_3, state, config>>

CandSep ==
/\ \A var0 \in FinNat : \A var1 \in FinNat : (~(Fluent22_2[var0])) => ((Fluent21_2[var1]) => (var1 <= var0))
/\ \A var0 \in Server : \A var1 \in FinNat : (Fluent36_1[var1][var0]) => (~(Fluent37_1[var1][var0]))
/\ \A var0 \in Server : (Fluent26_3[var0]) => (Fluent27_3[var0])
/\ \A var0 \in FinNat : (Fluent13_0[var0]) => (Fluent14_0[var0])
/\ \A var0 \in Server : \A var1 \in FinNat : (Fluent34_3[var0][var1]) => (Fluent35_3[var0][var1])

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
/\ Fluent34_3' = [Fluent34_3 EXCEPT ![i][curTerm] = TRUE]
/\ Fluent27_3' = [Fluent27_3 EXCEPT ![i] = FALSE]
/\ UNCHANGED<<Fluent37_1, Fluent35_3, Fluent14_0, Fluent36_1, Fluent26_3, Fluent22_2, Fluent13_0, Fluent21_2>>
/\ UNCHANGED<<Fluent2>>

GetEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ Fluent27_3' = [Fluent27_3 EXCEPT ![i] = TRUE]
/\ Fluent26_3' = [Fluent26_3 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent37_1, Fluent35_3, Fluent14_0, Fluent36_1, Fluent34_3, Fluent22_2, Fluent13_0, Fluent21_2>>
/\ UNCHANGED<<Fluent2>>

RollbackEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED<<Fluent37_1, Fluent35_3, Fluent14_0, Fluent36_1, Fluent34_3, Fluent27_3, Fluent26_3, Fluent22_2, Fluent13_0, Fluent21_2>>
/\ UNCHANGED<<Fluent2>>

BecomeLeader(i,newTerm) ==
/\ (\E voteQuorum \in Quorums : (newTerm = (currentTerm[i] + 1) /\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]] /\ (voteQuorum \in Quorums) /\ (i \in voteQuorum) /\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm)) /\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]] /\ UNCHANGED <<config>>))
/\ Fluent37_1' = [Fluent37_1 EXCEPT ![newTerm][i] = TRUE]
/\ Fluent35_3' = [[Fluent35_3 EXCEPT ![i] = [x0 \in FinNat |-> FALSE]] EXCEPT ![i][newTerm] = TRUE]
/\ Fluent14_0' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ Fluent36_1' = [[Fluent36_1 EXCEPT ![newTerm] = [x0 \in Server |-> TRUE]] EXCEPT ![newTerm][i] = FALSE]
/\ Fluent34_3' = [Fluent34_3 EXCEPT ![i] = [x0 \in FinNat |-> FALSE]]
/\ Fluent26_3' = [Fluent26_3 EXCEPT ![i] = FALSE]
/\ Fluent22_2' = [[x0 \in FinNat |-> TRUE] EXCEPT ![newTerm] = FALSE]
/\ Fluent13_0' = [x0 \in FinNat |-> FALSE]
/\ Fluent21_2' = [Fluent21_2 EXCEPT ![newTerm] = TRUE]
/\ UNCHANGED<<Fluent27_3>>
/\ UNCHANGED<<Fluent2>>

CommitEntry(i,ind,curTerm) ==
/\ (\E commitQuorum \in Quorums : (curTerm = currentTerm[i] /\ (commitQuorum \in Quorums) /\ ind > 0 /\ state[i] = Primary /\ (\A s \in commitQuorum : currentTerm[s] = curTerm) /\ UNCHANGED <<state,config,currentTerm>>))
/\ Fluent13_0' = [Fluent13_0 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent37_1, Fluent35_3, Fluent14_0, Fluent36_1, Fluent34_3, Fluent27_3, Fluent26_3, Fluent22_2, Fluent21_2>>
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ UNCHANGED<<>>

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<config>>
/\ UNCHANGED<<Fluent37_1, Fluent35_3, Fluent14_0, Fluent36_1, Fluent34_3, Fluent27_3, Fluent26_3, Fluent22_2, Fluent13_0, Fluent21_2>>
/\ UNCHANGED<<Fluent2>>

Init ==
/\ state = [i \in Server |-> Secondary]
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))
/\ currentTerm = [i \in Server |-> 0]
/\ Fluent37_1 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent35_3 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent14_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent36_1 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent34_3 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent27_3 = [ x0 \in Server |-> FALSE]
/\ Fluent26_3 = [ x0 \in Server |-> FALSE]
/\ Fluent22_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent13_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent21_2 = [ x0 \in FinNat |-> FALSE]
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
