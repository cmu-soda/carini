--------------------------- MODULE StateTermConfig_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent40_1, Fluent45_0, Fluent42_3, Fluent46_0, Fluent52_4, Fluent51_4, Fluent41_3, Fluent21_2, Fluent33_5, Fluent55_6, currentTerm, Fluent32_5, Fluent39_1, Fluent56_6, state, config

vars == <<Fluent40_1, Fluent45_0, Fluent42_3, Fluent46_0, Fluent52_4, Fluent51_4, Fluent41_3, Fluent21_2, Fluent33_5, Fluent55_6, currentTerm, Fluent32_5, Fluent39_1, Fluent56_6, state, config>>

CandSep ==
/\ \A var0 \in Server : \A var1 \in FinNat : (Fluent39_1[var1][var0]) => (~(Fluent40_1[var1][var0]))
/\ \A var0 \in FinNat : (Fluent33_5[var0]) => (Fluent32_5[var0])
/\ \A var0 \in FinNat : \A var1 \in FinNat : (Fluent45_0[var0]) => ((Fluent46_0[var1]) => (var0 <= var1))
/\ \A var0 \in Server : (Fluent55_6[var0]) => (Fluent56_6[var0])
/\ \A var0 \in Server : \A var1 \in FinNat : (Fluent52_4[var0][var1]) => (Fluent51_4[var0][var1])
/\ \A var0 \in FinNat : \A var1 \in Server : (Fluent41_3[var0][var1]) => (Fluent42_3[var0][var1])

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
/\ Fluent56_6' = [Fluent56_6 EXCEPT ![i] = FALSE]
/\ Fluent51_4' = [Fluent51_4 EXCEPT ![i][curTerm] = FALSE]
/\ Fluent41_3' = [Fluent41_3 EXCEPT ![curTerm][i] = TRUE]
/\ UNCHANGED<<Fluent33_5, Fluent55_6, Fluent32_5, Fluent39_1, Fluent40_1, Fluent45_0, Fluent42_3, Fluent46_0, Fluent52_4>>
/\ UNCHANGED<<Fluent21_2>>

GetEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ Fluent55_6' = [Fluent55_6 EXCEPT ![i] = TRUE]
/\ Fluent56_6' = [Fluent56_6 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent33_5, Fluent32_5, Fluent39_1, Fluent40_1, Fluent45_0, Fluent42_3, Fluent46_0, Fluent52_4, Fluent51_4, Fluent41_3>>
/\ UNCHANGED<<Fluent21_2>>

RollbackEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED<<Fluent33_5, Fluent55_6, Fluent32_5, Fluent39_1, Fluent56_6, Fluent40_1, Fluent45_0, Fluent42_3, Fluent46_0, Fluent52_4, Fluent51_4, Fluent41_3>>
/\ UNCHANGED<<Fluent21_2>>

BecomeLeader(i,newTerm) ==
/\ (\E voteQuorum \in Quorums : (newTerm = (currentTerm[i] + 1) /\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]] /\ (voteQuorum \in Quorums) /\ (i \in voteQuorum) /\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm)) /\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]] /\ UNCHANGED <<config>>))
/\ Fluent33_5' = [x0 \in FinNat |-> FALSE]
/\ Fluent55_6' = [Fluent55_6 EXCEPT ![i] = FALSE]
/\ Fluent32_5' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ Fluent39_1' = [Fluent39_1 EXCEPT ![newTerm][i] = TRUE]
/\ Fluent40_1' = [[Fluent40_1 EXCEPT ![newTerm] = [x0 \in Server |-> TRUE]] EXCEPT ![newTerm][i] = FALSE]
/\ Fluent45_0' = [Fluent45_0 EXCEPT ![newTerm] = TRUE]
/\ Fluent42_3' = [Fluent42_3 EXCEPT ![newTerm][i] = TRUE]
/\ Fluent46_0' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ Fluent52_4' = [[Fluent52_4 EXCEPT ![i] = [x0 \in FinNat |-> TRUE]] EXCEPT ![i][newTerm] = FALSE]
/\ Fluent51_4' = [Fluent51_4 EXCEPT ![i] = [x0 \in FinNat |-> TRUE]]
/\ UNCHANGED<<Fluent56_6, Fluent41_3>>
/\ UNCHANGED<<Fluent21_2>>

CommitEntry(i,ind,curTerm) ==
/\ (\E commitQuorum \in Quorums : (curTerm = currentTerm[i] /\ (commitQuorum \in Quorums) /\ ind > 0 /\ state[i] = Primary /\ (\A s \in commitQuorum : currentTerm[s] = curTerm) /\ UNCHANGED <<state,config,currentTerm>>))
/\ Fluent33_5' = [Fluent33_5 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent55_6, Fluent32_5, Fluent39_1, Fluent56_6, Fluent40_1, Fluent45_0, Fluent42_3, Fluent46_0, Fluent52_4, Fluent51_4, Fluent41_3>>
/\ Fluent21_2' = [Fluent21_2 EXCEPT ![curTerm][ind] = TRUE]
/\ UNCHANGED<<>>

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<config>>
/\ UNCHANGED<<Fluent33_5, Fluent55_6, Fluent32_5, Fluent39_1, Fluent56_6, Fluent40_1, Fluent45_0, Fluent42_3, Fluent46_0, Fluent52_4, Fluent51_4, Fluent41_3>>
/\ UNCHANGED<<Fluent21_2>>

Init ==
/\ state = [i \in Server |-> Secondary]
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))
/\ currentTerm = [i \in Server |-> 0]
/\ Fluent33_5 = [ x0 \in FinNat |-> FALSE]
/\ Fluent55_6 = [ x0 \in Server |-> FALSE]
/\ Fluent32_5 = [ x0 \in FinNat |-> FALSE]
/\ Fluent39_1 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent56_6 = [ x0 \in Server |-> FALSE]
/\ Fluent40_1 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent45_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent42_3 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent46_0 = [ x0 \in FinNat |-> FALSE]
/\ Fluent52_4 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent51_4 = [ x0 \in Server |-> [ x1 \in FinNat |-> FALSE]]
/\ Fluent41_3 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent21_2 = [ x0 \in FinNat |-> [ x1 \in FinNat |-> FALSE]]

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s,t \in Server : GetEntries(s,t))
\/ (\E s,t \in Server : RollbackEntries(s,t))
\/ (\E s \in Server : (\E newTerm \in FinNat : BecomeLeader(s,newTerm)))
\/ (\E s \in Server : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,ind,curTerm))))
\/ (\E s,t \in Server : UpdateTerms(s,t))

Spec == (Init /\ [][Next]_vars)
=============================================================================
