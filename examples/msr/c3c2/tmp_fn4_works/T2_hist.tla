--------------------------- MODULE T2_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent32_15, Fluent40_2, Fluent2, Fluent33_15, currentTerm, Fluent17_11, Fluent18_11, Fluent39_2, Fluent25_13, Fluent8_4, state, Fluent7_4, config, Fluent26_13, Fluent27_16, Fluent28_16

vars == <<Fluent32_15, Fluent40_2, Fluent2, Fluent33_15, currentTerm, Fluent17_11, Fluent18_11, Fluent39_2, Fluent25_13, Fluent8_4, state, Fluent7_4, config, Fluent26_13, Fluent27_16, Fluent28_16>>

CandSep ==
/\ \A var0 \in FinNat : (Fluent39_2[var0]) => (~(Fluent40_2[var0]))
/\ \A var0 \in FinNat : \A var1 \in Server : (Fluent28_16[var0][var1]) => (Fluent27_16[var0][var1])
/\ \A var0 \in FinNat : \A var1 \in FinNat : (~(Fluent25_13[var0])) => ((Fluent26_13[var1]) => (var1 <= var0))
/\ \A var0 \in Server : (Fluent17_11[var0]) => (Fluent18_11[var0])
/\ \A var0 \in FinNat : (Fluent32_15[var0]) => (Fluent33_15[var0])
/\ \A var0 \in FinNat : (Fluent7_4[var0]) => (Fluent8_4[var0])

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
/\ Fluent32_15' = [Fluent32_15 EXCEPT ![curTerm] = TRUE]
/\ Fluent28_16' = [Fluent28_16 EXCEPT ![curTerm][i] = TRUE]
/\ Fluent33_15' = [x0 \in FinNat |-> TRUE]
/\ UNCHANGED<<Fluent17_11, Fluent18_11, Fluent39_2, Fluent40_2, Fluent25_13, Fluent8_4, Fluent7_4, Fluent26_13, Fluent27_16>>
/\ UNCHANGED<<Fluent2>>

GetEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED<<Fluent32_15, Fluent17_11, Fluent18_11, Fluent39_2, Fluent40_2, Fluent25_13, Fluent8_4, Fluent7_4, Fluent26_13, Fluent27_16, Fluent28_16, Fluent33_15>>
/\ UNCHANGED<<Fluent2>>

RollbackEntries(i,j) ==
/\ state[i] = Secondary
/\ UNCHANGED <<state,config,currentTerm>>
/\ UNCHANGED<<Fluent32_15, Fluent17_11, Fluent18_11, Fluent39_2, Fluent40_2, Fluent25_13, Fluent8_4, Fluent7_4, Fluent26_13, Fluent27_16, Fluent28_16, Fluent33_15>>
/\ UNCHANGED<<Fluent2>>

BecomeLeader(i,voteQuorum,newTerm) ==
/\ newTerm = (currentTerm[i] + 1)
/\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]]
/\ (voteQuorum \in Quorums)
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForOplog(v,i,newTerm))
/\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]]
/\ UNCHANGED <<config>>
/\ Fluent17_11' = [[x0 \in Server |-> FALSE] EXCEPT ![i] = TRUE]
/\ Fluent18_11' = [[x0 \in Server |-> FALSE] EXCEPT ![i] = TRUE]
/\ Fluent39_2' = [[x0 \in FinNat |-> TRUE] EXCEPT ![newTerm] = FALSE]
/\ Fluent40_2' = [x0 \in FinNat |-> FALSE]
/\ Fluent25_13' = [[x0 \in FinNat |-> TRUE] EXCEPT ![newTerm] = FALSE]
/\ Fluent8_4' = [Fluent8_4 EXCEPT ![newTerm] = TRUE]
/\ Fluent26_13' = [Fluent26_13 EXCEPT ![newTerm] = TRUE]
/\ Fluent27_16' = [Fluent27_16 EXCEPT ![newTerm][i] = TRUE]
/\ Fluent33_15' = [Fluent33_15 EXCEPT ![newTerm] = FALSE]
/\ UNCHANGED<<Fluent32_15, Fluent7_4, Fluent28_16>>
/\ UNCHANGED<<Fluent2>>

CommitEntry(i,commitQuorum,ind,curTerm,minQTerm) ==
/\ minQTerm = MinTerm(commitQuorum)
/\ curTerm = currentTerm[i]
/\ (commitQuorum \in Quorums)
/\ ind > 0
/\ state[i] = Primary
/\ (\A s \in commitQuorum : currentTerm[s] = curTerm)
/\ UNCHANGED <<state,config,currentTerm>>
/\ Fluent17_11' = [Fluent17_11 EXCEPT ![i] = TRUE]
/\ Fluent40_2' = [Fluent40_2 EXCEPT ![curTerm] = TRUE]
/\ Fluent7_4' = [Fluent7_4 EXCEPT ![minQTerm] = TRUE]
/\ UNCHANGED<<Fluent32_15, Fluent18_11, Fluent39_2, Fluent25_13, Fluent8_4, Fluent26_13, Fluent27_16, Fluent28_16, Fluent33_15>>
/\ Fluent2' = [Fluent2 EXCEPT ![ind][curTerm] = TRUE]
/\ UNCHANGED<<>>

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED <<config>>
/\ UNCHANGED<<Fluent32_15, Fluent17_11, Fluent18_11, Fluent39_2, Fluent40_2, Fluent25_13, Fluent8_4, Fluent7_4, Fluent26_13, Fluent27_16, Fluent28_16, Fluent33_15>>
/\ UNCHANGED<<Fluent2>>

Init ==
/\ state = [i \in Server |-> Secondary]
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))
/\ currentTerm = [i \in Server |-> 0]
/\ Fluent32_15 = [ x0 \in FinNat |-> FALSE]
/\ Fluent17_11 = [ x0 \in Server |-> FALSE]
/\ Fluent18_11 = [ x0 \in Server |-> FALSE]
/\ Fluent39_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent40_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent25_13 = [ x0 \in FinNat |-> FALSE]
/\ Fluent8_4 = [ x0 \in FinNat |-> FALSE]
/\ Fluent7_4 = [ x0 \in FinNat |-> FALSE]
/\ Fluent26_13 = [ x0 \in FinNat |-> FALSE]
/\ Fluent27_16 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent28_16 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent33_15 = [ x0 \in FinNat |-> FALSE]
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
