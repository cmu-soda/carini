--------------------------- MODULE C1_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent1_5, Fluent0_5, committed, Fluent2_7, Fluent4_4, Fluent3_4, Fluent5_14, Fluent8_4, Fluent7_4, Fluent9_2, Fluent6_14, Fluent10_2

vars == <<Fluent1_5, Fluent0_5, committed, Fluent2_7, Fluent4_4, Fluent3_4, Fluent5_14, Fluent8_4, Fluent7_4, Fluent9_2, Fluent6_14, Fluent10_2>>

CandSep ==
/\ \A var0 \in Server : (Fluent1_5[var0]) => (Fluent0_5[var0])
/\ \A var0 \in FinNat : \E var1 \in FinNat : (var0 <= var1) => (~(Fluent2_7[var0]))
/\ \A var0 \in FinNat : (Fluent4_4[var0]) => (Fluent3_4[var0])
/\ \A var0 \in FinNat : (Fluent6_14[var0]) => (Fluent5_14[var0])
/\ \A var0 \in FinNat : \A var1 \in Server : (Fluent7_4[var0][var1]) => (Fluent8_4[var0][var1])
/\ \A var0 \in FinNat : (Fluent9_2[var0]) => (Fluent10_2[var0])

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

StateConstraint == TRUE

Empty(s) == Len(s) = 0

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

IsPrefix(s,t) == (Len(s) <= Len(t) /\ SubSeq(s,1,Len(s)) = SubSeq(t,1,Len(s)))

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ UNCHANGED <<committed>>
/\ Fluent0_5' = [Fluent0_5 EXCEPT ![i] = TRUE]
/\ Fluent2_7' = [Fluent2_7 EXCEPT ![newTerm] = TRUE]
/\ Fluent5_14' = [Fluent5_14 EXCEPT ![newTerm] = TRUE]
/\ Fluent8_4' = [Fluent8_4 EXCEPT ![newTerm][i] = TRUE]
/\ Fluent9_2' = [x0 \in FinNat |-> FALSE]
/\ Fluent10_2' = [[x0 \in FinNat |-> FALSE] EXCEPT ![newTerm] = TRUE]
/\ UNCHANGED<<Fluent1_5, Fluent4_4, Fluent3_4, Fluent7_4, Fluent6_14>>
/\ CandSep'

CommitEntry(i,commitQuorum,ind,curTerm,minQTerm) ==
/\ ind > 0
/\ ~((\E c \in committed : c.entry = <<ind,curTerm>>))
/\ committed' = (committed \cup {[entry |-> <<ind,curTerm>>,term |-> curTerm]})
/\ Fluent1_5' = [Fluent1_5 EXCEPT ![i] = TRUE]
/\ Fluent4_4' = [Fluent4_4 EXCEPT ![curTerm] = TRUE]
/\ Fluent3_4' = [Fluent3_4 EXCEPT ![minQTerm] = TRUE]
/\ Fluent7_4' = [Fluent7_4 EXCEPT ![curTerm][i] = TRUE]
/\ Fluent9_2' = [Fluent9_2 EXCEPT ![minQTerm] = TRUE]
/\ Fluent6_14' = [Fluent6_14 EXCEPT ![curTerm] = TRUE]
/\ UNCHANGED<<Fluent0_5, Fluent2_7, Fluent5_14, Fluent8_4, Fluent10_2>>
/\ CandSep'

Init ==
/\ committed = {}
/\ Fluent1_5 = [ x0 \in Server |-> FALSE]
/\ Fluent0_5 = [ x0 \in Server |-> FALSE]
/\ Fluent2_7 = [ x0 \in FinNat |-> FALSE]
/\ Fluent4_4 = [ x0 \in FinNat |-> FALSE]
/\ Fluent3_4 = [ x0 \in FinNat |-> FALSE]
/\ Fluent5_14 = [ x0 \in FinNat |-> FALSE]
/\ Fluent8_4 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent7_4 = [ x0 \in FinNat |-> [ x1 \in Server |-> FALSE]]
/\ Fluent9_2 = [ x0 \in FinNat |-> FALSE]
/\ Fluent6_14 = [ x0 \in FinNat |-> FALSE]
/\ Fluent10_2 = [ x0 \in FinNat |-> FALSE]

Next ==
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : (\E minQTerm \in FinNat : CommitEntry(s,Q,ind,curTerm,minQTerm))))))

Spec == (Init /\ [][Next]_vars)

StateMachineSafety == (\A c1,c2 \in committed : (c1.entry[1] = c2.entry[1] => c1 = c2))
=============================================================================
