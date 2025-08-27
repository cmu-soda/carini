--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS n1, n2, Server, n3, Quorums, NUM2, NUM3, NUM1, _n2n3_, _n1n2n3_, FinNat, _n1n3_, _n1n2_

VARIABLES Fluent6_0, Fluent5_0, committed, err, cexTraceIdx

vars == <<Fluent6_0, Fluent5_0, committed, err, cexTraceIdx>>

NoErr == err = FALSE

CandSep == (\A var0 \in FinNat : (\A var1 \in FinNat : (~(Fluent6_0[var0]) => (Fluent5_0[var1] => var1 <= var0))))

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

StateConstraint == TRUE

Empty(s) == Len(s) = 0

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

IsPrefix(s,t) == (Len(s) <= Len(t) /\ SubSeq(s,1,Len(s)) = SubSeq(t,1,Len(s)))

BecomeLeader(i,newTerm) ==
/\ (\E voteQuorum \in Quorums : ((i \in voteQuorum) /\ UNCHANGED <<committed>>))
/\ Fluent6_0' = [Fluent6_0 EXCEPT![newTerm] = TRUE]
/\ Fluent5_0' = [Fluent5_0 EXCEPT![newTerm] = TRUE]
/\ UNCHANGED <<>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

CommitEntry(i,ind,curTerm) ==
/\ (\E commmitQuorum \in Quorums : ((ind > 0 /\ ~((\E c \in committed : c.entry = <<ind,curTerm>>))) /\ committed' = (committed \cup {[entry |-> <<ind,curTerm>>,term |-> curTerm]})))
/\ UNCHANGED <<Fluent6_0,Fluent5_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

Init ==
/\ committed = {}
/\ Fluent6_0 = [x0 \in FinNat |-> FALSE]
/\ Fluent5_0 = [x0 \in FinNat |-> FALSE]
/\ cexTraceIdx = 0
/\ err = FALSE

Next ==
\/ (\E s \in Server : (\E newTerm \in FinNat : BecomeLeader(s,newTerm)))
\/ (\E s \in Server : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,ind,curTerm))))

Spec == (Init /\ [][Next]_vars)

StateMachineSafety == (\A c1,c2 \in committed : (c1.entry[1] = c2.entry[1] => c1 = c2))

TraceConstraint ==
/\ cexTraceIdx = 0 => BecomeLeader(n1,1) /\ err' = err
/\ cexTraceIdx = 1 => CommitEntry(n1,2,1) /\ err' = err
/\ cexTraceIdx = 2 => BecomeLeader(n1,2) /\ err' = err
/\ cexTraceIdx = 3 => CommitEntry(n1,2,2) /\ err' = TRUE
/\ cexTraceIdx >= 4 => FALSE

InternalAction == UNCHANGED<<cexTraceIdx,err>>

TraceConstraintSpec == Init /\ [][Next /\ (TraceConstraint \/ InternalAction)]_vars
=============================================================================
