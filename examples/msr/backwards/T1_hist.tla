--------------------------- MODULE T1_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server, Quorums, FinNat

VARIABLES Fluent1, Fluent0, state

vars == <<Fluent1, Fluent0, state>>

CandSep ==
/\ \A var0 \in Server : (Fluent0[var0]) => (Fluent1[var0])

Secondary == "secondary"

Primary == "primary"

Nil == "nil"

StateConstraint == TRUE

UpdateTermsExpr(i,j) ==
/\ state' = [state EXCEPT![j] = Secondary]

ClientRequest(i,curTerm) ==
/\ UNCHANGED <<state>>
/\ UNCHANGED<<Fluent1, Fluent0>>

GetEntries(i,j) ==
/\ UNCHANGED <<state>>
/\ UNCHANGED<<Fluent1, Fluent0>>

RollbackEntries(i,j) ==
/\ UNCHANGED <<state>>
/\ UNCHANGED<<Fluent1, Fluent0>>

BecomeLeader(i,voteQuorum,newTerm) ==
/\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]]
/\ Fluent1' = [Fluent1 EXCEPT ![i] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![i] = FALSE]

CommitEntry(i,commitQuorum,ind,curTerm) ==
/\ state[i] = Primary
/\ UNCHANGED <<state>>
/\ Fluent0' = [Fluent0 EXCEPT ![i] = TRUE]
/\ UNCHANGED<<Fluent1>>

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)
/\ UNCHANGED<<Fluent1, Fluent0>>

Init ==
/\ state = [i \in Server |-> Secondary]
/\ Fluent1 = [ x0 \in Server |-> FALSE]
/\ Fluent0 = [ x0 \in Server |-> FALSE]

Next ==
\/ (\E s \in Server : (\E t \in FinNat : ClientRequest(s,t)))
\/ (\E s,t \in Server : GetEntries(s,t))
\/ (\E s,t \in Server : RollbackEntries(s,t))
\/ (\E s \in Server : (\E Q \in Quorums : (\E newTerm \in FinNat : BecomeLeader(s,Q,newTerm))))
\/ (\E s \in Server : (\E Q \in Quorums : (\E ind \in FinNat : (\E curTerm \in FinNat : CommitEntry(s,Q,ind,curTerm)))))
\/ (\E s,t \in Server : UpdateTerms(s,t))

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ state \in [Server -> {Primary,Secondary}]
/\ Fluent1 \in [Server -> BOOLEAN]
/\ Fluent0 \in [Server -> BOOLEAN]

IISpec == TypeOK /\ CandSep /\ [][Next]_vars

=============================================================================
