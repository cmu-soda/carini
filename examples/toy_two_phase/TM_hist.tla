--------------------------- MODULE TM_hist ---------------------------
EXTENDS Naturals, Sequences, Integers, FiniteSets, TLC

CONSTANTS RMs

VARIABLES Fluent6_0, Fluent5_0, tmState, tmPrepared, Fluent13_0, Fluent12_0

vars == <<Fluent6_0, Fluent5_0, tmState, tmPrepared, Fluent13_0, Fluent12_0>>

CandSep ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent12_0[var0]) => (~(Fluent13_0[var1]))
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent6_0[var1]) => (Fluent5_0[var0])

Symmetry == Permutations(RMs)

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent5_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent13_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent12_0 = [ x0 \in RMs |-> FALSE]

Prepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<tmState>>
/\ Fluent5_0' = [Fluent5_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent13_0, Fluent12_0>>

Commit(rm) ==
/\ (tmState \in {"init","commmitted"})
/\ tmPrepared = RMs
/\ tmState' = "commit"
/\ UNCHANGED <<tmPrepared>>
/\ Fluent6_0' = [Fluent6_0 EXCEPT ![rm] = TRUE]
/\ Fluent13_0' = [Fluent13_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent5_0, Fluent12_0>>

Abort(rm) ==
/\ (tmState \in {"init","abort"})
/\ tmState' = "abort"
/\ UNCHANGED <<tmPrepared>>
/\ Fluent12_0' = [Fluent12_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent13_0>>

Next ==
\E rm \in RMs :
\/ Prepare(rm)
\/ Commit(rm)
\/ Abort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (tmState \in {"init","commit","abort"})
/\ (tmPrepared \in SUBSET(RMs))
=============================================================================
