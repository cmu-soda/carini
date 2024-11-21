--------------------------- MODULE ls_pending ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node

VARIABLES pending, Fluent2, Fluent1, Fluent0

vars == <<pending, Fluent2, Fluent1, Fluent0>>

Safety ==
/\ \A var0 \in Node : ~(Fluent0[var0][var0])
/\ \A var0 \in Node : ~(Fluent1[var0][var0])
/\ \A var0 \in Node : \A var1 \in Node : (Fluent2[var0][var1]) => (var0 = var1)

NewPacket(ps,pd) ==
/\ pending' = (pending \cup {<<ps,pd,ps,ps>>})
/\ UNCHANGED<<Fluent2,Fluent1,Fluent0>>

Forward(ps,pd,sw0,sw1,nondet) ==
/\ (<<ps,pd,sw0,sw1>> \in pending)
/\ pending' = ({ <<psa,pda,sw1a,da>> \in pending : psa = nondet } \cup { <<ps,pd,sw1,d>> : d \in Node })
/\ Fluent2' = [Fluent2 EXCEPT ![sw0][ps] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT ![sw1][nondet] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![pd][nondet] = TRUE]
/\ UNCHANGED<<>>

Next ==
\/ (\E ps,pd \in Node : NewPacket(ps,pd))
\/ (\E ps,pd,sw0,sw1,nondet \in Node : Forward(ps,pd,sw0,sw1,nondet))

Init ==
/\ pending = {}
/\ Fluent2 = [ x0 \in Node |-> [ x1 \in Node |-> FALSE]]
/\ Fluent1 = [ x0 \in Node |-> [ x1 \in Node |-> FALSE]]
/\ Fluent0 = [ x0 \in Node |-> [ x1 \in Node |-> FALSE]]

NextUnchanged == UNCHANGED <<pending>>

TypeOK ==
/\ (pending \in SUBSET((Node \X Node \X Node \X Node)))
=============================================================================
