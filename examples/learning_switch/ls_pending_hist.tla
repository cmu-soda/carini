--------------------------- MODULE ls_pending_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node

VARIABLES Fluent14, pending, Fluent16, Fluent15

vars == <<Fluent14, pending, Fluent16, Fluent15>>

CandSep ==
\A var0 \in Node : \E var1 \in Node : ((~(Fluent14[var0][var1])) => (Fluent15[var1][var1][var1][var0])) => (Fluent16[var1][var1][var1][var1])

NewPacket(ps,pd) ==
/\ pending' = (pending \cup {<<ps,pd,ps,ps>>})
/\ UNCHANGED<<Fluent14, Fluent16, Fluent15>>

Forward(ps,pd,sw0,sw1,nondet) ==
/\ (<<ps,pd,sw0,sw1>> \in pending)
/\ pending' = ({ <<psa,pda,sw1a,da>> \in pending : psa = nondet } \cup { <<ps,pd,sw1,d>> : d \in Node })
/\ Fluent14' = [Fluent14 EXCEPT ![sw1][nondet] = TRUE]
/\ Fluent16' = [Fluent16 EXCEPT ![pd][ps][nondet][sw0] = TRUE]
/\ Fluent15' = [Fluent15 EXCEPT ![pd][ps][nondet][sw0] = TRUE]
/\ UNCHANGED<<>>

Next ==
\/ (\E ps,pd \in Node : NewPacket(ps,pd))
\/ (\E ps,pd,sw0,sw1,nondet \in Node : Forward(ps,pd,sw0,sw1,nondet))

Init ==
/\ pending = {}
/\ Fluent14 = [ x0 \in Node |-> [ x1 \in Node |-> FALSE]]
/\ Fluent16 = [ x0 \in Node |-> [ x1 \in Node |-> [ x2 \in Node |-> [ x3 \in Node |-> FALSE]]]]
/\ Fluent15 = [ x0 \in Node |-> [ x1 \in Node |-> [ x2 \in Node |-> [ x3 \in Node |-> FALSE]]]]

Spec == (Init /\ [][Next]_vars)

NextUnchanged == UNCHANGED <<pending>>

TypeOK ==
/\ (pending \in SUBSET((Node \X Node \X Node \X Node)))
=============================================================================
