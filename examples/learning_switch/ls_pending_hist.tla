--------------------------- MODULE ls_pending_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node

VARIABLES Fluent12, pending

vars == <<Fluent12, pending>>

CandSep ==
\A var0 \in Node : \A var1 \in Node : (Fluent12[var1][var0][var0][var1]) => (var1 = var0)

NewPacket(ps,pd) ==
/\ pending' = (pending \cup {<<ps,pd,ps,ps>>})
/\ UNCHANGED<<Fluent12>>

Forward(ps,pd,sw0,sw1,nondet) ==
/\ (<<ps,pd,sw0,sw1>> \in pending)
/\ pending' = ({ <<psa,pda,sw1a,da>> \in pending : psa = nondet } \cup { <<ps,pd,sw1,d>> : d \in Node })
/\ Fluent12' = [Fluent12 EXCEPT ![ps][sw1][nondet][pd] = TRUE]
/\ UNCHANGED<<>>

Next ==
\/ (\E ps,pd \in Node : NewPacket(ps,pd))
\/ (\E ps,pd,sw0,sw1,nondet \in Node : Forward(ps,pd,sw0,sw1,nondet))

Init ==
/\ pending = {}
/\ Fluent12 = [ x0 \in Node |-> [ x1 \in Node |-> [ x2 \in Node |-> [ x3 \in Node |-> FALSE]]]]

Spec == (Init /\ [][Next]_vars)

NextUnchanged == UNCHANGED <<pending>>

TypeOK ==
/\ (pending \in SUBSET((Node \X Node \X Node \X Node)))
=============================================================================
