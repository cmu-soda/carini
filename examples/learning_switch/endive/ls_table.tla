--------------------------- MODULE ls_table ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node

VARIABLES Fluent2, Fluent1, Fluent0, table

vars == <<Fluent2, Fluent1, Fluent0, table>>

CandSep ==
/\ \A var0 \in Node : ~(Fluent0[var0][var0])
/\ \A var0 \in Node : ~(Fluent1[var0][var0])
/\ \A var0 \in Node : \A var1 \in Node : (Fluent2[var0][var1]) => (var0 = var1)

Forward(ps,pd,sw0,sw1,nondet) ==
/\ table' = IF (ps /= sw1 /\ (\A w \in Node : (w /= sw1 => (<<ps,sw1,w>> \notin table)))) THEN (table \cup { <<px,n1,n2>> \in (Node \X Node \X Node) : (px = ps /\ ((<<ps,n1,sw1>> \in table) /\ (<<ps,sw0,n2>> \in table))) }) ELSE table
/\ Fluent2' = [Fluent2 EXCEPT ![sw0][ps] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT ![sw1][nondet] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![pd][nondet] = TRUE]
/\ UNCHANGED<<>>
/\ CandSep'

Next ==
\/ (\E ps,pd,sw0,sw1,nondet \in Node : Forward(ps,pd,sw0,sw1,nondet))

Init ==
/\ table = { <<t,n1,n2>> \in (Node \X Node \X Node) : n1 = n2 }
/\ Fluent2 = [ x0 \in Node |-> [ x1 \in Node |-> FALSE]]
/\ Fluent1 = [ x0 \in Node |-> [ x1 \in Node |-> FALSE]]
/\ Fluent0 = [ x0 \in Node |-> [ x1 \in Node |-> FALSE]]

NextUnchanged == UNCHANGED <<table>>

TypeOK ==
/\ (table \in SUBSET((Node \X Node \X Node)))

Safety ==
/\ (\A t,x \in Node : (<<t,x,x>> \in table))
/\ (\A t,x,y,z \in Node : (((<<t,x,y>> \in table) /\ (<<t,y,z>> \in table)) => (<<t,x,z>> \in table)))
/\ (\A t,x,y \in Node : (((<<t,x,y>> \in table) /\ (<<t,y,x>> \in table)) => x = y))
/\ (\A t,x,y,z \in Node : (((<<t,x,y>> \in table) /\ (<<t,x,z>> \in table)) => ((<<t,y,z>> \in table) \/ (<<t,z,y>> \in table))))
=============================================================================
