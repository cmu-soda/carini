--------------------------- MODULE ls_table_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node

VARIABLES Fluent6_0, Fluent7_0, table

vars == <<Fluent6_0, Fluent7_0, table>>

CandSep ==
\A var0 \in Node : (Fluent6_0[var0]) => (Fluent7_0[var0])

Forward(ps,pd,sw0,sw1,nondet) ==
/\ table' = IF (ps /= sw1 /\ (\A w \in Node : (w /= sw1 => (<<ps,sw1,w>> \notin table)))) THEN (table \cup { <<px,n1,n2>> \in (Node \X Node \X Node) : (px = ps /\ ((<<ps,n1,sw1>> \in table) /\ (<<ps,sw0,n2>> \in table))) }) ELSE table
/\ Fluent6_0' = [Fluent6_0 EXCEPT ![ps] = TRUE]
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![sw0] = TRUE]
/\ UNCHANGED<<>>
/\ CandSep'

Next ==
\/ (\E ps,pd,sw0,sw1,nondet \in Node : Forward(ps,pd,sw0,sw1,nondet))

Init ==
/\ table = { <<t,n1,n2>> \in (Node \X Node \X Node) : n1 = n2 }
/\ Fluent6_0 = [ x0 \in Node |-> FALSE]
/\ Fluent7_0 = [ x0 \in Node |-> FALSE]

Spec == (Init /\ [][Next]_vars)

NextUnchanged == UNCHANGED <<table>>

TypeOK ==
/\ (table \in SUBSET((Node \X Node \X Node)))

Safety ==
/\ (\A t,x \in Node : (<<t,x,x>> \in table))
/\ (\A t,x,y,z \in Node : (((<<t,x,y>> \in table) /\ (<<t,y,z>> \in table)) => (<<t,x,z>> \in table)))
/\ (\A t,x,y \in Node : (((<<t,x,y>> \in table) /\ (<<t,y,x>> \in table)) => x = y))
/\ (\A t,x,y,z \in Node : (((<<t,x,y>> \in table) /\ (<<t,x,z>> \in table)) => ((<<t,y,z>> \in table) \/ (<<t,z,y>> \in table))))
=============================================================================
