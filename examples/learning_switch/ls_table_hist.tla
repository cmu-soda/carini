--------------------------- MODULE ls_table_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node

VARIABLES Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, table

vars == <<Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, table>>

CandSep ==
/\ \A var0 \in Node : Fluent0[var0][var0]
/\ \A var0 \in Node : Fluent1[var0][var0]
/\ \A var0 \in Node : Fluent2[var0][var0][var0]
/\ \A var0 \in Node : Fluent3[var0][var0]
/\ \A var0 \in Node : Fluent4[var0][var0]
/\ \A var0 \in Node : (Fluent6[var0][var0]) => (Fluent5[var0])
/\ \A var0 \in Node : (Fluent7[var0]) => (Fluent8[var0][var0])
/\ \A var0 \in Node : (Fluent9[var0]) => (Fluent10[var0][var0])

Forward(ps,pd,sw0,sw1,nondet) ==
/\ table' = IF (ps /= sw1 /\ (\A w \in Node : (w /= sw1 => (<<ps,sw1,w>> \notin table)))) THEN (table \cup { <<px,n1,n2>> \in (Node \X Node \X Node) : (px = ps /\ ((<<ps,n1,sw1>> \in table) /\ (<<ps,sw0,n2>> \in table))) }) ELSE table
/\ Fluent9' = [Fluent9 EXCEPT![sw0] = TRUE]
/\ Fluent8' = [Fluent8 EXCEPT![sw0][pd] = TRUE]
/\ Fluent7' = [Fluent7 EXCEPT![ps] = TRUE]
/\ Fluent6' = [Fluent6 EXCEPT![pd][sw0] = TRUE]
/\ Fluent5' = [Fluent5 EXCEPT![ps] = TRUE]
/\ Fluent10' = [Fluent10 EXCEPT![sw1][sw0] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT![nondet][ps] = FALSE]
/\ Fluent3' = [Fluent3 EXCEPT![pd][nondet] = FALSE]
/\ Fluent2' = [Fluent2 EXCEPT![ps][nondet][pd] = FALSE]
/\ Fluent1' = [Fluent1 EXCEPT![nondet][sw1] = FALSE]
/\ Fluent0' = [Fluent0 EXCEPT![sw0][nondet] = FALSE]
/\ UNCHANGED<<>>
/\ CandSep'

Next ==
\/ (\E ps,pd,sw0,sw1,nondet \in Node : Forward(ps,pd,sw0,sw1,nondet))

Init ==
/\ table = { <<t,n1,n2>> \in (Node \X Node \X Node) : n1 = n2 }
/\ Fluent9 = [ x0 \in Node |-> FALSE]
/\ Fluent8 = [ x0 \in Node |-> [ x1 \in Node |-> FALSE]]
/\ Fluent7 = [ x0 \in Node |-> FALSE]
/\ Fluent6 = [ x0 \in Node |-> [ x1 \in Node |-> FALSE]]
/\ Fluent5 = [ x0 \in Node |-> FALSE]
/\ Fluent10 = [ x0 \in Node |-> [ x1 \in Node |-> FALSE]]
/\ Fluent4 = [ x0 \in Node |-> [ x1 \in Node |-> TRUE]]
/\ Fluent3 = [ x0 \in Node |-> [ x1 \in Node |-> TRUE]]
/\ Fluent2 = [ x0 \in Node |-> [ x1 \in Node |-> [ x2 \in Node |-> TRUE]]]
/\ Fluent1 = [ x0 \in Node |-> [ x1 \in Node |-> TRUE]]
/\ Fluent0 = [ x0 \in Node |-> [ x1 \in Node |-> TRUE]]

NextUnchanged == UNCHANGED <<table>>

TypeOK ==
/\ (table \in SUBSET((Node \X Node \X Node)))

Safety ==
/\ (\A t,x \in Node : (<<t,x,x>> \in table))
/\ (\A t,x,y,z \in Node : (((<<t,x,y>> \in table) /\ (<<t,y,z>> \in table)) => (<<t,x,z>> \in table)))
/\ (\A t,x,y \in Node : (((<<t,x,y>> \in table) /\ (<<t,y,x>> \in table)) => x = y))
/\ (\A t,x,y,z \in Node : (((<<t,x,y>> \in table) /\ (<<t,x,z>> \in table)) => ((<<t,y,z>> \in table) \/ (<<t,z,y>> \in table))))
=============================================================================
