--------------------------- MODULE ls_table_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node

VARIABLES Fluent12, Fluent11, Fluent9, Fluent8, Fluent13, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, table

vars == <<Fluent12, Fluent11, Fluent9, Fluent8, Fluent13, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0, table>>

CandSep ==
/\ \A var0 \in Node : (Fluent0[var0]) => (Fluent1[var0][var0])
/\ \A var0 \in Node : (Fluent3[var0][var0]) => (Fluent2[var0][var0])
/\ \A var0 \in Node : \E var1 \in Node : ((Fluent4[var0][var0][var1]) => (var0 = var1)) => (~(Fluent5[var0][var0][var1]))
/\ \A var0 \in Node : (Fluent6[var0][var0]) => (Fluent7[var0][var0])
/\ \A var0 \in Node : \E var1 \in Node : (Fluent9[var0][var0]) => (Fluent8[var1][var0][var1])
/\ \A var0 \in Node : \E var1 \in Node : ((Fluent10[var0][var1][var0]) => (var1 = var0)) => (~(Fluent11[var0][var1]))
/\ \A var0 \in Node : (Fluent12[var0]) => (Fluent13[var0][var0][var0])

Forward(ps,pd,sw0,sw1,nondet) ==
/\ table' = IF (ps /= sw1 /\ (\A w \in Node : (w /= sw1 => (<<ps,sw1,w>> \notin table)))) THEN (table \cup { <<px,n1,n2>> \in (Node \X Node \X Node) : (px = ps /\ ((<<ps,n1,sw1>> \in table) /\ (<<ps,sw0,n2>> \in table))) }) ELSE table
/\ Fluent12' = [Fluent12 EXCEPT ![ps] = TRUE]
/\ Fluent11' = [Fluent11 EXCEPT ![ps][sw0] = TRUE]
/\ Fluent9' = [Fluent9 EXCEPT ![pd][sw1] = TRUE]
/\ Fluent8' = [Fluent8 EXCEPT ![sw0][pd][sw1] = TRUE]
/\ Fluent13' = [Fluent13 EXCEPT ![sw0][sw1][ps] = TRUE]
/\ Fluent7' = [Fluent7 EXCEPT ![sw1][pd] = TRUE]
/\ Fluent6' = [Fluent6 EXCEPT ![sw0][pd] = TRUE]
/\ Fluent5' = [Fluent5 EXCEPT ![pd][ps][sw0] = TRUE]
/\ Fluent10' = [Fluent10 EXCEPT ![ps][sw1][sw0] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT ![sw0][ps][sw1] = TRUE]
/\ Fluent3' = [Fluent3 EXCEPT ![pd][ps] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT ![pd][sw0] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT ![sw1][sw0] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT ![ps] = TRUE]
/\ UNCHANGED<<>>
/\ CandSep'

Next ==
\/ (\E ps,pd,sw0,sw1,nondet \in Node : Forward(ps,pd,sw0,sw1,nondet))

Init ==
/\ table = { <<t,n1,n2>> \in (Node \X Node \X Node) : n1 = n2 }
/\ Fluent12 = [ x0 \in Node |-> FALSE]
/\ Fluent11 = [ x0 \in Node |-> [ x1 \in Node |-> FALSE]]
/\ Fluent9 = [ x0 \in Node |-> [ x1 \in Node |-> FALSE]]
/\ Fluent8 = [ x0 \in Node |-> [ x1 \in Node |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent13 = [ x0 \in Node |-> [ x1 \in Node |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent7 = [ x0 \in Node |-> [ x1 \in Node |-> FALSE]]
/\ Fluent6 = [ x0 \in Node |-> [ x1 \in Node |-> FALSE]]
/\ Fluent5 = [ x0 \in Node |-> [ x1 \in Node |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent10 = [ x0 \in Node |-> [ x1 \in Node |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent4 = [ x0 \in Node |-> [ x1 \in Node |-> [ x2 \in Node |-> FALSE]]]
/\ Fluent3 = [ x0 \in Node |-> [ x1 \in Node |-> FALSE]]
/\ Fluent2 = [ x0 \in Node |-> [ x1 \in Node |-> FALSE]]
/\ Fluent1 = [ x0 \in Node |-> [ x1 \in Node |-> FALSE]]
/\ Fluent0 = [ x0 \in Node |-> FALSE]

NextUnchanged == UNCHANGED <<table>>

TypeOK ==
/\ (table \in SUBSET((Node \X Node \X Node)))

Safety ==
/\ (\A t,x \in Node : (<<t,x,x>> \in table))
/\ (\A t,x,y,z \in Node : (((<<t,x,y>> \in table) /\ (<<t,y,z>> \in table)) => (<<t,x,z>> \in table)))
/\ (\A t,x,y \in Node : (((<<t,x,y>> \in table) /\ (<<t,y,x>> \in table)) => x = y))
/\ (\A t,x,y,z \in Node : (((<<t,x,y>> \in table) /\ (<<t,x,z>> \in table)) => ((<<t,y,z>> \in table) \/ (<<t,z,y>> \in table))))
=============================================================================
