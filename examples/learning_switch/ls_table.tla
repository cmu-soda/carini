---- MODULE ls_table ----
\* benchmark: pyv-learning-switch

EXTENDS TLC, Naturals, FiniteSets

CONSTANT 
    \* @type: Set(Str);
    Node

VARIABLE 
    \* @type: Set(<<Str, Str, Str>>);
    table

vars == <<table>>


\* @type: (Str, Str, Str, Str, Str) => Bool;
Forward(ps,pd,sw0,sw1,nondet) ==
    \* Remove all elements whose first element is not 'nondet',
    \* and also add elements for all d \in Node.
    /\ table' = IF ( (ps # sw1) /\ (\A w \in Node : w # sw1 => <<ps,sw1,w>> \notin table) )
                THEN  table \cup
                      {<<px,n1,n2>> \in Node \X Node \X Node : 
                            /\ px = ps 
                            /\ (<<ps,n1,sw1>> \in table /\ <<ps,sw0,n2>> \in table) }
                ELSE table

Next == 
    \/ \E ps,pd,sw0,sw1,nondet \in Node : Forward(ps,pd,sw0,sw1,nondet)

Init ==
    /\ table = {<<t,n1,n2>> \in (Node \X Node \X Node) : n1 = n2}

Spec == Init /\ [][Next]_vars

NextUnchanged == UNCHANGED <<table>>

TypeOK == 
    /\ table \in SUBSET (Node \X Node \X Node)

\* invariant [safety] 
\* (forall T, X. table(T,X,X)) & 
\* (forall T, X, Y, Z. table(T,X,Y) & table(T,Y,Z) -> table(T,X,Z)) &
\* (forall T, X, Y. table(T,X,Y) & table(T,Y,X) -> X = Y) & 
\* (forall T, X, Y, Z. table(T,X,Y) & table(T,X,Z) -> table(T,Y,Z) | table(T,Z,Y))
Safety == 
    /\ \A t,x \in Node : <<t,x,x>> \in table
    /\ \A t,x,y,z \in Node : (<<t,x,y>> \in table /\ <<t,y,z>> \in table) => (<<t,x,z>> \in table)
    /\ \A t,x,y \in Node : (<<t,x,y>> \in table /\ <<t,y,x>> \in table) => (x = y)
    /\ \A t,x,y,z \in Node : (<<t,x,y>> \in table /\ <<t,x,z>> \in table) => (<<t,y,z>> \in table \/ <<t,z,y>> \in table)

====
