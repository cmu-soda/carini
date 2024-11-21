---- MODULE ls_pending ----
\* benchmark: pyv-learning-switch

EXTENDS TLC, Naturals, FiniteSets

CONSTANT 
    \* @type: Set(Str);
    Node

VARIABLE 
    \* @type: Set(<<Str, Str, Str, Str>>);
    pending

vars == <<pending>>

\* @type: (Str, Str) => Bool;
NewPacket(ps,pd) ==
    /\ pending' = pending \cup {<<ps,pd,ps,ps>>}

\* @type: (Str, Str, Str, Str, Str) => Bool;
Forward(ps,pd,sw0,sw1,nondet) ==
    /\ <<ps,pd,sw0,sw1>> \in pending
    \* Remove all elements whose first element is not 'nondet',
    \* and also add elements for all d \in Node.
    /\ pending' = 
        {<<psa,pda,sw1a,da>> \in pending : psa = nondet} \cup 
        {<<ps,pd,sw1,d>> : d \in Node}

Next == 
    \/ \E ps,pd \in Node : NewPacket(ps,pd)
    \/ \E ps,pd,sw0,sw1,nondet \in Node : Forward(ps,pd,sw0,sw1,nondet)

Init ==
    /\ pending = {}

Spec == Init /\ [][Next]_vars

NextUnchanged == UNCHANGED <<pending>>

TypeOK == 
    /\ pending \in SUBSET (Node \X Node \X Node \X Node)

====
