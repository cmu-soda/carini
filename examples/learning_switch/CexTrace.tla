--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, e1, e2, e3

VARIABLES pending, Fluent131_0, Fluent132_0, cexTraceIdx

vars == <<pending, Fluent131_0, Fluent132_0, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ Fluent132_0 = ( e1 :>
        ( e1 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e2 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) ) @@
    e2 :>
        ( e1 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e2 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) ) @@
    e3 :>
        ( e1 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e2 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) ) )
  /\ pending = {}
  /\ Fluent131_0 = ( e1 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
    e2 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
    e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) )

/\ cexTraceIdx = 1 =>
  /\ Fluent132_0 = ( e1 :>
        ( e1 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e2 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) ) @@
    e2 :>
        ( e1 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e2 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) ) @@
    e3 :>
        ( e1 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e2 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) ) )
  /\ pending = {<<e1, e2, e1, e1>>}
  /\ Fluent131_0 = ( e1 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
    e2 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
    e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) )

/\ cexTraceIdx = 2 =>
  /\ Fluent132_0 = ( e1 :>
        ( e1 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e2 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) ) @@
    e2 :>
        ( e1 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e2 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) ) @@
    e3 :>
        ( e1 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e2 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) ) )
  /\ pending = {<<e1, e2, e1, e1>>, <<e1, e2, e1, e2>>, <<e1, e2, e1, e3>>}
  /\ Fluent131_0 = ( e1 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
    e2 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
    e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) )

/\ cexTraceIdx = 3 =>
  /\ Fluent132_0 = ( e1 :>
        ( e1 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e2 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) ) @@
    e2 :>
        ( e1 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e2 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) ) @@
    e3 :>
        ( e1 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e2 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) ) )
  /\ pending = { <<e1, e2, e1, e1>>,
    <<e1, e2, e1, e2>>,
    <<e1, e2, e1, e3>>,
    <<e1, e2, e2, e1>>,
    <<e1, e2, e2, e2>>,
    <<e1, e2, e2, e3>> }
  /\ Fluent131_0 = ( e1 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
    e2 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
    e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) )

/\ cexTraceIdx = 4 =>
  /\ Fluent132_0 = ( e1 :>
        ( e1 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e2 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) ) @@
    e2 :>
        ( e1 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e2 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) ) @@
    e3 :>
        ( e1 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e2 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) ) )
  /\ pending = { <<e1, e2, e1, e1>>,
    <<e1, e2, e1, e2>>,
    <<e1, e2, e1, e3>>,
    <<e1, e2, e2, e1>>,
    <<e1, e2, e2, e2>>,
    <<e1, e2, e2, e3>>,
    <<e1, e2, e3, e1>>,
    <<e1, e2, e3, e2>>,
    <<e1, e2, e3, e3>> }
  /\ Fluent131_0 = ( e1 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
    e2 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
    e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) )

/\ cexTraceIdx = 5 =>
  /\ Fluent132_0 = ( e1 :>
        ( e1 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e2 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e3 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) ) @@
    e2 :>
        ( e1 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e2 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) ) @@
    e3 :>
        ( e1 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e2 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
          e3 :> (e1 :> FALSE @@ e2 :> FALSE @@ e3 :> FALSE) ) )
  /\ pending = { <<e1, e2, e1, e1>>,
    <<e1, e2, e1, e2>>,
    <<e1, e2, e1, e3>>,
    <<e1, e2, e2, e1>>,
    <<e1, e2, e2, e2>>,
    <<e1, e2, e2, e3>>,
    <<e1, e2, e3, e1>>,
    <<e1, e2, e3, e2>>,
    <<e1, e2, e3, e3>> }
  /\ Fluent131_0 = ( e1 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
    e2 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) @@
    e3 :> (e1 :> TRUE @@ e2 :> FALSE @@ e3 :> FALSE) )


CandSep == (\A var0 \in Node : (\A var1 \in Node : (Fluent131_0[var0][var1] => Fluent132_0[var0][var1][var1])))

NewPacket(ps,pd) ==
/\ pending' = (pending \cup {<<ps,pd,ps,ps>>})
/\ UNCHANGED <<Fluent131_0,Fluent132_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Forward(ps,pd,sw0,sw1,nondet) ==
/\ (<<ps,pd,sw0,sw1>> \in pending)
/\ pending' = ({ <<psa,pda,sw1a,da>> \in pending : psa = nondet } \cup { <<ps,pd,sw1,d>> : d \in Node })
/\ Fluent131_0' = [Fluent131_0 EXCEPT![sw0][ps] = TRUE]
/\ Fluent132_0' = [[Fluent132_0 EXCEPT![sw1][sw0][ps] = TRUE] EXCEPT![sw1][pd][nondet] = TRUE]
/\ UNCHANGED <<>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\/ (\E ps,pd \in Node : NewPacket(ps,pd))
\/ (\E ps,pd,sw0,sw1,nondet \in Node : Forward(ps,pd,sw0,sw1,nondet))

Init ==
/\ pending = {}
/\ Fluent131_0 = [x0 \in Node |-> [x1 \in Node |-> FALSE]]
/\ Fluent132_0 = [x0 \in Node |-> [x1 \in Node |-> [x2 \in Node |-> FALSE]]]
/\ cexTraceIdx = 0
/\ TraceConstraint

Spec == (Init /\ [][Next]_vars)

NextUnchanged == UNCHANGED <<pending>>

TypeOK ==
/\ (pending \in SUBSET((Node \X Node \X Node \X Node)))
=============================================================================
