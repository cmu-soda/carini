--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS Quorum, n1, n2, n3, Node, NUM2, NUM0, NUM1, _n2n3_, _n1n2n3_, Value, Round, _n1n3_, v1, _n1n2_, v2

VARIABLES proposal, one_b, one_a, Fluent28_28, cexTraceIdx, Fluent29_28

vars == <<proposal, one_b, one_a, Fluent28_28, cexTraceIdx, Fluent29_28>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ one_a = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent29_28 = ( v1 :>
        ( {n1, n2} :> FALSE @@
          {n1, n3} :> FALSE @@
          {n2, n3} :> FALSE @@
          {n1, n2, n3} :> FALSE ) @@
    v2 :>
        ( {n1, n2} :> FALSE @@
          {n1, n3} :> FALSE @@
          {n2, n3} :> FALSE @@
          {n1, n2, n3} :> FALSE ) )
  /\ Fluent28_28 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ proposal = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )

/\ cexTraceIdx = 1 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent29_28 = ( v1 :>
        ( {n1, n2} :> FALSE @@
          {n1, n3} :> FALSE @@
          {n2, n3} :> FALSE @@
          {n1, n2, n3} :> FALSE ) @@
    v2 :>
        ( {n1, n2} :> FALSE @@
          {n1, n3} :> FALSE @@
          {n2, n3} :> FALSE @@
          {n1, n2, n3} :> FALSE ) )
  /\ Fluent28_28 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ proposal = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )

/\ cexTraceIdx = 2 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent29_28 = ( v1 :>
        ( {n1, n2} :> FALSE @@
          {n1, n3} :> FALSE @@
          {n2, n3} :> FALSE @@
          {n1, n2, n3} :> FALSE ) @@
    v2 :>
        ( {n1, n2} :> FALSE @@
          {n1, n3} :> FALSE @@
          {n2, n3} :> FALSE @@
          {n1, n2, n3} :> FALSE ) )
  /\ Fluent28_28 = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ proposal = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )

/\ cexTraceIdx = 3 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent29_28 = ( v1 :>
        ( {n1, n2} :> FALSE @@
          {n1, n3} :> FALSE @@
          {n2, n3} :> FALSE @@
          {n1, n2, n3} :> FALSE ) @@
    v2 :>
        ( {n1, n2} :> FALSE @@
          {n1, n3} :> FALSE @@
          {n2, n3} :> FALSE @@
          {n1, n2, n3} :> FALSE ) )
  /\ Fluent28_28 = (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE)
  /\ proposal = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )

/\ cexTraceIdx = 4 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent29_28 = ( v1 :>
        ( {n1, n2} :> FALSE @@
          {n1, n3} :> FALSE @@
          {n2, n3} :> FALSE @@
          {n1, n2, n3} :> FALSE ) @@
    v2 :>
        ( {n1, n2} :> FALSE @@
          {n1, n3} :> FALSE @@
          {n2, n3} :> FALSE @@
          {n1, n2, n3} :> FALSE ) )
  /\ Fluent28_28 = (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> FALSE)
  /\ proposal = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )

/\ cexTraceIdx = 5 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) )
  /\ Fluent29_28 = ( v1 :>
        ( {n1, n2} :> FALSE @@
          {n1, n3} :> FALSE @@
          {n2, n3} :> FALSE @@
          {n1, n2, n3} :> FALSE ) @@
    v2 :>
        ( {n1, n2} :> FALSE @@
          {n1, n3} :> FALSE @@
          {n2, n3} :> FALSE @@
          {n1, n2, n3} :> FALSE ) )
  /\ Fluent28_28 = (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE)
  /\ proposal = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )

/\ cexTraceIdx = 6 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) )
  /\ Fluent29_28 = ( v1 :>
        ( {n1, n2} :> FALSE @@
          {n1, n3} :> FALSE @@
          {n2, n3} :> FALSE @@
          {n1, n2, n3} :> FALSE ) @@
    v2 :>
        ( {n1, n2} :> FALSE @@
          {n1, n3} :> FALSE @@
          {n2, n3} :> FALSE @@
          {n1, n2, n3} :> FALSE ) )
  /\ Fluent28_28 = (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE)
  /\ proposal = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )

/\ cexTraceIdx = 7 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    n3 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) )
  /\ Fluent29_28 = ( v1 :>
        ( {n1, n2} :> FALSE @@
          {n1, n3} :> FALSE @@
          {n2, n3} :> FALSE @@
          {n1, n2, n3} :> FALSE ) @@
    v2 :>
        ( {n1, n2} :> FALSE @@
          {n1, n3} :> FALSE @@
          {n2, n3} :> FALSE @@
          {n1, n2, n3} :> FALSE ) )
  /\ Fluent28_28 = (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE)
  /\ proposal = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )

/\ cexTraceIdx = 8 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    n3 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) )
  /\ Fluent29_28 = ( v1 :>
        ( {n1, n2} :> TRUE @@
          {n1, n3} :> FALSE @@
          {n2, n3} :> FALSE @@
          {n1, n2, n3} :> FALSE ) @@
    v2 :>
        ( {n1, n2} :> FALSE @@
          {n1, n3} :> FALSE @@
          {n2, n3} :> FALSE @@
          {n1, n2, n3} :> FALSE ) )
  /\ Fluent28_28 = (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE)
  /\ proposal = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> TRUE @@ v2 :> FALSE) )

/\ cexTraceIdx = 9 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    n3 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) )
  /\ Fluent29_28 = ( v1 :>
        ( {n1, n2} :> TRUE @@
          {n1, n3} :> FALSE @@
          {n2, n3} :> FALSE @@
          {n1, n2, n3} :> FALSE ) @@
    v2 :>
        ( {n1, n2} :> TRUE @@
          {n1, n3} :> FALSE @@
          {n2, n3} :> FALSE @@
          {n1, n2, n3} :> FALSE ) )
  /\ Fluent28_28 = (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE)
  /\ proposal = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> TRUE) @@
    2 :> (v1 :> TRUE @@ v2 :> FALSE) )


CandSep == (\A var0 \in Quorum : (\E var1 \in Node : (\E var2 \in Value : (Fluent29_28[var2][var0] => ~(Fluent28_28[var1])))))

None == 0

Init ==
/\ one_a = [r \in Round |-> FALSE]
/\ one_b = [n \in Node |-> [r \in Round |-> FALSE]]
/\ proposal = [r \in Round |-> [v \in Value |-> FALSE]]
/\ Fluent28_28 = [x0 \in Node |-> FALSE]
/\ Fluent29_28 = [x0 \in Value |-> [x1 \in Quorum |-> FALSE]]
/\ cexTraceIdx = 0
/\ TraceConstraint

send_1a(r) ==
/\ r /= None
/\ one_a' = [one_a EXCEPT![r] = TRUE]
/\ UNCHANGED <<one_b,proposal>>
/\ UNCHANGED <<Fluent28_28,Fluent29_28>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

join_round(n,r) ==
/\ r /= None
/\ one_a[r]
/\ one_b' = [one_b EXCEPT![n][r] = TRUE]
/\ UNCHANGED <<one_a,proposal>>
/\ Fluent28_28' = [Fluent28_28 EXCEPT![n] = TRUE]
/\ UNCHANGED <<Fluent29_28>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

propose(r,q,maxr,v) ==
/\ r /= None
/\ (\A V \in Value : ~(proposal[r][V]))
/\ (\A N \in Node : ((N \in q) => one_b[N][r]))
/\ proposal' = [proposal EXCEPT![r][v] = TRUE]
/\ UNCHANGED <<one_a,one_b>>
/\ Fluent29_28' = [Fluent29_28 EXCEPT![v][q] = TRUE]
/\ UNCHANGED <<Fluent28_28>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

cast_vote(n,v,r) ==
/\ r /= None
/\ proposal[r][v]
/\ UNCHANGED <<one_a,one_b,proposal>>
/\ UNCHANGED <<Fluent28_28,Fluent29_28>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\/ (\E r \in Round : send_1a(r))
\/ (\E n \in Node, r \in Round : join_round(n,r))
\/ (\E r \in Round, q \in Quorum, maxr \in Round, v \in Value : propose(r,q,maxr,v))
\/ (\E n \in Node, v \in Value, r \in Round : cast_vote(n,v,r))

Spec == (Init /\ [][Next]_vars)
=============================================================================
