--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS Quorum, n1, n2, n3, Node, NUM2, NUM0, NUM1, _n2n3_, _n1n2n3_, Value, Round, _n1n3_, v1, _n1n2_, v2

VARIABLES proposal, Fluent29_0, one_b, one_a, vote, cexTraceIdx

vars == <<proposal, Fluent29_0, one_b, one_a, vote, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ one_a = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent29_0 = ( {n1, n2} :> FALSE @@
    {n1, n3} :> FALSE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ vote = ( n1 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n2 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n3 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ proposal = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )

/\ cexTraceIdx = 1 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent29_0 = ( {n1, n2} :> FALSE @@
    {n1, n3} :> FALSE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ vote = ( n1 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n2 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n3 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ proposal = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )

/\ cexTraceIdx = 2 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent29_0 = ( {n1, n2} :> FALSE @@
    {n1, n3} :> FALSE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ vote = ( n1 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n2 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n3 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ proposal = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )

/\ cexTraceIdx = 3 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent29_0 = ( {n1, n2} :> FALSE @@
    {n1, n3} :> FALSE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ vote = ( n1 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n2 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n3 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ proposal = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )

/\ cexTraceIdx = 4 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent29_0 = ( {n1, n2} :> FALSE @@
    {n1, n3} :> FALSE @@
    {n2, n3} :> FALSE @@
    {n1, n2, n3} :> FALSE )
  /\ vote = ( n1 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n2 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n3 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ proposal = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> TRUE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )

/\ cexTraceIdx = 5 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent29_0 = ( {n1, n2} :> TRUE @@
    {n1, n3} :> TRUE @@
    {n2, n3} :> TRUE @@
    {n1, n2, n3} :> TRUE )
  /\ vote = ( n1 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> TRUE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n2 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n3 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ proposal = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> TRUE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )


CandSep == (\A var0 \in Quorum : ~(Fluent29_0[var0]))

None == 0

Init ==
/\ one_a = [r \in Round |-> FALSE]
/\ one_b = [n \in Node |-> [r \in Round |-> FALSE]]
/\ proposal = [r \in Round |-> [v \in Value |-> FALSE]]
/\ vote = [n \in Node |-> [r \in Round |-> [v \in Value |-> FALSE]]]
/\ Fluent29_0 = [x0 \in Quorum |-> FALSE]
/\ cexTraceIdx = 0
/\ TraceConstraint

send_1a(r) ==
/\ r /= None
/\ one_a' = [one_a EXCEPT![r] = TRUE]
/\ UNCHANGED <<one_b,proposal,vote>>
/\ UNCHANGED <<Fluent29_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

join_round(n,r) ==
/\ r /= None
/\ one_a[r]
/\ one_b' = [one_b EXCEPT![n][r] = TRUE]
/\ UNCHANGED <<one_a,proposal,vote>>
/\ UNCHANGED <<Fluent29_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

propose(r,q,maxr,v) ==
/\ r /= None
/\ (\A V \in Value : ~(proposal[r][V]))
/\ (\A N \in Node : ((N \in q) => one_b[N][r]))
/\ (maxr = None => (\A N \in Node, MAXR \in Round, V \in Value : ~((((N \in q) /\ ~(r <= MAXR)) /\ vote[N][MAXR][V]))))
/\ (maxr /= None => ((\E N \in Node : (((N \in q) /\ ~(r <= maxr)) /\ vote[N][maxr][v])) /\ (\A N \in Node, MAXR \in Round, V \in Value : ((((N \in q) /\ ~(r <= MAXR)) /\ vote[N][MAXR][V]) => MAXR <= maxr))))
/\ proposal' = [proposal EXCEPT![r][v] = TRUE]
/\ UNCHANGED <<one_a,one_b,vote>>
/\ UNCHANGED <<Fluent29_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

cast_vote(n,v,r) ==
/\ r /= None
/\ proposal[r][v]
/\ vote' = [vote EXCEPT![n][r][v] = TRUE]
/\ UNCHANGED <<one_a,one_b,proposal>>
/\ Fluent29_0' = [x0 \in Quorum |-> TRUE]
/\ UNCHANGED <<>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

decide(r,v,q) ==
/\ r /= None
/\ (\A N \in Node : ((N \in q) => vote[N][r][v]))
/\ UNCHANGED <<one_a,one_b,proposal,vote>>
/\ UNCHANGED <<Fluent29_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\/ (\E r \in Round : send_1a(r))
\/ (\E n \in Node, r \in Round : join_round(n,r))
\/ (\E r \in Round, q \in Quorum, maxr \in Round, v \in Value : propose(r,q,maxr,v))
\/ (\E n \in Node, v \in Value, r \in Round : cast_vote(n,v,r))
\/ (\E r \in Round, v \in Value, q \in Quorum : decide(r,v,q))

Spec == (Init /\ [][Next]_vars)
=============================================================================
