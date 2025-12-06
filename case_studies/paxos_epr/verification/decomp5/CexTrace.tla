--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS Quorum, n1, n2, n3, Node, NUM2, NUM0, NUM1, _n2n3_, _n1n2n3_, Value, Round, _n1n3_, v1, _n1n2_, v2

VARIABLES Fluent11_49, one_b, one_a, left_round, Fluent12_49, cexTraceIdx

vars == <<Fluent11_49, one_b, one_a, left_round, Fluent12_49, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ one_a = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent12_49 = ( 0 :>
        ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
          v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) ) @@
    1 :>
        ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
          v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) ) @@
    2 :>
        ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
          v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) ) )
  /\ Fluent11_49 = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )

/\ cexTraceIdx = 1 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent12_49 = ( 0 :>
        ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
          v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) ) @@
    1 :>
        ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
          v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) ) @@
    2 :>
        ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
          v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) ) )
  /\ Fluent11_49 = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )

/\ cexTraceIdx = 2 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent12_49 = ( 0 :>
        ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
          v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) ) @@
    1 :>
        ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
          v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) ) @@
    2 :>
        ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
          v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) ) )
  /\ Fluent11_49 = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )

/\ cexTraceIdx = 3 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent12_49 = ( 0 :>
        ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
          v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) ) @@
    1 :>
        ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
          v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) ) @@
    2 :>
        ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
          v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) ) )
  /\ Fluent11_49 = ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )

/\ cexTraceIdx = 4 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent12_49 = ( 0 :>
        ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
          v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) ) @@
    1 :>
        ( v1 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) @@
          v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) ) @@
    2 :>
        ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
          v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) ) )
  /\ Fluent11_49 = ( 0 :> (v1 :> TRUE @@ v2 :> FALSE) @@
    1 :> (v1 :> TRUE @@ v2 :> TRUE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )

/\ cexTraceIdx = 5 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent12_49 = ( 0 :>
        ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
          v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) ) @@
    1 :>
        ( v1 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) @@
          v2 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) ) @@
    2 :>
        ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
          v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) ) )
  /\ Fluent11_49 = ( 0 :> (v1 :> TRUE @@ v2 :> TRUE) @@
    1 :> (v1 :> TRUE @@ v2 :> TRUE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )

/\ cexTraceIdx = 6 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent12_49 = ( 0 :>
        ( v1 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) @@
          v2 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) ) @@
    1 :>
        ( v1 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) @@
          v2 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) ) @@
    2 :>
        ( v1 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) @@
          v2 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) ) )
  /\ Fluent11_49 = ( 0 :> (v1 :> TRUE @@ v2 :> TRUE) @@
    1 :> (v1 :> TRUE @@ v2 :> TRUE) @@
    2 :> (v1 :> FALSE @@ v2 :> FALSE) )

/\ cexTraceIdx = 7 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent12_49 = ( 0 :>
        ( v1 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) @@
          v2 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) ) @@
    1 :>
        ( v1 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) @@
          v2 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) ) @@
    2 :>
        ( v1 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) @@
          v2 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) ) )
  /\ Fluent11_49 = ( 0 :> (v1 :> TRUE @@ v2 :> TRUE) @@
    1 :> (v1 :> TRUE @@ v2 :> TRUE) @@
    2 :> (v1 :> TRUE @@ v2 :> FALSE) )

/\ cexTraceIdx = 8 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent12_49 = ( 0 :>
        ( v1 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) @@
          v2 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) ) @@
    1 :>
        ( v1 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) @@
          v2 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) ) @@
    2 :>
        ( v1 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) @@
          v2 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE) ) )
  /\ Fluent11_49 = ( 0 :> (v1 :> TRUE @@ v2 :> TRUE) @@
    1 :> (v1 :> TRUE @@ v2 :> TRUE) @@
    2 :> (v1 :> TRUE @@ v2 :> TRUE) )


CandSep == (\A var0 \in Node : (\E var1 \in Value : (\E var2 \in Round : (Fluent12_49[var2][var1][var0] => ~(Fluent11_49[var2][var1])))))

None == 0

Init ==
/\ one_a = [r \in Round |-> FALSE]
/\ one_b = [n \in Node |-> [r \in Round |-> FALSE]]
/\ left_round = [n \in Node |-> [r \in Round |-> FALSE]]
/\ Fluent11_49 = [x0 \in Round |-> [x1 \in Value |-> FALSE]]
/\ Fluent12_49 = [x0 \in Round |-> [x1 \in Value |-> [x2 \in Node |-> FALSE]]]
/\ cexTraceIdx = 0
/\ TraceConstraint

send_1a(r) ==
/\ r /= None
/\ one_a' = [one_a EXCEPT![r] = TRUE]
/\ UNCHANGED <<one_b,left_round>>
/\ UNCHANGED <<Fluent11_49,Fluent12_49>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

join_round(n,r) ==
/\ r /= None
/\ one_a[r]
/\ ~(left_round[n][r])
/\ one_b' = [one_b EXCEPT![n][r] = TRUE]
/\ left_round' = [N \in Node |-> [R \in Round |-> (left_round[N][R] \/ (N = n /\ ~(r <= R)))]]
/\ UNCHANGED <<one_a>>
/\ UNCHANGED <<Fluent11_49,Fluent12_49>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

propose(r,q,maxr,v) ==
/\ (\A N \in Node : ((N \in q) => one_b[N][r]))
/\ UNCHANGED <<one_a,one_b,left_round>>
/\ Fluent11_49' = [[Fluent11_49 EXCEPT![r] = [x0 \in Value |-> TRUE]] EXCEPT![maxr][v] = TRUE]
/\ Fluent12_49' = [Fluent12_49 EXCEPT![r][v] = [x0 \in Node |-> TRUE]]
/\ UNCHANGED <<>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

cast_vote(n,v,r) ==
/\ r /= None
/\ ~(left_round[n][r])
/\ UNCHANGED <<one_a,one_b,left_round>>
/\ Fluent12_49' = [x0 \in Round |-> [x1 \in Value |-> [x2 \in Node |-> Fluent12_49[r][v][n]]]]
/\ UNCHANGED <<Fluent11_49>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\/ (\E r \in Round : send_1a(r))
\/ (\E n \in Node, r \in Round : join_round(n,r))
\/ (\E r \in Round, q \in Quorum, maxr \in Round, v \in Value : propose(r,q,maxr,v))
\/ (\E n \in Node, v \in Value, r \in Round : cast_vote(n,v,r))

Spec == (Init /\ [][Next]_vars)
=============================================================================
