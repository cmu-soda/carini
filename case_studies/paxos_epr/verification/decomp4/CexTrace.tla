--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS Quorum, n1, n2, n3, Node, NUM2, NUM0, NUM1, _n2n3_, _n1n2n3_, Value, Round, _n1n3_, v1, _n1n2_, v2

VARIABLES Fluent40_7, Fluent41_7, one_b, one_a, Fluent39_7, left_round, vote, cexTraceIdx

vars == <<Fluent40_7, Fluent41_7, one_b, one_a, Fluent39_7, left_round, vote, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ one_a = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent40_7 = ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ Fluent41_7 = ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent39_7 = (v1 :> FALSE @@ v2 :> FALSE)
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

/\ cexTraceIdx = 1 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent40_7 = ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ Fluent41_7 = ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent39_7 = (v1 :> FALSE @@ v2 :> FALSE)
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

/\ cexTraceIdx = 2 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent40_7 = ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ Fluent41_7 = ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent39_7 = (v1 :> FALSE @@ v2 :> FALSE)
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

/\ cexTraceIdx = 3 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent40_7 = ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ Fluent41_7 = ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent39_7 = (v1 :> FALSE @@ v2 :> FALSE)
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

/\ cexTraceIdx = 4 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent40_7 = ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ Fluent41_7 = ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent39_7 = (v1 :> TRUE @@ v2 :> FALSE)
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

/\ cexTraceIdx = 5 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent40_7 = ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ Fluent41_7 = ( v1 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent39_7 = (v1 :> TRUE @@ v2 :> TRUE)
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

/\ cexTraceIdx = 6 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent40_7 = ( v1 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ Fluent41_7 = ( v1 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) @@
    v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent39_7 = (v1 :> TRUE @@ v2 :> TRUE)
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

/\ cexTraceIdx = 7 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent40_7 = ( v1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
    v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ Fluent41_7 = ( v1 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> FALSE) @@
    v2 :> (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent39_7 = (v1 :> TRUE @@ v2 :> TRUE)
  /\ vote = ( n1 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> TRUE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n2 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> TRUE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n3 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )

/\ cexTraceIdx = 8 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent40_7 = ( v1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
    v2 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ Fluent41_7 = ( v1 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> FALSE) @@
    v2 :> (n1 :> TRUE @@ n2 :> FALSE @@ n3 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent39_7 = (v1 :> TRUE @@ v2 :> TRUE)
  /\ vote = ( n1 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> TRUE @@ v2 :> TRUE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n2 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> TRUE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n3 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )

/\ cexTraceIdx = 9 =>
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent40_7 = ( v1 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) @@
    v2 :> (n1 :> FALSE @@ n2 :> TRUE @@ n3 :> FALSE) )
  /\ Fluent41_7 = ( v1 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> FALSE) @@
    v2 :> (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent39_7 = (v1 :> TRUE @@ v2 :> TRUE)
  /\ vote = ( n1 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> TRUE @@ v2 :> TRUE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n2 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> TRUE @@ v2 :> TRUE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    n3 :>
        ( 0 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )


CandSep == (\A var0 \in Node : (\E var1 \in Value : (Fluent41_7[var1][var0] => (Fluent39_7[var1] => Fluent40_7[var1][var0]))))

None == 0

Init ==
/\ one_a = [r \in Round |-> FALSE]
/\ one_b = [n \in Node |-> [r \in Round |-> FALSE]]
/\ left_round = [n \in Node |-> [r \in Round |-> FALSE]]
/\ vote = [n \in Node |-> [r \in Round |-> [v \in Value |-> FALSE]]]
/\ Fluent40_7 = [x0 \in Value |-> [x1 \in Node |-> FALSE]]
/\ Fluent41_7 = [x0 \in Value |-> [x1 \in Node |-> FALSE]]
/\ Fluent39_7 = [x0 \in Value |-> FALSE]
/\ cexTraceIdx = 0
/\ TraceConstraint

send_1a(r) ==
/\ r /= None
/\ one_a' = [one_a EXCEPT![r] = TRUE]
/\ UNCHANGED <<one_b,left_round,vote>>
/\ UNCHANGED <<Fluent40_7,Fluent41_7,Fluent39_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

join_round(n,r) ==
/\ r /= None
/\ one_a[r]
/\ ~(left_round[n][r])
/\ one_b' = [one_b EXCEPT![n][r] = TRUE]
/\ left_round' = [N \in Node |-> [R \in Round |-> (left_round[N][R] \/ (N = n /\ ~(r <= R)))]]
/\ UNCHANGED <<one_a,vote>>
/\ UNCHANGED <<Fluent40_7,Fluent41_7,Fluent39_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

propose(r,maxr,v) ==
/\ (\E q \in Quorum : ((((r /= None /\ (\A N \in Node : ((N \in q) => one_b[N][r]))) /\ (maxr = None => (\A N \in Node, MAXR \in Round, V \in Value : ~((((N \in q) /\ ~(r <= MAXR)) /\ vote[N][MAXR][V]))))) /\ (maxr /= None => ((\E N \in Node : (((N \in q) /\ ~(r <= maxr)) /\ vote[N][maxr][v])) /\ (\A N \in Node, MAXR \in Round, V \in Value : ((((N \in q) /\ ~(r <= MAXR)) /\ vote[N][MAXR][V]) => MAXR <= maxr))))) /\ UNCHANGED <<one_a,one_b,left_round,vote>>))
/\ Fluent39_7' = [Fluent39_7 EXCEPT![v] = TRUE]
/\ UNCHANGED <<Fluent40_7,Fluent41_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

cast_vote(n,v,r) ==
/\ r /= None
/\ ~(left_round[n][r])
/\ vote' = [vote EXCEPT![n][r][v] = TRUE]
/\ UNCHANGED <<one_a,one_b,left_round>>
/\ Fluent40_7' = [[Fluent40_7 EXCEPT![v] = [x0 \in Node |-> FALSE]] EXCEPT![v][n] = TRUE]
/\ Fluent41_7' = [Fluent41_7 EXCEPT![v][n] = TRUE]
/\ UNCHANGED <<Fluent39_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

decide(r,v) ==
/\ (\E q \in Quorum : ((r /= None /\ (\A N \in Node : ((N \in q) => vote[N][r][v]))) /\ UNCHANGED <<one_a,one_b,left_round,vote>>))
/\ UNCHANGED <<Fluent40_7,Fluent41_7,Fluent39_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\/ (\E r \in Round : send_1a(r))
\/ (\E n \in Node, r \in Round : join_round(n,r))
\/ (\E r \in Round, maxr \in Round, v \in Value : propose(r,maxr,v))
\/ (\E n \in Node, v \in Value, r \in Round : cast_vote(n,v,r))
\/ (\E r \in Round, v \in Value : decide(r,v))

Spec == (Init /\ [][Next]_vars)
=============================================================================
