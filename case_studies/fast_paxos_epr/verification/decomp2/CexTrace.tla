--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS n1, n2, n3, Node, NUM2, NUM0, NUM1, vv1, vv2, _n2n3_, _n1n2n3_, Value, Round, Quorum_f, _n1n2_, Quorum_c

VARIABLES proposal, one_b, one_a, Fluent22_32, any_msg, Fluent21_32, left_round, Fluent20_32, cexTraceIdx

vars == <<proposal, one_b, one_a, Fluent22_32, any_msg, Fluent21_32, left_round, Fluent20_32, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ any_msg = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ one_a = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent22_32 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent21_32 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent20_32 = ( 0 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    1 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    2 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) )
  /\ proposal = ( 0 :> (vv1 :> FALSE @@ vv2 :> FALSE) @@
    1 :> (vv1 :> FALSE @@ vv2 :> FALSE) @@
    2 :> (vv1 :> FALSE @@ vv2 :> FALSE) )

/\ cexTraceIdx = 1 =>
  /\ any_msg = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent22_32 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent21_32 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent20_32 = ( 0 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    1 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    2 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) )
  /\ proposal = ( 0 :> (vv1 :> FALSE @@ vv2 :> FALSE) @@
    1 :> (vv1 :> FALSE @@ vv2 :> FALSE) @@
    2 :> (vv1 :> FALSE @@ vv2 :> FALSE) )

/\ cexTraceIdx = 2 =>
  /\ any_msg = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent22_32 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent21_32 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent20_32 = ( 0 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    1 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    2 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) )
  /\ proposal = ( 0 :> (vv1 :> FALSE @@ vv2 :> FALSE) @@
    1 :> (vv1 :> FALSE @@ vv2 :> FALSE) @@
    2 :> (vv1 :> FALSE @@ vv2 :> FALSE) )

/\ cexTraceIdx = 3 =>
  /\ any_msg = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent22_32 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent21_32 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent20_32 = ( 0 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    1 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    2 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) )
  /\ proposal = ( 0 :> (vv1 :> FALSE @@ vv2 :> FALSE) @@
    1 :> (vv1 :> FALSE @@ vv2 :> FALSE) @@
    2 :> (vv1 :> FALSE @@ vv2 :> FALSE) )

/\ cexTraceIdx = 4 =>
  /\ any_msg = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent22_32 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent21_32 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent20_32 = ( 0 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    1 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    2 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) )
  /\ proposal = ( 0 :> (vv1 :> FALSE @@ vv2 :> FALSE) @@
    1 :> (vv1 :> FALSE @@ vv2 :> FALSE) @@
    2 :> (vv1 :> FALSE @@ vv2 :> FALSE) )

/\ cexTraceIdx = 5 =>
  /\ any_msg = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE) @@
    n2 :> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent22_32 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent21_32 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent20_32 = ( 0 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    1 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    2 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) )
  /\ proposal = ( 0 :> (vv1 :> FALSE @@ vv2 :> FALSE) @@
    1 :> (vv1 :> FALSE @@ vv2 :> FALSE) @@
    2 :> (vv1 :> FALSE @@ vv2 :> FALSE) )

/\ cexTraceIdx = 6 =>
  /\ any_msg = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent22_32 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent21_32 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent20_32 = ( 0 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    1 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    2 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) )
  /\ proposal = ( 0 :> (vv1 :> FALSE @@ vv2 :> FALSE) @@
    1 :> (vv1 :> FALSE @@ vv2 :> FALSE) @@
    2 :> (vv1 :> FALSE @@ vv2 :> FALSE) )

/\ cexTraceIdx = 7 =>
  /\ any_msg = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent22_32 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent21_32 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent20_32 = ( 0 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    1 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    2 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) )
  /\ proposal = ( 0 :> (vv1 :> FALSE @@ vv2 :> FALSE) @@
    1 :> (vv1 :> TRUE @@ vv2 :> FALSE) @@
    2 :> (vv1 :> FALSE @@ vv2 :> FALSE) )

/\ cexTraceIdx = 8 =>
  /\ any_msg = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE)
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent22_32 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent21_32 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent20_32 = ( 0 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    1 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    2 :> ({n1, n2} :> TRUE @@ {n2, n3} :> FALSE) )
  /\ proposal = ( 0 :> (vv1 :> FALSE @@ vv2 :> FALSE) @@
    1 :> (vv1 :> TRUE @@ vv2 :> FALSE) @@
    2 :> (vv1 :> FALSE @@ vv2 :> FALSE) )

/\ cexTraceIdx = 9 =>
  /\ any_msg = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE)
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent22_32 = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
  /\ Fluent21_32 = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ Fluent20_32 = ( 0 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    1 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    2 :> ({n1, n2} :> TRUE @@ {n2, n3} :> FALSE) )
  /\ proposal = ( 0 :> (vv1 :> FALSE @@ vv2 :> FALSE) @@
    1 :> (vv1 :> TRUE @@ vv2 :> FALSE) @@
    2 :> (vv1 :> FALSE @@ vv2 :> FALSE) )

/\ cexTraceIdx = 10 =>
  /\ any_msg = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE)
  /\ one_a = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE)
  /\ one_b = ( n1 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    n2 :> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ left_round = ( n1 :> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n2 :> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE) @@
    n3 :> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE) )
  /\ Fluent22_32 = (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE)
  /\ Fluent21_32 = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)
  /\ Fluent20_32 = ( 0 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    1 :> ({n1, n2} :> FALSE @@ {n2, n3} :> FALSE) @@
    2 :> ({n1, n2} :> TRUE @@ {n2, n3} :> FALSE) )
  /\ proposal = ( 0 :> (vv1 :> FALSE @@ vv2 :> FALSE) @@
    1 :> (vv1 :> TRUE @@ vv2 :> FALSE) @@
    2 :> (vv1 :> FALSE @@ vv2 :> FALSE) )


CandSep == (\A var0 \in Round : (\A var1 \in Quorum_c : (Fluent22_32[var0] => (Fluent20_32[var0][var1] => Fluent21_32[var0]))))

None == 0

Init ==
/\ one_a = [R \in Round |-> FALSE]
/\ one_b = [N \in Node |-> [R \in Round |-> FALSE]]
/\ left_round = [N \in Node |-> [R \in Round |-> FALSE]]
/\ proposal = [R \in Round |-> [V \in Value |-> FALSE]]
/\ any_msg = [R \in Round |-> FALSE]
/\ Fluent22_32 = [x0 \in Round |-> FALSE]
/\ Fluent21_32 = [x0 \in Round |-> FALSE]
/\ Fluent20_32 = [x0 \in Round |-> [x1 \in Quorum_c |-> FALSE]]
/\ cexTraceIdx = 0
/\ TraceConstraint

send_1a(r) ==
/\ r /= None
/\ one_a' = [one_a EXCEPT![r] = TRUE]
/\ UNCHANGED <<one_b,left_round,proposal,any_msg>>
/\ UNCHANGED <<Fluent22_32,Fluent21_32,Fluent20_32>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

join_round(n,r) ==
/\ r /= None
/\ one_a[r]
/\ ~(left_round[n][r])
/\ one_b' = [one_b EXCEPT![n][r] = TRUE]
/\ left_round' = [N \in Node |-> [R \in Round |-> (left_round[N][R] \/ (N = n /\ R < r))]]
/\ UNCHANGED <<one_a,proposal,any_msg>>
/\ UNCHANGED <<Fluent22_32,Fluent21_32,Fluent20_32>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

propose_1(r,q,maxr,v,v2) ==
/\ r /= None
/\ (\A V \in Value : ~(proposal[r][V]))
/\ ~(any_msg[r])
/\ (\A N \in q : one_b[N][r])
/\ maxr /= None
/\ proposal' = [proposal EXCEPT![r][v2] = TRUE]
/\ UNCHANGED <<one_a,one_b,left_round,any_msg>>
/\ Fluent20_32' = [Fluent20_32 EXCEPT![r][q] = Fluent20_32[maxr][q]]
/\ UNCHANGED <<Fluent22_32,Fluent21_32>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

propose_2(r,q,maxr,v) ==
/\ r /= None
/\ (\A V \in Value : ~(proposal[r][V]))
/\ ~(any_msg[r])
/\ (\A N \in q : one_b[N][r])
/\ maxr /= None
/\ proposal' = [proposal EXCEPT![r][v] = TRUE]
/\ UNCHANGED <<one_a,one_b,left_round,any_msg>>
/\ UNCHANGED <<Fluent22_32,Fluent21_32,Fluent20_32>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

propose_3(r,q,v) ==
/\ r /= None
/\ (\A V \in Value : ~(proposal[r][V]))
/\ ~(any_msg[r])
/\ (\A N \in q : one_b[N][r])
/\ any_msg' = [any_msg EXCEPT![r] = TRUE]
/\ UNCHANGED <<one_a,one_b,left_round,proposal>>
/\ Fluent20_32' = [Fluent20_32 EXCEPT![r][q] = TRUE]
/\ UNCHANGED <<Fluent22_32,Fluent21_32>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

propose_4(r,q,v) ==
/\ r /= None
/\ (\A V \in Value : ~(proposal[r][V]))
/\ ~(any_msg[r])
/\ (\A N \in q : one_b[N][r])
/\ proposal' = [proposal EXCEPT![r][v] = TRUE]
/\ UNCHANGED <<one_a,one_b,left_round,any_msg>>
/\ UNCHANGED <<Fluent22_32,Fluent21_32,Fluent20_32>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

cast_vote(n,v,r) ==
/\ r /= None
/\ ~(left_round[n][r])
/\ (proposal[r][v] \/ any_msg[r])
/\ UNCHANGED <<one_a,one_b,left_round,proposal,any_msg>>
/\ Fluent22_32' = [x0 \in Round |-> Fluent21_32[r]]
/\ Fluent21_32' = [Fluent21_32 EXCEPT![r] = TRUE]
/\ UNCHANGED <<Fluent20_32>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\/ (\E r \in Round : send_1a(r))
\/ (\E n \in Node, r \in Round : join_round(n,r))
\/ (\E r \in Round, q \in Quorum_c, maxr \in Round, v,v2 \in Value : propose_1(r,q,maxr,v,v2))
\/ (\E r \in Round, q \in Quorum_c, maxr \in Round, v \in Value : propose_2(r,q,maxr,v))
\/ (\E r \in Round, q \in Quorum_c, v \in Value : propose_3(r,q,v))
\/ (\E r \in Round, q \in Quorum_c, v \in Value : propose_4(r,q,v))
\/ (\E n \in Node, v \in Value, r \in Round : cast_vote(n,v,r))

Spec == (Init /\ [][Next]_vars)
=============================================================================
