--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS N1, N2, K1, K2, Node, Value, V1, V2, Key

VARIABLES owner, Fluent15_11, transfer_msg, Fluent14_11, cexTraceIdx

vars == <<owner, Fluent15_11, transfer_msg, Fluent14_11, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ owner = (N1 :> {} @@ N2 :> {K2})
  /\ transfer_msg = {}
  /\ Fluent15_11 = (N1 :> (K1 :> FALSE @@ K2 :> FALSE) @@ N2 :> (K1 :> FALSE @@ K2 :> FALSE))
  /\ Fluent14_11 = (N1 :> (K1 :> FALSE @@ K2 :> FALSE) @@ N2 :> (K1 :> FALSE @@ K2 :> FALSE))

/\ cexTraceIdx = 1 =>
  /\ owner = (N1 :> {} @@ N2 :> {K2})
  /\ transfer_msg = {}
  /\ Fluent15_11 = (N1 :> (K1 :> FALSE @@ K2 :> FALSE) @@ N2 :> (K1 :> FALSE @@ K2 :> TRUE))
  /\ Fluent14_11 = (N1 :> (K1 :> FALSE @@ K2 :> FALSE) @@ N2 :> (K1 :> FALSE @@ K2 :> TRUE))

/\ cexTraceIdx = 2 =>
  /\ owner = (N1 :> {} @@ N2 :> {K2})
  /\ transfer_msg = {<<N1, K2, V1>>}
  /\ Fluent15_11 = (N1 :> (K1 :> FALSE @@ K2 :> FALSE) @@ N2 :> (K1 :> FALSE @@ K2 :> TRUE))
  /\ Fluent14_11 = (N1 :> (K1 :> FALSE @@ K2 :> FALSE) @@ N2 :> (K1 :> FALSE @@ K2 :> FALSE))

/\ cexTraceIdx = 3 =>
  /\ owner = (N1 :> {K2} @@ N2 :> {K2})
  /\ transfer_msg = {}
  /\ Fluent15_11 = (N1 :> (K1 :> FALSE @@ K2 :> FALSE) @@ N2 :> (K1 :> FALSE @@ K2 :> TRUE))
  /\ Fluent14_11 = (N1 :> (K1 :> FALSE @@ K2 :> FALSE) @@ N2 :> (K1 :> FALSE @@ K2 :> FALSE))

/\ cexTraceIdx = 4 =>
  /\ owner = (N1 :> {K2} @@ N2 :> {K2})
  /\ transfer_msg = {}
  /\ Fluent15_11 = (N1 :> (K1 :> FALSE @@ K2 :> TRUE) @@ N2 :> (K1 :> FALSE @@ K2 :> TRUE))
  /\ Fluent14_11 = (N1 :> (K1 :> FALSE @@ K2 :> TRUE) @@ N2 :> (K1 :> FALSE @@ K2 :> FALSE))


CandSep == (\A var0 \in Key : (\A var1 \in Node : (\E var2 \in Node : (Fluent15_11[var2][var0] => Fluent14_11[var1][var0]))))

Nil == "nil"

Reshard(k,v,n_old,n_new) ==
/\ owner' = [owner EXCEPT![n_old] = (owner[n_old] \ {k})]
/\ transfer_msg' = (transfer_msg \cup {<<n_new,k,v>>})
/\ Fluent14_11' = [x0 \in Node |-> [x1 \in Key |-> FALSE]]
/\ UNCHANGED <<Fluent15_11>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RecvTransferMsg(n,k,v) ==
/\ (<<n,k,v>> \in transfer_msg)
/\ transfer_msg' = (transfer_msg \ {<<n,k,v>>})
/\ owner' = [owner EXCEPT![n] = (owner[n] \cup {k})]
/\ UNCHANGED <<Fluent15_11,Fluent14_11>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Put(n,k,v) ==
/\ (k \in owner[n])
/\ UNCHANGED <<owner,transfer_msg>>
/\ Fluent15_11' = [Fluent15_11 EXCEPT![n][k] = TRUE]
/\ Fluent14_11' = [Fluent14_11 EXCEPT![n][k] = TRUE]
/\ UNCHANGED <<>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))
\/ (\E n \in Node, k \in Key, v \in Value : Put(n,k,v))

Init ==
/\ (owner \in [Node -> SUBSET(Key)])
/\ (\A i,j \in Node : (\A k \in Key : (((k \in owner[i]) /\ (k \in owner[j])) => i = j)))
/\ transfer_msg = {}
/\ Fluent15_11 = [x0 \in Node |-> [x1 \in Key |-> FALSE]]
/\ Fluent14_11 = [x0 \in Node |-> [x1 \in Key |-> FALSE]]
/\ cexTraceIdx = 0
/\ TraceConstraint

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (owner \in [Node -> SUBSET(Key)])
/\ (transfer_msg \in SUBSET((Node \X Key \X Value)))
=============================================================================
