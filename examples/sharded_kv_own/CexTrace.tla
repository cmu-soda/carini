--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS N1, N2, K1, K2, Node, Value, V1, V2, Key

VARIABLES owner, Fluent47_6, Fluent46_6, transfer_msg, cexTraceIdx

vars == <<owner, Fluent47_6, Fluent46_6, transfer_msg, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ owner = (N1 :> {} @@ N2 :> {})
  /\ Fluent46_6 = (K1 :> (N1 :> FALSE @@ N2 :> FALSE) @@ K2 :> (N1 :> FALSE @@ N2 :> FALSE))
  /\ Fluent47_6 = (K1 :> (N1 :> FALSE @@ N2 :> FALSE) @@ K2 :> (N1 :> FALSE @@ N2 :> FALSE))
  /\ transfer_msg = {}

/\ cexTraceIdx = 1 =>
  /\ owner = (N1 :> {} @@ N2 :> {})
  /\ Fluent46_6 = (K1 :> (N1 :> FALSE @@ N2 :> FALSE) @@ K2 :> (N1 :> FALSE @@ N2 :> FALSE))
  /\ Fluent47_6 = (K1 :> (N1 :> FALSE @@ N2 :> FALSE) @@ K2 :> (N1 :> FALSE @@ N2 :> FALSE))
  /\ transfer_msg = {<<N1, K1, V2>>}

/\ cexTraceIdx = 2 =>
  /\ owner = (N1 :> {} @@ N2 :> {})
  /\ Fluent46_6 = (K1 :> (N1 :> FALSE @@ N2 :> FALSE) @@ K2 :> (N1 :> FALSE @@ N2 :> FALSE))
  /\ Fluent47_6 = (K1 :> (N1 :> FALSE @@ N2 :> FALSE) @@ K2 :> (N1 :> FALSE @@ N2 :> FALSE))
  /\ transfer_msg = {<<N1, K1, V1>>, <<N1, K1, V2>>}

/\ cexTraceIdx = 3 =>
  /\ owner = (N1 :> {} @@ N2 :> {})
  /\ Fluent46_6 = (K1 :> (N1 :> FALSE @@ N2 :> FALSE) @@ K2 :> (N1 :> FALSE @@ N2 :> FALSE))
  /\ Fluent47_6 = (K1 :> (N1 :> FALSE @@ N2 :> FALSE) @@ K2 :> (N1 :> FALSE @@ N2 :> FALSE))
  /\ transfer_msg = {<<N1, K1, V1>>, <<N1, K1, V2>>, <<N2, K1, V1>>}

/\ cexTraceIdx = 4 =>
  /\ owner = (N1 :> {K1} @@ N2 :> {})
  /\ Fluent46_6 = (K1 :> (N1 :> FALSE @@ N2 :> FALSE) @@ K2 :> (N1 :> FALSE @@ N2 :> FALSE))
  /\ Fluent47_6 = (K1 :> (N1 :> TRUE @@ N2 :> FALSE) @@ K2 :> (N1 :> FALSE @@ N2 :> FALSE))
  /\ transfer_msg = {<<N1, K1, V2>>, <<N2, K1, V1>>}

/\ cexTraceIdx = 5 =>
  /\ owner = (N1 :> {K1} @@ N2 :> {})
  /\ Fluent46_6 = (K1 :> (N1 :> FALSE @@ N2 :> FALSE) @@ K2 :> (N1 :> FALSE @@ N2 :> FALSE))
  /\ Fluent47_6 = (K1 :> (N1 :> FALSE @@ N2 :> FALSE) @@ K2 :> (N1 :> TRUE @@ N2 :> TRUE))
  /\ transfer_msg = {<<N1, K1, V2>>, <<N2, K1, V1>>}

/\ cexTraceIdx = 6 =>
  /\ owner = (N1 :> {K1} @@ N2 :> {K1})
  /\ Fluent46_6 = (K1 :> (N1 :> FALSE @@ N2 :> FALSE) @@ K2 :> (N1 :> FALSE @@ N2 :> FALSE))
  /\ Fluent47_6 = (K1 :> (N1 :> FALSE @@ N2 :> TRUE) @@ K2 :> (N1 :> TRUE @@ N2 :> TRUE))
  /\ transfer_msg = {<<N1, K1, V2>>}

/\ cexTraceIdx = 7 =>
  /\ owner = (N1 :> {K1} @@ N2 :> {K1})
  /\ Fluent46_6 = (K1 :> (N1 :> FALSE @@ N2 :> FALSE) @@ K2 :> (N1 :> FALSE @@ N2 :> FALSE))
  /\ Fluent47_6 = (K1 :> (N1 :> TRUE @@ N2 :> TRUE) @@ K2 :> (N1 :> TRUE @@ N2 :> TRUE))
  /\ transfer_msg = {}

/\ cexTraceIdx = 8 =>
  /\ owner = (N1 :> {K1} @@ N2 :> {K1, K2})
  /\ Fluent46_6 = (K1 :> (N1 :> TRUE @@ N2 :> TRUE) @@ K2 :> (N1 :> TRUE @@ N2 :> TRUE))
  /\ Fluent47_6 = (K1 :> (N1 :> TRUE @@ N2 :> TRUE) @@ K2 :> (N1 :> TRUE @@ N2 :> TRUE))
  /\ transfer_msg = {}


CandSep == (\A var0 \in Node : (\E var1 \in Node : (\E var2 \in Key : (Fluent47_6[var2][var1] => ~(Fluent46_6[var2][var0])))))

Nil == "nil"

Reshard(k,v,n_old,n_new) ==
/\ owner' = [owner EXCEPT![n_old] = (owner[n_old] \ {k})]
/\ transfer_msg' = (transfer_msg \cup {<<n_new,k,v>>})
/\ Fluent47_6' = [Fluent47_6 EXCEPT![k][n_old] = FALSE]
/\ Fluent46_6' = [Fluent46_6 EXCEPT![k][n_old] = FALSE]
/\ UNCHANGED <<>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RecvTransferMsg(n,k,v) ==
/\ (<<n,k,v>> \in transfer_msg)
/\ transfer_msg' = (transfer_msg \ {<<n,k,v>>})
/\ owner' = [owner EXCEPT![n] = (owner[n] \cup {k})]
/\ Fluent47_6' = [Fluent47_6 EXCEPT![k][n] = TRUE]
/\ UNCHANGED <<Fluent46_6>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Put(n,k,v) ==
/\ (k \in owner[n])
/\ UNCHANGED <<owner,transfer_msg>>
/\ Fluent47_6' = [[x0 \in Key |-> [x1 \in Node |-> TRUE]] EXCEPT![k] = [x0 \in Node |-> FALSE]]
/\ UNCHANGED <<Fluent46_6>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Own(n,k) ==
/\ (\A n2 \in Node : (k \notin owner[n2]))
/\ (\A n2 \in Node : (\A v2 \in Value : (<<n2,k,v2>> \notin transfer_msg)))
/\ owner' = [owner EXCEPT![n] = (owner[n] \cup {k})]
/\ UNCHANGED <<transfer_msg>>
/\ Fluent46_6' = [x0 \in Key |-> [x1 \in Node |-> TRUE]]
/\ UNCHANGED <<Fluent47_6>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))
\/ (\E n \in Node, k \in Key, v \in Value : Put(n,k,v))
\/ (\E n \in Node, k \in Key : Own(n,k))

Init ==
/\ owner = [n \in Node |-> {}]
/\ transfer_msg = {}
/\ Fluent47_6 = [x0 \in Key |-> [x1 \in Node |-> FALSE]]
/\ Fluent46_6 = [x0 \in Key |-> [x1 \in Node |-> FALSE]]
/\ cexTraceIdx = 0
/\ TraceConstraint

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (owner \in [Node -> SUBSET(Key)])
/\ (transfer_msg \in SUBSET((Node \X Key \X Value)))
=============================================================================
