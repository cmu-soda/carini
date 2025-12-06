--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS a1, a2, Address, Value, v1, v2, c1, c2, Core

VARIABLES shared, Fluent154_0, exclusive, Fluent156_0, Fluent155_0, cexTraceIdx

vars == <<shared, Fluent154_0, exclusive, Fluent156_0, Fluent155_0, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ Fluent154_0 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ Fluent155_0 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ Fluent156_0 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ exclusive = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ shared = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))

/\ cexTraceIdx = 1 =>
  /\ Fluent154_0 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ Fluent155_0 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ Fluent156_0 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ exclusive = (c1 :> (a1 :> TRUE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ shared = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))

/\ cexTraceIdx = 2 =>
  /\ Fluent154_0 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ Fluent155_0 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ Fluent156_0 = (a1 :> TRUE @@ a2 :> FALSE)
  /\ exclusive = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ shared = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))

/\ cexTraceIdx = 3 =>
  /\ Fluent154_0 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ Fluent155_0 = (a1 :> FALSE @@ a2 :> TRUE)
  /\ Fluent156_0 = (a1 :> TRUE @@ a2 :> FALSE)
  /\ exclusive = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ shared = (c1 :> (a1 :> FALSE @@ a2 :> TRUE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))

/\ cexTraceIdx = 4 =>
  /\ Fluent154_0 = (a1 :> TRUE @@ a2 :> TRUE)
  /\ Fluent155_0 = (a1 :> FALSE @@ a2 :> TRUE)
  /\ Fluent156_0 = (a1 :> TRUE @@ a2 :> FALSE)
  /\ exclusive = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ shared = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))


CandSep == (\A var0 \in Address : (Fluent154_0[var0] => (Fluent156_0[var0] => Fluent155_0[var0])))

Init ==
/\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
/\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
/\ Fluent154_0 = [x0 \in Address |-> FALSE]
/\ Fluent156_0 = [x0 \in Address |-> FALSE]
/\ Fluent155_0 = [x0 \in Address |-> FALSE]
/\ cexTraceIdx = 0
/\ TraceConstraint

do_bus_read_valid(c,a,v) ==
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ Fluent155_0' = [Fluent155_0 EXCEPT![a] = TRUE]
/\ UNCHANGED <<Fluent154_0,Fluent156_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

complete_proc_read_invalid_shared(c,a,v) ==
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<exclusive>>
/\ UNCHANGED <<Fluent154_0,Fluent156_0,Fluent155_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<shared>>
/\ UNCHANGED <<Fluent154_0,Fluent156_0,Fluent155_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

do_bus_read_for_ownership_valid(c,a,v) ==
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<Fluent154_0,Fluent156_0,Fluent155_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

proc_write_exclusive(c,a,v) ==
/\ exclusive[c][a]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<shared>>
/\ UNCHANGED <<Fluent154_0,Fluent156_0,Fluent155_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

issue_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ UNCHANGED <<exclusive,shared>>
/\ UNCHANGED <<Fluent154_0,Fluent156_0,Fluent155_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

do_bus_upgrade(c,a) ==
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<exclusive>>
/\ UNCHANGED <<Fluent154_0,Fluent156_0,Fluent155_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

complete_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<exclusive>>
/\ Fluent154_0' = [x0 \in Address |-> Fluent155_0[a]]
/\ UNCHANGED <<Fluent156_0,Fluent155_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

evict_exclusive_or_shared(c,a) ==
/\ (exclusive[c][a] \/ shared[c][a])
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ Fluent154_0' = [Fluent154_0 EXCEPT![a] = FALSE]
/\ Fluent156_0' = [Fluent156_0 EXCEPT![a] = TRUE]
/\ UNCHANGED <<Fluent155_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\E c \in Core :
\E a \in Address :
\E v \in Value :
\/ do_bus_read_valid(c,a,v)
\/ complete_proc_read_invalid_shared(c,a,v)
\/ complete_proc_read_invalid_exclusive(c,a,v)
\/ do_bus_read_for_ownership_valid(c,a,v)
\/ proc_write_exclusive(c,a,v)
\/ issue_proc_write_shared(c,a,v)
\/ do_bus_upgrade(c,a)
\/ complete_proc_write_shared(c,a,v)
\/ evict_exclusive_or_shared(c,a)

Spec == (Init /\ [][Next]_vars)
=============================================================================
