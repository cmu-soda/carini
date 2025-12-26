--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS a1, c3, a2, Address, Value, v1, v2, c1, c2, Core

VARIABLES shared, upgraded, upgrading, bus_mode, invalid, exclusive, modified, cexTraceIdx

vars == <<shared, upgraded, upgrading, bus_mode, invalid, exclusive, modified, cexTraceIdx>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ invalid = ( c1 :> (a1 :> TRUE @@ a2 :> TRUE) @@
    c2 :> (a1 :> TRUE @@ a2 :> TRUE) @@
    c3 :> (a1 :> TRUE @@ a2 :> TRUE) )
  /\ upgraded = FALSE
  /\ exclusive = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_mode = "not_used"
  /\ shared = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ modified = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ upgrading = FALSE

/\ cexTraceIdx = 1 =>
  /\ invalid = ( c1 :> (a1 :> TRUE @@ a2 :> TRUE) @@
    c2 :> (a1 :> TRUE @@ a2 :> TRUE) @@
    c3 :> (a1 :> TRUE @@ a2 :> TRUE) )
  /\ upgraded = FALSE
  /\ exclusive = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_mode = "read"
  /\ shared = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ modified = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ upgrading = FALSE

/\ cexTraceIdx = 2 =>
  /\ invalid = ( c1 :> (a1 :> FALSE @@ a2 :> TRUE) @@
    c2 :> (a1 :> TRUE @@ a2 :> TRUE) @@
    c3 :> (a1 :> TRUE @@ a2 :> TRUE) )
  /\ upgraded = FALSE
  /\ exclusive = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_mode = "not_used"
  /\ shared = ( c1 :> (a1 :> TRUE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ modified = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ upgrading = FALSE

/\ cexTraceIdx = 3 =>
  /\ invalid = ( c1 :> (a1 :> FALSE @@ a2 :> TRUE) @@
    c2 :> (a1 :> TRUE @@ a2 :> TRUE) @@
    c3 :> (a1 :> TRUE @@ a2 :> TRUE) )
  /\ upgraded = FALSE
  /\ exclusive = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_mode = "write"
  /\ shared = ( c1 :> (a1 :> TRUE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ modified = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ upgrading = TRUE

/\ cexTraceIdx = 4 =>
  /\ invalid = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> TRUE @@ a2 :> TRUE) @@
    c3 :> (a1 :> TRUE @@ a2 :> TRUE) )
  /\ upgraded = FALSE
  /\ exclusive = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_mode = "not_used"
  /\ shared = ( c1 :> (a1 :> TRUE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ modified = ( c1 :> (a1 :> FALSE @@ a2 :> TRUE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ upgrading = TRUE

/\ cexTraceIdx = 5 =>
  /\ invalid = ( c1 :> (a1 :> FALSE @@ a2 :> TRUE) @@
    c2 :> (a1 :> TRUE @@ a2 :> TRUE) @@
    c3 :> (a1 :> TRUE @@ a2 :> TRUE) )
  /\ upgraded = TRUE
  /\ exclusive = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_mode = "not_used"
  /\ shared = ( c1 :> (a1 :> TRUE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ modified = ( c1 :> (a1 :> FALSE @@ a2 :> TRUE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ upgrading = TRUE


CandSep ==
/\ bus_mode /= "bad"
/\ (upgraded => upgrading)

Init ==
/\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
/\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
/\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
/\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]
/\ bus_mode = "not_used"
/\ upgrading = FALSE
/\ upgraded = FALSE
/\ cexTraceIdx = 0
/\ TraceConstraint

issue_proc_read_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<modified,exclusive,shared,invalid>>
/\ UNCHANGED <<upgrading,upgraded>>
/\ bus_mode' = IF bus_mode = "not_used" THEN "read" ELSE "bad"
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

do_bus_read_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<modified,exclusive,shared,invalid>>
/\ UNCHANGED <<bus_mode,upgrading,upgraded>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

do_bus_read_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ ~(modified[c][a])
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<invalid>>
/\ UNCHANGED <<bus_mode,upgrading,upgraded>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

do_bus_read_modified(c,a,v) ==
/\ ~(invalid[c][a])
/\ modified[c][a]
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<invalid>>
/\ UNCHANGED <<bus_mode,upgrading,upgraded>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

complete_proc_read_invalid_shared(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<modified,exclusive>>
/\ UNCHANGED <<upgrading,upgraded>>
/\ bus_mode' = IF bus_mode = "read" THEN "not_used" ELSE "bad"
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<modified,shared>>
/\ UNCHANGED <<upgrading,upgraded>>
/\ bus_mode' = IF bus_mode = "read" THEN "not_used" ELSE "bad"
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

issue_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ UNCHANGED <<modified,exclusive,shared,invalid>>
/\ UNCHANGED <<upgrading,upgraded>>
/\ bus_mode' = IF bus_mode = "not_used" THEN "write" ELSE "bad"
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

do_bus_read_for_ownership_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<modified,exclusive,shared,invalid>>
/\ UNCHANGED <<bus_mode,upgrading,upgraded>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

do_bus_read_for_ownership_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ ~(modified[c][a])
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<bus_mode,upgrading,upgraded>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

do_bus_read_for_ownership_modified(c,a,v) ==
/\ ~(invalid[c][a])
/\ modified[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<bus_mode,upgrading,upgraded>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

complete_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<exclusive,shared>>
/\ UNCHANGED <<upgrading,upgraded>>
/\ bus_mode' = IF bus_mode = "write" THEN "not_used" ELSE "bad"
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

proc_write_exclusive(c,a,v) ==
/\ exclusive[c][a]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<shared,invalid>>
/\ UNCHANGED <<upgrading,upgraded>>
/\ bus_mode' = IF bus_mode = "not_used" THEN "not_used" ELSE "bad"
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

issue_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ UNCHANGED <<modified,exclusive,shared,invalid>>
/\ UNCHANGED <<upgraded>>
/\ bus_mode' = IF bus_mode = "not_used" THEN "write" ELSE "bad"
/\ upgrading' = TRUE
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

do_bus_upgrade(c,a) ==
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<modified,exclusive>>
/\ UNCHANGED <<bus_mode,upgrading>>
/\ upgraded' = TRUE
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

complete_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<exclusive,invalid>>
/\ bus_mode' = IF bus_mode = "write" THEN "not_used" ELSE "bad"
/\ upgrading' = FALSE
/\ upgraded' = FALSE
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

evict_modified(c,a) ==
/\ modified[c][a]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<exclusive,shared>>
/\ UNCHANGED <<upgrading,upgraded>>
/\ bus_mode' = IF bus_mode = "not_used" THEN "not_used" ELSE "bad"
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

evict_exclusive_or_shared(c,a) ==
/\ (exclusive[c][a] \/ shared[c][a])
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<modified>>
/\ UNCHANGED <<upgrading,upgraded>>
/\ bus_mode' = IF bus_mode = "not_used" THEN "not_used" ELSE "bad"
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\E c \in Core :
\E a \in Address :
\E v \in Value :
\/ issue_proc_read_invalid(c,a)
\/ do_bus_read_invalid(c,a)
\/ do_bus_read_valid(c,a,v)
\/ do_bus_read_modified(c,a,v)
\/ complete_proc_read_invalid_shared(c,a,v)
\/ complete_proc_read_invalid_exclusive(c,a,v)
\/ issue_proc_write_invalid(c,a,v)
\/ do_bus_read_for_ownership_invalid(c,a)
\/ do_bus_read_for_ownership_valid(c,a,v)
\/ do_bus_read_for_ownership_modified(c,a,v)
\/ complete_proc_write_invalid(c,a,v)
\/ proc_write_exclusive(c,a,v)
\/ issue_proc_write_shared(c,a,v)
\/ do_bus_upgrade(c,a)
\/ complete_proc_write_shared(c,a,v)
\/ evict_modified(c,a)
\/ evict_exclusive_or_shared(c,a)

Spec == (Init /\ [][Next]_vars)

Safety == (\A C \in Core, A \in Address : (~((invalid[C][A] /\ modified[C][A])) /\ ~((invalid[C][A] /\ exclusive[C][A])) /\ ~((invalid[C][A] /\ shared[C][A])) /\ ~((modified[C][A] /\ exclusive[C][A])) /\ ~((modified[C][A] /\ shared[C][A])) /\ ~((exclusive[C][A] /\ shared[C][A]))))
=============================================================================
