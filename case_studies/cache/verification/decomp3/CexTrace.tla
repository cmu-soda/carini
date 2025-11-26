--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS a1, a2, Address, Value, v1, v2, c1, c2, Core

VARIABLES Fluent137_14, proc_write, Fluent136_14, proc_read, bus_read_for_ownership, bus_transfer, invalid, bus_read, bus_upgrade, cexTraceIdx, bus_in_use

vars == <<Fluent137_14, proc_write, Fluent136_14, proc_read, bus_read_for_ownership, bus_transfer, invalid, bus_read, bus_upgrade, cexTraceIdx, bus_in_use>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ proc_read = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_transfer = (v1 :> FALSE @@ v2 :> FALSE)
  /\ invalid = (c1 :> (a1 :> TRUE @@ a2 :> TRUE) @@ c2 :> (a1 :> TRUE @@ a2 :> TRUE))
  /\ bus_read_for_ownership = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_in_use = FALSE
  /\ proc_write = ( c1 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c2 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ Fluent137_14 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ Fluent136_14 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ bus_read = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_upgrade = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))

/\ cexTraceIdx = 1 =>
  /\ proc_read = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_transfer = (v1 :> FALSE @@ v2 :> FALSE)
  /\ invalid = (c1 :> (a1 :> TRUE @@ a2 :> TRUE) @@ c2 :> (a1 :> TRUE @@ a2 :> TRUE))
  /\ bus_read_for_ownership = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_in_use = TRUE
  /\ proc_write = ( c1 :>
        ( a1 :> (v1 :> TRUE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c2 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ Fluent137_14 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ Fluent136_14 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ bus_read = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_upgrade = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> TRUE @@ a2 :> FALSE))

/\ cexTraceIdx = 2 =>
  /\ proc_read = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_transfer = (v1 :> FALSE @@ v2 :> FALSE)
  /\ invalid = (c1 :> (a1 :> FALSE @@ a2 :> TRUE) @@ c2 :> (a1 :> TRUE @@ a2 :> TRUE))
  /\ bus_read_for_ownership = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_in_use = FALSE
  /\ proc_write = ( c1 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c2 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ Fluent137_14 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ Fluent136_14 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ bus_read = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_upgrade = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> TRUE @@ a2 :> FALSE))

/\ cexTraceIdx = 3 =>
  /\ proc_read = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> TRUE @@ a2 :> FALSE))
  /\ bus_transfer = (v1 :> FALSE @@ v2 :> FALSE)
  /\ invalid = (c1 :> (a1 :> FALSE @@ a2 :> TRUE) @@ c2 :> (a1 :> TRUE @@ a2 :> TRUE))
  /\ bus_read_for_ownership = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_in_use = TRUE
  /\ proc_write = ( c1 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c2 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ Fluent137_14 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ Fluent136_14 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ bus_read = (c1 :> (a1 :> TRUE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_upgrade = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> TRUE @@ a2 :> FALSE))

/\ cexTraceIdx = 4 =>
  /\ proc_read = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> TRUE @@ a2 :> FALSE))
  /\ bus_transfer = (v1 :> TRUE @@ v2 :> FALSE)
  /\ invalid = (c1 :> (a1 :> FALSE @@ a2 :> TRUE) @@ c2 :> (a1 :> TRUE @@ a2 :> TRUE))
  /\ bus_read_for_ownership = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_in_use = TRUE
  /\ proc_write = ( c1 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c2 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ Fluent137_14 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ Fluent136_14 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ bus_read = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_upgrade = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> TRUE @@ a2 :> FALSE))

/\ cexTraceIdx = 5 =>
  /\ proc_read = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_transfer = (v1 :> FALSE @@ v2 :> FALSE)
  /\ invalid = (c1 :> (a1 :> FALSE @@ a2 :> TRUE) @@ c2 :> (a1 :> FALSE @@ a2 :> TRUE))
  /\ bus_read_for_ownership = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_in_use = FALSE
  /\ proc_write = ( c1 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c2 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ Fluent137_14 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ Fluent136_14 = (a1 :> TRUE @@ a2 :> FALSE)
  /\ bus_read = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_upgrade = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> TRUE @@ a2 :> FALSE))

/\ cexTraceIdx = 6 =>
  /\ proc_read = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_transfer = (v1 :> FALSE @@ v2 :> FALSE)
  /\ invalid = (c1 :> (a1 :> TRUE @@ a2 :> TRUE) @@ c2 :> (a1 :> FALSE @@ a2 :> TRUE))
  /\ bus_read_for_ownership = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_in_use = FALSE
  /\ proc_write = ( c1 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c2 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ Fluent137_14 = (a1 :> FALSE @@ a2 :> FALSE)
  /\ Fluent136_14 = (a1 :> TRUE @@ a2 :> FALSE)
  /\ bus_read = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_upgrade = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> TRUE @@ a2 :> FALSE))

/\ cexTraceIdx = 7 =>
  /\ proc_read = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_transfer = (v1 :> FALSE @@ v2 :> FALSE)
  /\ invalid = (c1 :> (a1 :> TRUE @@ a2 :> TRUE) @@ c2 :> (a1 :> FALSE @@ a2 :> TRUE))
  /\ bus_read_for_ownership = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> TRUE @@ a2 :> FALSE))
  /\ bus_in_use = TRUE
  /\ proc_write = ( c1 :>
        ( a1 :> (v1 :> TRUE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c2 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ Fluent137_14 = (a1 :> TRUE @@ a2 :> FALSE)
  /\ Fluent136_14 = (a1 :> TRUE @@ a2 :> FALSE)
  /\ bus_read = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> FALSE @@ a2 :> FALSE))
  /\ bus_upgrade = (c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@ c2 :> (a1 :> TRUE @@ a2 :> FALSE))


CandSep == (\A var0 \in Address : (Fluent137_14[var0] => ~(Fluent136_14[var0])))

Init ==
/\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]
/\ proc_read = [c \in Core |-> [a \in Address |-> FALSE]]
/\ proc_write = [c \in Core |-> [a \in Address |-> [v \in Value |-> FALSE]]]
/\ bus_in_use = FALSE
/\ bus_read = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_read_for_ownership = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_upgrade = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_transfer = [v \in Value |-> FALSE]
/\ Fluent137_14 = [x0 \in Address |-> FALSE]
/\ Fluent136_14 = [x0 \in Address |-> FALSE]
/\ cexTraceIdx = 0
/\ TraceConstraint

issue_proc_read_invalid(c,a) ==
/\ invalid[c][a]
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_read' = [proc_read EXCEPT![c][a] = TRUE]
/\ bus_read' = [C \in Core |-> [A \in Address |-> (bus_read[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<invalid,proc_write,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ Fluent137_14' = [Fluent137_14 EXCEPT![a] = FALSE]
/\ UNCHANGED <<Fluent136_14>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

do_bus_read_invalid(c,a) ==
/\ invalid[c][a]
/\ bus_read[c][a]
/\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<invalid,proc_read,proc_write,bus_in_use,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED <<Fluent137_14,Fluent136_14>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

do_bus_read_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ bus_read[c][a]
/\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
/\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
/\ UNCHANGED <<invalid,proc_read,proc_write,bus_in_use,bus_read_for_ownership,bus_upgrade>>
/\ UNCHANGED <<Fluent137_14,Fluent136_14>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

complete_proc_read_invalid_shared(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ proc_read[c][a]
/\ bus_transfer[v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_read[C][A])))
/\ bus_transfer' = [V \in Value |-> FALSE]
/\ bus_in_use' = FALSE
/\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<proc_write,bus_read,bus_read_for_ownership,bus_upgrade>>
/\ Fluent136_14' = [Fluent136_14 EXCEPT![a] = TRUE]
/\ UNCHANGED <<Fluent137_14>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ proc_read[c][a]
/\ (\A V \in Value : ~(bus_transfer[V]))
/\ (\A C \in Core : (\A A \in Address : ~(bus_read[C][A])))
/\ bus_in_use' = FALSE
/\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<proc_write,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED <<Fluent137_14,Fluent136_14>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

issue_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
/\ bus_read_for_ownership' = [C \in Core |-> [A \in Address |-> (bus_read_for_ownership[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<invalid,proc_read,bus_read,bus_upgrade,bus_transfer>>
/\ Fluent137_14' = [Fluent137_14 EXCEPT![a] = TRUE]
/\ UNCHANGED <<Fluent136_14>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

do_bus_read_for_ownership_invalid(c,a) ==
/\ invalid[c][a]
/\ bus_read_for_ownership[c][a]
/\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<invalid,proc_read,proc_write,bus_in_use,bus_read,bus_upgrade,bus_transfer>>
/\ UNCHANGED <<Fluent137_14,Fluent136_14>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

do_bus_read_for_ownership_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ bus_read_for_ownership[c][a]
/\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
/\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read,bus_upgrade>>
/\ UNCHANGED <<Fluent137_14,Fluent136_14>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

complete_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ proc_write[c][a][v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_read_for_ownership[C][A])))
/\ bus_transfer' = [V \in Value |-> FALSE]
/\ bus_in_use' = FALSE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
/\ UNCHANGED <<proc_read,bus_read,bus_read_for_ownership,bus_upgrade>>
/\ UNCHANGED <<Fluent137_14,Fluent136_14>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

proc_write_exclusive(c,a,v) ==
/\ ~(bus_in_use)
/\ UNCHANGED <<invalid,proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED <<Fluent137_14,Fluent136_14>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

issue_proc_write_shared(c,a,v) ==
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
/\ bus_upgrade' = [C \in Core |-> [A \in Address |-> (bus_upgrade[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<invalid,proc_read,bus_read,bus_read_for_ownership,bus_transfer>>
/\ UNCHANGED <<Fluent137_14,Fluent136_14>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

do_bus_upgrade(c,a) ==
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ bus_upgrade[c][a]
/\ bus_upgrade' = [bus_upgrade EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_transfer>>
/\ UNCHANGED <<Fluent137_14,Fluent136_14>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

complete_proc_write_shared(c,a,v) ==
/\ proc_write[c][a][v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_upgrade[C][A])))
/\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
/\ bus_in_use' = FALSE
/\ UNCHANGED <<invalid,proc_read,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED <<Fluent137_14,Fluent136_14>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

evict_modified(c,a) ==
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ ~(bus_in_use)
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED <<Fluent137_14,Fluent136_14>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

evict_exclusive_or_shared(c,a) ==
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ ~(bus_in_use)
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED <<Fluent137_14,Fluent136_14>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\E c \in Core :
\E a \in Address :
\E v \in Value :
\/ issue_proc_read_invalid(c,a)
\/ do_bus_read_invalid(c,a)
\/ do_bus_read_valid(c,a,v)
\/ complete_proc_read_invalid_shared(c,a,v)
\/ complete_proc_read_invalid_exclusive(c,a,v)
\/ issue_proc_write_invalid(c,a,v)
\/ do_bus_read_for_ownership_invalid(c,a)
\/ do_bus_read_for_ownership_valid(c,a,v)
\/ complete_proc_write_invalid(c,a,v)
\/ proc_write_exclusive(c,a,v)
\/ issue_proc_write_shared(c,a,v)
\/ do_bus_upgrade(c,a)
\/ complete_proc_write_shared(c,a,v)
\/ evict_modified(c,a)
\/ evict_exclusive_or_shared(c,a)

Spec == (Init /\ [][Next]_vars)
=============================================================================
