--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS a1, c3, a2, Address, Value, v1, v2, c1, c2, Core

VARIABLES shared, proc_write, proc_read, bus_read_for_ownership, bus_transfer, exclusive, Fluent104_7, bus_read, bus_upgrade, cexTraceIdx, bus_in_use

vars == <<shared, proc_write, proc_read, bus_read_for_ownership, bus_transfer, exclusive, Fluent104_7, bus_read, bus_upgrade, cexTraceIdx, bus_in_use>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ proc_read = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_transfer = (v1 :> FALSE @@ v2 :> FALSE)
  /\ Fluent104_7 = (c1 :> FALSE @@ c2 :> FALSE @@ c3 :> FALSE)
  /\ bus_read_for_ownership = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_in_use = FALSE
  /\ exclusive = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ proc_write = ( c1 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c2 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c3 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ bus_read = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ shared = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_upgrade = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )

/\ cexTraceIdx = 1 =>
  /\ proc_read = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_transfer = (v1 :> FALSE @@ v2 :> FALSE)
  /\ Fluent104_7 = (c1 :> FALSE @@ c2 :> FALSE @@ c3 :> FALSE)
  /\ bus_read_for_ownership = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> TRUE @@ a2 :> FALSE) @@
    c3 :> (a1 :> TRUE @@ a2 :> FALSE) )
  /\ bus_in_use = TRUE
  /\ exclusive = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ proc_write = ( c1 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> TRUE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c2 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c3 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ bus_read = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ shared = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_upgrade = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )

/\ cexTraceIdx = 2 =>
  /\ proc_read = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_transfer = (v1 :> FALSE @@ v2 :> FALSE)
  /\ Fluent104_7 = (c1 :> TRUE @@ c2 :> FALSE @@ c3 :> TRUE)
  /\ bus_read_for_ownership = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> TRUE @@ a2 :> FALSE) )
  /\ bus_in_use = TRUE
  /\ exclusive = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ proc_write = ( c1 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> TRUE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c2 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c3 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ bus_read = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ shared = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_upgrade = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )

/\ cexTraceIdx = 3 =>
  /\ proc_read = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_transfer = (v1 :> TRUE @@ v2 :> FALSE)
  /\ Fluent104_7 = (c1 :> TRUE @@ c2 :> FALSE @@ c3 :> TRUE)
  /\ bus_read_for_ownership = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_in_use = TRUE
  /\ exclusive = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ proc_write = ( c1 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> TRUE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c2 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c3 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ bus_read = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ shared = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_upgrade = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )

/\ cexTraceIdx = 4 =>
  /\ proc_read = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_transfer = (v1 :> FALSE @@ v2 :> FALSE)
  /\ Fluent104_7 = (c1 :> TRUE @@ c2 :> FALSE @@ c3 :> TRUE)
  /\ bus_read_for_ownership = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_in_use = FALSE
  /\ exclusive = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ proc_write = ( c1 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c2 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c3 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ bus_read = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ shared = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_upgrade = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )

/\ cexTraceIdx = 5 =>
  /\ proc_read = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_transfer = (v1 :> FALSE @@ v2 :> FALSE)
  /\ Fluent104_7 = (c1 :> TRUE @@ c2 :> FALSE @@ c3 :> TRUE)
  /\ bus_read_for_ownership = ( c1 :> (a1 :> TRUE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> TRUE @@ a2 :> FALSE) )
  /\ bus_in_use = TRUE
  /\ exclusive = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ proc_write = ( c1 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c2 :>
        ( a1 :> (v1 :> TRUE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c3 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ bus_read = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ shared = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_upgrade = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )

/\ cexTraceIdx = 6 =>
  /\ proc_read = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_transfer = (v1 :> TRUE @@ v2 :> FALSE)
  /\ Fluent104_7 = (c1 :> TRUE @@ c2 :> FALSE @@ c3 :> TRUE)
  /\ bus_read_for_ownership = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> TRUE @@ a2 :> FALSE) )
  /\ bus_in_use = TRUE
  /\ exclusive = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ proc_write = ( c1 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c2 :>
        ( a1 :> (v1 :> TRUE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c3 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ bus_read = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ shared = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_upgrade = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )

/\ cexTraceIdx = 7 =>
  /\ proc_read = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_transfer = (v1 :> TRUE @@ v2 :> TRUE)
  /\ Fluent104_7 = (c1 :> TRUE @@ c2 :> FALSE @@ c3 :> TRUE)
  /\ bus_read_for_ownership = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_in_use = TRUE
  /\ exclusive = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ proc_write = ( c1 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c2 :>
        ( a1 :> (v1 :> TRUE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c3 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ bus_read = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ shared = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_upgrade = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )

/\ cexTraceIdx = 8 =>
  /\ proc_read = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_transfer = (v1 :> FALSE @@ v2 :> FALSE)
  /\ Fluent104_7 = (c1 :> TRUE @@ c2 :> TRUE @@ c3 :> TRUE)
  /\ bus_read_for_ownership = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_in_use = FALSE
  /\ exclusive = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ proc_write = ( c1 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c2 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) @@
    c3 :>
        ( a1 :> (v1 :> FALSE @@ v2 :> FALSE) @@
          a2 :> (v1 :> FALSE @@ v2 :> FALSE) ) )
  /\ bus_read = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ shared = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )
  /\ bus_upgrade = ( c1 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c2 :> (a1 :> FALSE @@ a2 :> FALSE) @@
    c3 :> (a1 :> FALSE @@ a2 :> FALSE) )


CandSep == (\A var0 \in Value : (\A var1 \in Value : (\E var2 \in Core : (var1 = var0 => ~(Fluent104_7[var2])))))

Init ==
/\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
/\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
/\ proc_read = [c \in Core |-> [a \in Address |-> FALSE]]
/\ proc_write = [c \in Core |-> [a \in Address |-> [v \in Value |-> FALSE]]]
/\ bus_in_use = FALSE
/\ bus_read = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_read_for_ownership = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_upgrade = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_transfer = [v \in Value |-> FALSE]
/\ Fluent104_7 = [x0 \in Core |-> FALSE]
/\ cexTraceIdx = 0
/\ TraceConstraint

issue_proc_read_invalid(c,a) ==
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_read' = [proc_read EXCEPT![c][a] = TRUE]
/\ bus_read' = [C \in Core |-> [A \in Address |-> (bus_read[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<exclusive,shared,proc_write,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED <<Fluent104_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

do_bus_read_invalid(c,a) ==
/\ bus_read[c][a]
/\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<exclusive,shared,proc_read,proc_write,bus_in_use,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED <<Fluent104_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

do_bus_read_valid(c,a,v) ==
/\ bus_read[c][a]
/\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read_for_ownership,bus_upgrade>>
/\ UNCHANGED <<Fluent104_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

complete_proc_read_invalid_shared(c,a,v) ==
/\ proc_read[c][a]
/\ bus_transfer[v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_read[C][A])))
/\ bus_transfer' = [V \in Value |-> FALSE]
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ bus_in_use' = FALSE
/\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<exclusive,proc_write,bus_read,bus_read_for_ownership,bus_upgrade>>
/\ UNCHANGED <<Fluent104_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ proc_read[c][a]
/\ (\A V \in Value : ~(bus_transfer[V]))
/\ (\A C \in Core : (\A A \in Address : ~(bus_read[C][A])))
/\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
/\ bus_in_use' = FALSE
/\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<shared,proc_write,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED <<Fluent104_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

issue_proc_write_invalid(c,a,v) ==
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
/\ bus_read_for_ownership' = [C \in Core |-> [A \in Address |-> (bus_read_for_ownership[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<exclusive,shared,proc_read,bus_read,bus_upgrade,bus_transfer>>
/\ UNCHANGED <<Fluent104_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

do_bus_read_for_ownership_invalid(c,a) ==
/\ bus_read_for_ownership[c][a]
/\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<exclusive,shared,proc_read,proc_write,bus_in_use,bus_read,bus_upgrade,bus_transfer>>
/\ Fluent104_7' = [[x0 \in Core |-> TRUE] EXCEPT![c] = FALSE]
/\ UNCHANGED <<>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

do_bus_read_for_ownership_valid(c,a,v) ==
/\ bus_read_for_ownership[c][a]
/\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read,bus_upgrade>>
/\ UNCHANGED <<Fluent104_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

complete_proc_write_invalid(c,a,v) ==
/\ proc_write[c][a][v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_read_for_ownership[C][A])))
/\ bus_transfer' = [V \in Value |-> FALSE]
/\ bus_in_use' = FALSE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
/\ UNCHANGED <<exclusive,shared,proc_read,bus_read,bus_read_for_ownership,bus_upgrade>>
/\ Fluent104_7' = [Fluent104_7 EXCEPT![c] = TRUE]
/\ UNCHANGED <<>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

proc_write_exclusive(c,a,v) ==
/\ exclusive[c][a]
/\ ~(bus_in_use)
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<shared,proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED <<Fluent104_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

issue_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
/\ bus_upgrade' = [C \in Core |-> [A \in Address |-> (bus_upgrade[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<exclusive,shared,proc_read,bus_read,bus_read_for_ownership,bus_transfer>>
/\ UNCHANGED <<Fluent104_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

do_bus_upgrade(c,a) ==
/\ bus_upgrade[c][a]
/\ bus_upgrade' = [bus_upgrade EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<exclusive,proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_transfer>>
/\ UNCHANGED <<Fluent104_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

complete_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ proc_write[c][a][v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_upgrade[C][A])))
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
/\ bus_in_use' = FALSE
/\ UNCHANGED <<exclusive,proc_read,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED <<Fluent104_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

evict_modified(c,a) ==
/\ ~(bus_in_use)
/\ UNCHANGED <<exclusive,shared,proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED <<Fluent104_7>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

evict_exclusive_or_shared(c,a) ==
/\ ~(bus_in_use)
/\ (exclusive[c][a] \/ shared[c][a])
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED <<Fluent104_7>>
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
