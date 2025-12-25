---- MODULE C1 ----

CONSTANTS Address, Core, Value

VARIABLES exclusive, shared

vars == <<exclusive, shared>>


Init ==
    /\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ shared = [c \in Core |-> [a \in Address |-> FALSE]]

do_bus_read_valid(c, a, v) ==
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]

do_bus_read_modified(c, a, v) ==
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]

complete_proc_read_invalid_shared(c, a, v) ==
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<exclusive>>

complete_proc_read_invalid_exclusive(c, a, v) ==
    /\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<shared>>

do_bus_read_for_ownership_valid(c, a, v) ==
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]

do_bus_read_for_ownership_modified(c, a, v) ==
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]

proc_write_exclusive(c, a, v) ==
    /\ exclusive[c][a]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<shared>>

issue_proc_write_shared(c, a, v) ==
    /\ shared[c][a]
    /\ UNCHANGED<<exclusive, shared>>

complete_proc_write_shared(c, a, v) ==
    /\ shared[c][a]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<exclusive>>

evict_exclusive_or_shared(c, a) ==
    /\ exclusive[c][a] \/ shared[c][a]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]

Next ==
    \E c \in Core : \E a \in Address : \E v \in Value :
        \/ do_bus_read_valid(c,a,v)
        \/ do_bus_read_modified(c,a,v)
        \/ complete_proc_read_invalid_shared(c,a,v)
        \/ complete_proc_read_invalid_exclusive(c,a,v)
        \/ do_bus_read_for_ownership_valid(c,a,v)
        \/ do_bus_read_for_ownership_modified(c,a,v)
        \/ proc_write_exclusive(c,a,v)
        \/ issue_proc_write_shared(c,a,v)
        \/ complete_proc_write_shared(c,a,v)
        \/ evict_exclusive_or_shared(c,a)

Spec == Init /\ [][Next]_vars

Safety == \A C \in Core, A \in Address : ~(exclusive[C][A] /\ shared[C][A])

======
