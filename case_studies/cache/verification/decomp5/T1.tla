---- MODULE T1 ----

CONSTANTS Address, Core, Value

VARIABLES exclusive, shared, proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade, bus_transfer

vars == <<exclusive, shared, proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade, bus_transfer>>


Init ==
    /\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ proc_read = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ proc_write = [c \in Core |-> [a \in Address |-> [v \in Value |-> FALSE]]]
    /\ bus_in_use = FALSE
    /\ bus_read_for_ownership = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ bus_upgrade = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ bus_transfer = [v \in Value |-> FALSE]

issue_proc_read_invalid(c, a) ==
    /\ ~bus_in_use
    /\ bus_in_use' = TRUE
    /\ proc_read' = [proc_read EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<exclusive, shared, proc_write, bus_read_for_ownership, bus_upgrade, bus_transfer>>

do_bus_read_valid(c, a, v) ==
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
    /\ UNCHANGED<<proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade>>

complete_proc_read_invalid_shared(c, a, v) ==
    /\ proc_read[c][a]
    /\ bus_transfer[v]
    /\ bus_transfer' = [V \in Value |-> FALSE]
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ bus_in_use' = FALSE
    /\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<exclusive, proc_write, bus_read_for_ownership, bus_upgrade>>

complete_proc_read_invalid_exclusive(c, a, v) ==
    /\ proc_read[c][a]
    /\ \A V \in Value : ~bus_transfer[V]
    /\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
    /\ bus_in_use' = FALSE
    /\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<shared, proc_write, bus_read_for_ownership, bus_upgrade, bus_transfer>>

issue_proc_write_invalid(c, a, v) ==
    /\ ~bus_in_use
    /\ bus_in_use' = TRUE
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
    /\ bus_read_for_ownership' = [C \in Core |-> [A \in Address |-> bus_read_for_ownership[C][A] \/ (C # c /\ A = a)]]
    /\ UNCHANGED<<exclusive, shared, proc_read, bus_upgrade, bus_transfer>>

do_bus_read_for_ownership_invalid(c, a) ==
    /\ bus_read_for_ownership[c][a]
    /\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<exclusive, shared, proc_read, proc_write, bus_in_use, bus_upgrade, bus_transfer>>

do_bus_read_for_ownership_valid(c, a, v) ==
    /\ bus_read_for_ownership[c][a]
    /\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
    /\ UNCHANGED<<proc_read, proc_write, bus_in_use, bus_upgrade>>

complete_proc_write_invalid(c, a, v) ==
    /\ proc_write[c][a][v]
    /\ \A C \in Core : \A A \in Address : ~bus_read_for_ownership[C][A]
    /\ bus_transfer' = [V \in Value |-> FALSE]
    /\ bus_in_use' = FALSE
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
    /\ UNCHANGED<<exclusive, shared, proc_read, bus_read_for_ownership, bus_upgrade>>

proc_write_exclusive(c, a, v) ==
    /\ exclusive[c][a]
    /\ ~bus_in_use
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<shared, proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade, bus_transfer>>

issue_proc_write_shared(c, a, v) ==
    /\ shared[c][a]
    /\ ~bus_in_use
    /\ bus_in_use' = TRUE
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
    /\ bus_upgrade' = [C \in Core |-> [A \in Address |-> bus_upgrade[C][A] \/ (C # c /\ A = a)]]
    /\ UNCHANGED<<exclusive, shared, proc_read, bus_read_for_ownership, bus_transfer>>

do_bus_upgrade(c, a) ==
    /\ bus_upgrade[c][a]
    /\ bus_upgrade' = [bus_upgrade EXCEPT![c][a] = FALSE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<exclusive, proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_transfer>>

complete_proc_write_shared(c, a, v) ==
    /\ shared[c][a]
    /\ proc_write[c][a][v]
    /\ \A C \in Core : \A A \in Address : ~bus_upgrade[C][A]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
    /\ bus_in_use' = FALSE
    /\ UNCHANGED<<exclusive, proc_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>

evict_modified(c, a) ==
    /\ ~bus_in_use
    /\ UNCHANGED<<exclusive, shared, proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade, bus_transfer>>

evict_exclusive_or_shared(c, a) ==
    /\ ~bus_in_use
    /\ exclusive[c][a] \/ shared[c][a]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade, bus_transfer>>

Next ==
    \E c \in Core : \E a \in Address : \E v \in Value :
        \/ issue_proc_read_invalid(c,a)
        \*\/ do_bus_read_invalid(c,a)
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

Spec == Init /\ [][Next]_vars

======
