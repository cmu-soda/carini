---- MODULE T1 ----

CONSTANTS Address, Core, Value

VARIABLES invalid, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer

vars == <<invalid, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>


Init ==
    /\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]
    /\ proc_read = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ proc_write = [c \in Core |-> [a \in Address |-> [v \in Value |-> FALSE]]]
    /\ bus_in_use = FALSE
    /\ bus_read = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ bus_read_for_ownership = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ bus_upgrade = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ bus_transfer = [v \in Value |-> FALSE]

issue_proc_read_invalid(c, a) ==
    /\ invalid[c][a]
    /\ ~bus_in_use
    /\ bus_in_use' = TRUE
    /\ proc_read' = [proc_read EXCEPT![c][a] = TRUE]
    /\ bus_read' = [C \in Core |-> [A \in Address |-> bus_read[C][A] \/ (C # c /\ A = a)]]
    /\ UNCHANGED<<invalid, proc_write, bus_read_for_ownership, bus_upgrade, bus_transfer>>

do_bus_read_invalid(c, a) ==
    /\ invalid[c][a]
    /\ bus_read[c][a]
    /\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<invalid, proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade, bus_transfer>>

do_bus_read_valid(c, a, v) ==
    /\ ~invalid[c][a]
    /\ bus_read[c][a]
    /\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
    /\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
    /\ UNCHANGED<<invalid, proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade>>

complete_proc_read_invalid_shared(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ proc_read[c][a]
    /\ bus_transfer[v]
    /\ \A C \in Core : \A A \in Address : ~bus_read[C][A]
    /\ bus_transfer' = [V \in Value |-> FALSE]
    /\ bus_in_use' = FALSE
    /\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<proc_write, bus_read, bus_read_for_ownership, bus_upgrade>>

complete_proc_read_invalid_exclusive(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ proc_read[c][a]
    /\ \A V \in Value : ~bus_transfer[V]
    /\ \A C \in Core : \A A \in Address : ~bus_read[C][A]
    /\ bus_in_use' = FALSE
    /\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<proc_write, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>

issue_proc_write_invalid(c, a, v) ==
    /\ invalid[c][a]
    /\ ~bus_in_use
    /\ bus_in_use' = TRUE
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
    /\ bus_read_for_ownership' = [C \in Core |-> [A \in Address |-> bus_read_for_ownership[C][A] \/ (C # c /\ A = a)]]
    /\ UNCHANGED<<invalid, proc_read, bus_read, bus_upgrade, bus_transfer>>

do_bus_read_for_ownership_invalid(c, a) ==
    /\ invalid[c][a]
    /\ bus_read_for_ownership[c][a]
    /\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<invalid, proc_read, proc_write, bus_in_use, bus_read, bus_upgrade, bus_transfer>>

do_bus_read_for_ownership_valid(c, a, v) ==
    /\ ~invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ bus_read_for_ownership[c][a]
    /\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
    /\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
    /\ UNCHANGED<<proc_read, proc_write, bus_in_use, bus_read, bus_upgrade>>

complete_proc_write_invalid(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ proc_write[c][a][v]
    /\ \A C \in Core : \A A \in Address : ~bus_read_for_ownership[C][A]
    /\ bus_transfer' = [V \in Value |-> FALSE]
    /\ bus_in_use' = FALSE
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
    /\ UNCHANGED<<proc_read, bus_read, bus_read_for_ownership, bus_upgrade>>

proc_write_exclusive(c, a, v) ==
    /\ ~bus_in_use
    /\ UNCHANGED<<invalid, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>

issue_proc_write_shared(c, a, v) ==
    /\ ~bus_in_use
    /\ bus_in_use' = TRUE
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
    /\ bus_upgrade' = [C \in Core |-> [A \in Address |-> bus_upgrade[C][A] \/ (C # c /\ A = a)]]
    /\ UNCHANGED<<invalid, proc_read, bus_read, bus_read_for_ownership, bus_transfer>>

do_bus_upgrade(c, a) ==
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ bus_upgrade[c][a]
    /\ bus_upgrade' = [bus_upgrade EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_transfer>>

complete_proc_write_shared(c, a, v) ==
    /\ proc_write[c][a][v]
    /\ \A C \in Core : \A A \in Address : ~bus_upgrade[C][A]
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
    /\ bus_in_use' = FALSE
    /\ UNCHANGED<<invalid, proc_read, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>

evict_modified(c, a) ==
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ ~bus_in_use
    /\ UNCHANGED<<proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>

evict_exclusive_or_shared(c, a) ==
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ ~bus_in_use
    /\ UNCHANGED<<proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>

Next ==
    \E c \in Core : \E a \in Address : \E v \in Value :
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

Spec == Init /\ [][Next]_vars

======
