---- MODULE T2 ----

CONSTANTS Address, Core, Value

VARIABLES proc_write, bus_read_for_ownership, bus_upgrade, bus_transfer

vars == <<proc_write, bus_read_for_ownership, bus_upgrade, bus_transfer>>


Init ==
    /\ proc_write = [c \in Core |-> [a \in Address |-> [v \in Value |-> FALSE]]]
    /\ bus_read_for_ownership = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ bus_upgrade = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ bus_transfer = [v \in Value |-> FALSE]

do_bus_read_valid(c, a, v) ==
    /\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
    /\ UNCHANGED<<proc_write, bus_read_for_ownership, bus_upgrade>>

complete_proc_read_invalid_shared(c, a, v) ==
    /\ bus_transfer[v]
    /\ bus_transfer' = [V \in Value |-> FALSE]
    /\ UNCHANGED<<proc_write, bus_read_for_ownership, bus_upgrade>>

complete_proc_read_invalid_exclusive(c, a, v) ==
    /\ \A V \in Value : ~bus_transfer[V]
    /\ UNCHANGED<<proc_write, bus_read_for_ownership, bus_upgrade, bus_transfer>>

issue_proc_write_invalid(c, a, v) ==
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
    /\ bus_read_for_ownership' = [C \in Core |-> [A \in Address |-> bus_read_for_ownership[C][A] \/ (C # c /\ A = a)]]
    /\ UNCHANGED<<bus_upgrade, bus_transfer>>

do_bus_read_for_ownership_invalid(c, a) ==
    /\ bus_read_for_ownership[c][a]
    /\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<proc_write, bus_upgrade, bus_transfer>>

do_bus_read_for_ownership_valid(c, a, v) ==
    /\ bus_read_for_ownership[c][a]
    /\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
    /\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
    /\ UNCHANGED<<proc_write, bus_upgrade>>

complete_proc_write_invalid(c, a, v) ==
    /\ proc_write[c][a][v]
    /\ \A C \in Core : \A A \in Address : ~bus_read_for_ownership[C][A]
    /\ bus_transfer' = [V \in Value |-> FALSE]
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
    /\ UNCHANGED<<bus_read_for_ownership, bus_upgrade>>

issue_proc_write_shared(c, a, v) ==
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
    /\ bus_upgrade' = [C \in Core |-> [A \in Address |-> bus_upgrade[C][A] \/ (C # c /\ A = a)]]
    /\ UNCHANGED<<bus_read_for_ownership, bus_transfer>>

do_bus_upgrade(c, a) ==
    /\ bus_upgrade[c][a]
    /\ bus_upgrade' = [bus_upgrade EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<proc_write, bus_read_for_ownership, bus_transfer>>

complete_proc_write_shared(c, a, v) ==
    /\ proc_write[c][a][v]
    /\ \A C \in Core : \A A \in Address : ~bus_upgrade[C][A]
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
    /\ UNCHANGED<<bus_read_for_ownership, bus_upgrade, bus_transfer>>

Next ==
    \E c \in Core : \E a \in Address : \E v \in Value :
        \/ do_bus_read_valid(c,a,v)
        \/ complete_proc_read_invalid_shared(c,a,v)
        \/ complete_proc_read_invalid_exclusive(c,a,v)
        \/ issue_proc_write_invalid(c,a,v)
        \/ do_bus_read_for_ownership_invalid(c,a)
        \/ do_bus_read_for_ownership_valid(c,a,v)
        \/ complete_proc_write_invalid(c,a,v)
        \/ issue_proc_write_shared(c,a,v)
        \/ do_bus_upgrade(c,a)
        \/ complete_proc_write_shared(c,a,v)

Spec == Init /\ [][Next]_vars

======
