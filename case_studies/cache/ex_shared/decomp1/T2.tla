---- MODULE T2 ----

CONSTANTS Address, Core, Value

VARIABLES bus_read_for_ownership

vars == <<bus_read_for_ownership>>


Init ==
    /\ bus_read_for_ownership = [c \in Core |-> [a \in Address |-> FALSE]]

issue_proc_write_invalid(c, a, v) ==
    /\ bus_read_for_ownership' = [C \in Core |-> [A \in Address |-> bus_read_for_ownership[C][A] \/ (C # c /\ A = a)]]

do_bus_read_for_ownership_invalid(c, a) ==
    /\ bus_read_for_ownership[c][a]
    /\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]

do_bus_read_for_ownership_valid(c, a, v) ==
    /\ bus_read_for_ownership[c][a]
    /\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]

complete_proc_write_invalid(c, a, v) ==
    /\ \A C \in Core : \A A \in Address : ~bus_read_for_ownership[C][A]
    /\ UNCHANGED<<bus_read_for_ownership>>

Next ==
    \E c \in Core : \E a \in Address : \E v \in Value :
        \/ issue_proc_write_invalid(c,a,v)
        \/ do_bus_read_for_ownership_invalid(c,a)
        \/ do_bus_read_for_ownership_valid(c,a,v)
        \/ complete_proc_write_invalid(c,a,v)

Spec == Init /\ [][Next]_vars

======
