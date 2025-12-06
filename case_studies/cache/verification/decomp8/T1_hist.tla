--------------------------- MODULE T1_hist ---------------------------


CONSTANTS Address, Core, Value

VARIABLES bus_read_for_ownership, bus_transfer, bus_read, Fluent13_22, Fluent14_22, bus_upgrade

vars == <<bus_read_for_ownership, bus_transfer, bus_read, Fluent13_22, Fluent14_22, bus_upgrade>>

CandSep ==
\A var0 \in Address : (Fluent14_22[var0]) => (~(Fluent13_22[var0]))

Init ==
/\ bus_read = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_read_for_ownership = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_upgrade = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_transfer = [v \in Value |-> FALSE]
/\ Fluent13_22 = [ x0 \in Address |-> FALSE]
/\ Fluent14_22 = [ x0 \in Address |-> FALSE]

issue_proc_read_invalid(c,a) ==
/\ bus_read' = [C \in Core |-> [A \in Address |-> (bus_read[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent13_22, Fluent14_22>>

do_bus_read_invalid(c,a) ==
/\ bus_read[c][a]
/\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent13_22, Fluent14_22>>

do_bus_read_valid(c,a,v) ==
/\ bus_read[c][a]
/\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
/\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
/\ UNCHANGED <<bus_read_for_ownership,bus_upgrade>>
/\ UNCHANGED<<Fluent13_22, Fluent14_22>>

complete_proc_read_invalid_shared(c,a,v) ==
/\ bus_transfer[v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_read[C][A])))
/\ bus_transfer' = [V \in Value |-> FALSE]
/\ UNCHANGED <<bus_read,bus_read_for_ownership,bus_upgrade>>
/\ UNCHANGED<<Fluent13_22, Fluent14_22>>

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ (\A V \in Value : ~(bus_transfer[V]))
/\ (\A C \in Core : (\A A \in Address : ~(bus_read[C][A])))
/\ UNCHANGED <<bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent13_22, Fluent14_22>>

issue_proc_write_invalid(c,a,v) ==
/\ bus_read_for_ownership' = [C \in Core |-> [A \in Address |-> (bus_read_for_ownership[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<bus_read,bus_upgrade,bus_transfer>>
/\ Fluent13_22' = [Fluent13_22 EXCEPT ![a] = FALSE]
/\ Fluent14_22' = [Fluent14_22 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<>>

do_bus_read_for_ownership_invalid(c,a) ==
/\ bus_read_for_ownership[c][a]
/\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<bus_read,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent13_22, Fluent14_22>>

do_bus_read_for_ownership_valid(c,a,v) ==
/\ bus_read_for_ownership[c][a]
/\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
/\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
/\ UNCHANGED <<bus_read,bus_upgrade>>
/\ UNCHANGED<<Fluent13_22, Fluent14_22>>

complete_proc_write_invalid(c,a,v) ==
/\ (\A C \in Core : (\A A \in Address : ~(bus_read_for_ownership[C][A])))
/\ bus_transfer' = [V \in Value |-> FALSE]
/\ UNCHANGED <<bus_read,bus_read_for_ownership,bus_upgrade>>
/\ Fluent13_22' = [Fluent13_22 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent14_22>>

issue_proc_write_shared(c,a,v) ==
/\ bus_upgrade' = [C \in Core |-> [A \in Address |-> (bus_upgrade[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<bus_read,bus_read_for_ownership,bus_transfer>>
/\ UNCHANGED<<Fluent13_22, Fluent14_22>>

do_bus_upgrade(c,a) ==
/\ bus_upgrade[c][a]
/\ bus_upgrade' = [bus_upgrade EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<bus_read,bus_read_for_ownership,bus_transfer>>
/\ UNCHANGED<<Fluent13_22, Fluent14_22>>

complete_proc_write_shared(c,a,v) ==
/\ (\A C \in Core : (\A A \in Address : ~(bus_upgrade[C][A])))
/\ UNCHANGED <<bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent13_22, Fluent14_22>>

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
\/ issue_proc_write_shared(c,a,v)
\/ do_bus_upgrade(c,a)
\/ complete_proc_write_shared(c,a,v)

Spec == (Init /\ [][Next]_vars)
=============================================================================
