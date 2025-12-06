--------------------------- MODULE T1_hist ---------------------------


CONSTANTS Address, Core, Value

VARIABLES Fluent41_6, Fluent42_6, bus_read_for_ownership, bus_transfer, bus_read, bus_upgrade, bus_in_use

vars == <<Fluent41_6, Fluent42_6, bus_read_for_ownership, bus_transfer, bus_read, bus_upgrade, bus_in_use>>

CandSep ==
\A var0 \in Core : \E var1 \in Address : (Fluent41_6[var0]) => (~(Fluent42_6[var0][var1]))

Init ==
/\ bus_in_use = FALSE
/\ bus_read = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_read_for_ownership = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_upgrade = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_transfer = [v \in Value |-> FALSE]
/\ Fluent41_6 = [ x0 \in Core |-> FALSE]
/\ Fluent42_6 = [ x0 \in Core |-> [ x1 \in Address |-> FALSE]]

issue_proc_read_invalid(c,a) ==
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ bus_read' = [C \in Core |-> [A \in Address |-> (bus_read[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ Fluent42_6' = [Fluent42_6 EXCEPT ![c][a] = TRUE]
/\ UNCHANGED<<Fluent41_6>>

do_bus_read_invalid(c,a) ==
/\ bus_read[c][a]
/\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<bus_in_use,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent41_6, Fluent42_6>>

do_bus_read_valid(c,a,v) ==
/\ bus_read[c][a]
/\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
/\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
/\ UNCHANGED <<bus_in_use,bus_read_for_ownership,bus_upgrade>>
/\ UNCHANGED<<Fluent41_6, Fluent42_6>>

complete_proc_read_invalid_shared(c,a,v) ==
/\ bus_transfer[v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_read[C][A])))
/\ bus_transfer' = [V \in Value |-> FALSE]
/\ bus_in_use' = FALSE
/\ UNCHANGED <<bus_read,bus_read_for_ownership,bus_upgrade>>
/\ UNCHANGED<<Fluent41_6, Fluent42_6>>

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ (\A V \in Value : ~(bus_transfer[V]))
/\ (\A C \in Core : (\A A \in Address : ~(bus_read[C][A])))
/\ bus_in_use' = FALSE
/\ UNCHANGED <<bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent41_6, Fluent42_6>>

issue_proc_write_invalid(c,a,v) ==
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ bus_read_for_ownership' = [C \in Core |-> [A \in Address |-> (bus_read_for_ownership[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<bus_read,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent41_6, Fluent42_6>>

do_bus_read_for_ownership_invalid(c,a) ==
/\ bus_read_for_ownership[c][a]
/\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<bus_in_use,bus_read,bus_upgrade,bus_transfer>>
/\ Fluent41_6' = [Fluent41_6 EXCEPT ![c] = TRUE]
/\ Fluent42_6' = [Fluent42_6 EXCEPT ![c][a] = TRUE]
/\ UNCHANGED<<>>

do_bus_read_for_ownership_valid(c,a,v) ==
/\ bus_read_for_ownership[c][a]
/\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
/\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
/\ UNCHANGED <<bus_in_use,bus_read,bus_upgrade>>
/\ UNCHANGED<<Fluent41_6, Fluent42_6>>

complete_proc_write_invalid(c,a,v) ==
/\ (\A C \in Core : (\A A \in Address : ~(bus_read_for_ownership[C][A])))
/\ bus_transfer' = [V \in Value |-> FALSE]
/\ bus_in_use' = FALSE
/\ UNCHANGED <<bus_read,bus_read_for_ownership,bus_upgrade>>
/\ UNCHANGED<<Fluent41_6, Fluent42_6>>

proc_write_exclusive(c,a,v) ==
/\ ~(bus_in_use)
/\ UNCHANGED <<bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent41_6, Fluent42_6>>

issue_proc_write_shared(c,a,v) ==
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ bus_upgrade' = [C \in Core |-> [A \in Address |-> (bus_upgrade[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<bus_read,bus_read_for_ownership,bus_transfer>>
/\ UNCHANGED<<Fluent41_6, Fluent42_6>>

do_bus_upgrade(c,a) ==
/\ bus_upgrade[c][a]
/\ bus_upgrade' = [bus_upgrade EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<bus_in_use,bus_read,bus_read_for_ownership,bus_transfer>>
/\ UNCHANGED<<Fluent41_6, Fluent42_6>>

complete_proc_write_shared(c,a,v) ==
/\ (\A C \in Core : (\A A \in Address : ~(bus_upgrade[C][A])))
/\ bus_in_use' = FALSE
/\ UNCHANGED <<bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent41_6, Fluent42_6>>

evict_modified(c,a) ==
/\ ~(bus_in_use)
/\ UNCHANGED <<bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent41_6, Fluent42_6>>

evict_exclusive_or_shared(c,a) ==
/\ ~(bus_in_use)
/\ UNCHANGED <<bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent41_6, Fluent42_6>>

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
