--------------------------- MODULE T1_hist ---------------------------


CONSTANTS Address, Core, Value

VARIABLES Fluent169_3, proc_write, proc_read, bus_read_for_ownership, Fluent168_3, bus_transfer, bus_read, bus_upgrade, bus_in_use

vars == <<Fluent169_3, proc_write, proc_read, bus_read_for_ownership, Fluent168_3, bus_transfer, bus_read, bus_upgrade, bus_in_use>>

CandSep ==
\A var0 \in Address : (Fluent169_3[var0]) => (Fluent168_3[var0])

Init ==
/\ proc_read = [c \in Core |-> [a \in Address |-> FALSE]]
/\ proc_write = [c \in Core |-> [a \in Address |-> [v \in Value |-> FALSE]]]
/\ bus_in_use = FALSE
/\ bus_read = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_read_for_ownership = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_upgrade = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_transfer = [v \in Value |-> FALSE]
/\ Fluent169_3 = [ x0 \in Address |-> FALSE]
/\ Fluent168_3 = [ x0 \in Address |-> FALSE]

issue_proc_read_invalid(c,a) ==
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_read' = [proc_read EXCEPT![c][a] = TRUE]
/\ bus_read' = [C \in Core |-> [A \in Address |-> (bus_read[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<proc_write,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent169_3, Fluent168_3>>

do_bus_read_invalid(c,a) ==
/\ bus_read[c][a]
/\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent169_3, Fluent168_3>>

do_bus_read_valid(c,a,v) ==
/\ bus_read[c][a]
/\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
/\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read_for_ownership,bus_upgrade>>
/\ Fluent168_3' = [Fluent168_3 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent169_3>>

complete_proc_read_invalid_shared(c,a,v) ==
/\ proc_read[c][a]
/\ bus_transfer[v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_read[C][A])))
/\ bus_transfer' = [V \in Value |-> FALSE]
/\ bus_in_use' = FALSE
/\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<proc_write,bus_read,bus_read_for_ownership,bus_upgrade>>
/\ Fluent169_3' = [Fluent169_3 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent168_3>>

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ proc_read[c][a]
/\ (\A V \in Value : ~(bus_transfer[V]))
/\ (\A C \in Core : (\A A \in Address : ~(bus_read[C][A])))
/\ bus_in_use' = FALSE
/\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<proc_write,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent169_3, Fluent168_3>>

issue_proc_write_invalid(c,a,v) ==
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
/\ bus_read_for_ownership' = [C \in Core |-> [A \in Address |-> (bus_read_for_ownership[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<proc_read,bus_read,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent169_3, Fluent168_3>>

do_bus_read_for_ownership_invalid(c,a) ==
/\ bus_read_for_ownership[c][a]
/\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent169_3, Fluent168_3>>

do_bus_read_for_ownership_valid(c,a,v) ==
/\ bus_read_for_ownership[c][a]
/\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
/\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read,bus_upgrade>>
/\ UNCHANGED<<Fluent169_3, Fluent168_3>>

complete_proc_write_invalid(c,a,v) ==
/\ proc_write[c][a][v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_read_for_ownership[C][A])))
/\ bus_transfer' = [V \in Value |-> FALSE]
/\ bus_in_use' = FALSE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
/\ UNCHANGED <<proc_read,bus_read,bus_read_for_ownership,bus_upgrade>>
/\ UNCHANGED<<Fluent169_3, Fluent168_3>>

proc_write_exclusive(c,a,v) ==
/\ ~(bus_in_use)
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent169_3, Fluent168_3>>

issue_proc_write_shared(c,a,v) ==
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
/\ bus_upgrade' = [C \in Core |-> [A \in Address |-> (bus_upgrade[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<proc_read,bus_read,bus_read_for_ownership,bus_transfer>>
/\ UNCHANGED<<Fluent169_3, Fluent168_3>>

do_bus_upgrade(c,a) ==
/\ bus_upgrade[c][a]
/\ bus_upgrade' = [bus_upgrade EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_transfer>>
/\ UNCHANGED<<Fluent169_3, Fluent168_3>>

complete_proc_write_shared(c,a,v) ==
/\ proc_write[c][a][v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_upgrade[C][A])))
/\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
/\ bus_in_use' = FALSE
/\ UNCHANGED <<proc_read,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ Fluent168_3' = [x0 \in Address |-> TRUE]
/\ UNCHANGED<<Fluent169_3>>

evict_modified(c,a) ==
/\ ~(bus_in_use)
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent169_3, Fluent168_3>>

evict_exclusive_or_shared(c,a) ==
/\ ~(bus_in_use)
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent169_3, Fluent168_3>>

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
