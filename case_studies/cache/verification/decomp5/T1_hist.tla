--------------------------- MODULE T1_hist ---------------------------


CONSTANTS Address, Core, Value

VARIABLES shared, Fluent49_23, bus_transfer, Fluent2_26, Fluent28_0, proc_write, Fluent27_0, Fluent24_6, bus_read_for_ownership, Fluent23_6, exclusive, Fluent48_23, Fluent43_17, Fluent53_0, Fluent52_0, Fluent3_26, bus_in_use, Fluent10_2, Fluent55_6, Fluent38_4, Fluent34_8, proc_read, Fluent39_4, Fluent56_6, Fluent33_8, Fluent6_6, Fluent5_6, Fluent9_2, bus_upgrade, Fluent44_17

vars == <<shared, Fluent49_23, bus_transfer, Fluent2_26, Fluent28_0, proc_write, Fluent27_0, Fluent24_6, bus_read_for_ownership, Fluent23_6, exclusive, Fluent48_23, Fluent43_17, Fluent53_0, Fluent52_0, Fluent3_26, bus_in_use, Fluent10_2, Fluent55_6, Fluent38_4, Fluent34_8, proc_read, Fluent39_4, Fluent56_6, Fluent33_8, Fluent6_6, Fluent5_6, Fluent9_2, bus_upgrade, Fluent44_17>>

CandSep ==
/\ \A var0 \in Core : (Fluent27_0[var0]) => (Fluent28_0[var0])
/\ \A var0 \in Core : (Fluent3_26[var0]) => (Fluent2_26[var0])
/\ \A var0 \in Core : (Fluent6_6[var0]) => (Fluent5_6[var0])
/\ \A var0 \in Core : (Fluent49_23[var0]) => (Fluent48_23[var0])
/\ \A var0 \in Value : (Fluent9_2[var0]) => (Fluent10_2[var0])
/\ \A var0 \in Core : (Fluent23_6[var0]) => (Fluent24_6[var0])
/\ \A var0 \in Address : (Fluent38_4[var0]) => (Fluent39_4[var0])
/\ \A var0 \in Core : (Fluent55_6[var0]) => (Fluent56_6[var0])
/\ \A var0 \in Value : (Fluent33_8[var0]) => (Fluent34_8[var0])
/\ \A var0 \in Core : (Fluent43_17[var0]) => (Fluent44_17[var0])
/\ \A var0 \in Core : (Fluent52_0[var0]) => (Fluent53_0[var0])

Init ==
/\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
/\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
/\ proc_read = [c \in Core |-> [a \in Address |-> FALSE]]
/\ proc_write = [c \in Core |-> [a \in Address |-> [v \in Value |-> FALSE]]]
/\ bus_in_use = FALSE
/\ bus_read_for_ownership = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_upgrade = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_transfer = [v \in Value |-> FALSE]
/\ Fluent49_23 = [ x0 \in Core |-> FALSE]
/\ Fluent53_0 = [ x0 \in Core |-> FALSE]
/\ Fluent52_0 = [ x0 \in Core |-> FALSE]
/\ Fluent3_26 = [ x0 \in Core |-> FALSE]
/\ Fluent2_26 = [ x0 \in Core |-> FALSE]
/\ Fluent10_2 = [ x0 \in Value |-> FALSE]
/\ Fluent55_6 = [ x0 \in Core |-> FALSE]
/\ Fluent28_0 = [ x0 \in Core |-> FALSE]
/\ Fluent27_0 = [ x0 \in Core |-> FALSE]
/\ Fluent24_6 = [ x0 \in Core |-> FALSE]
/\ Fluent38_4 = [ x0 \in Address |-> FALSE]
/\ Fluent34_8 = [ x0 \in Value |-> FALSE]
/\ Fluent23_6 = [ x0 \in Core |-> FALSE]
/\ Fluent39_4 = [ x0 \in Address |-> FALSE]
/\ Fluent56_6 = [ x0 \in Core |-> FALSE]
/\ Fluent33_8 = [ x0 \in Value |-> FALSE]
/\ Fluent48_23 = [ x0 \in Core |-> FALSE]
/\ Fluent6_6 = [ x0 \in Core |-> FALSE]
/\ Fluent5_6 = [ x0 \in Core |-> FALSE]
/\ Fluent9_2 = [ x0 \in Value |-> FALSE]
/\ Fluent43_17 = [ x0 \in Core |-> FALSE]
/\ Fluent44_17 = [ x0 \in Core |-> FALSE]

issue_proc_read_invalid(c,a) ==
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_read' = [proc_read EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<exclusive,shared,proc_write,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ Fluent2_26' = [Fluent2_26 EXCEPT ![c] = TRUE]
/\ Fluent24_6' = [Fluent24_6 EXCEPT ![c] = TRUE]
/\ Fluent34_8' = [x0 \in Value |-> FALSE]
/\ Fluent5_6' = [Fluent5_6 EXCEPT ![c] = TRUE]
/\ Fluent44_17' = [Fluent44_17 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent3_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent27_0, Fluent38_4, Fluent23_6, Fluent39_4, Fluent56_6, Fluent33_8, Fluent48_23, Fluent6_6, Fluent9_2, Fluent43_17>>

do_bus_read_valid(c,a,v) ==
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read_for_ownership,bus_upgrade>>
/\ Fluent10_2' = [Fluent10_2 EXCEPT ![v] = TRUE]
/\ Fluent28_0' = [x0 \in Core |-> TRUE]
/\ Fluent39_4' = [x0 \in Address |-> TRUE]
/\ Fluent44_17' = [Fluent44_17 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent3_26, Fluent2_26, Fluent55_6, Fluent27_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent23_6, Fluent56_6, Fluent33_8, Fluent48_23, Fluent6_6, Fluent5_6, Fluent9_2, Fluent43_17>>

complete_proc_read_invalid_shared(c,a,v) ==
/\ proc_read[c][a]
/\ bus_transfer[v]
/\ bus_transfer' = [V \in Value |-> FALSE]
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ bus_in_use' = FALSE
/\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<exclusive,proc_write,bus_read_for_ownership,bus_upgrade>>
/\ Fluent3_26' = [Fluent3_26 EXCEPT ![c] = TRUE]
/\ Fluent9_2' = [Fluent9_2 EXCEPT ![v] = TRUE]
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent2_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent27_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent23_6, Fluent39_4, Fluent56_6, Fluent33_8, Fluent48_23, Fluent6_6, Fluent5_6, Fluent43_17, Fluent44_17>>

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ proc_read[c][a]
/\ (\A V \in Value : ~(bus_transfer[V]))
/\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
/\ bus_in_use' = FALSE
/\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<shared,proc_write,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ Fluent56_6' = [Fluent56_6 EXCEPT ![c] = TRUE]
/\ Fluent6_6' = [Fluent6_6 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent3_26, Fluent2_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent27_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent23_6, Fluent39_4, Fluent33_8, Fluent48_23, Fluent5_6, Fluent9_2, Fluent43_17, Fluent44_17>>

issue_proc_write_invalid(c,a,v) ==
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
/\ bus_read_for_ownership' = [C \in Core |-> [A \in Address |-> (bus_read_for_ownership[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<exclusive,shared,proc_read,bus_upgrade,bus_transfer>>
/\ Fluent53_0' = [x0 \in Core |-> TRUE]
/\ Fluent34_8' = [Fluent34_8 EXCEPT ![v] = TRUE]
/\ Fluent39_4' = [Fluent39_4 EXCEPT ![a] = TRUE]
/\ Fluent33_8' = [Fluent33_8 EXCEPT ![v] = TRUE]
/\ Fluent48_23' = [Fluent48_23 EXCEPT ![c] = TRUE]
/\ Fluent44_17' = [Fluent44_17 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent49_23, Fluent52_0, Fluent3_26, Fluent2_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent27_0, Fluent24_6, Fluent38_4, Fluent23_6, Fluent56_6, Fluent6_6, Fluent5_6, Fluent9_2, Fluent43_17>>

do_bus_read_for_ownership_invalid(c,a) ==
/\ bus_read_for_ownership[c][a]
/\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<exclusive,shared,proc_read,proc_write,bus_in_use,bus_upgrade,bus_transfer>>
/\ Fluent48_23' = [Fluent48_23 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent3_26, Fluent2_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent27_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent23_6, Fluent39_4, Fluent56_6, Fluent33_8, Fluent6_6, Fluent5_6, Fluent9_2, Fluent43_17, Fluent44_17>>

do_bus_read_for_ownership_valid(c,a,v) ==
/\ bus_read_for_ownership[c][a]
/\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_upgrade>>
/\ Fluent52_0' = [Fluent52_0 EXCEPT ![c] = TRUE]
/\ Fluent10_2' = [Fluent10_2 EXCEPT ![v] = TRUE]
/\ Fluent48_23' = [Fluent48_23 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent3_26, Fluent2_26, Fluent55_6, Fluent28_0, Fluent27_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent23_6, Fluent39_4, Fluent56_6, Fluent33_8, Fluent6_6, Fluent5_6, Fluent9_2, Fluent43_17, Fluent44_17>>

complete_proc_write_invalid(c,a,v) ==
/\ proc_write[c][a][v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_read_for_ownership[C][A])))
/\ bus_transfer' = [V \in Value |-> FALSE]
/\ bus_in_use' = FALSE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
/\ UNCHANGED <<exclusive,shared,proc_read,bus_read_for_ownership,bus_upgrade>>
/\ Fluent49_23' = [x0 \in Core |-> Fluent48_23[c]]
/\ Fluent38_4' = [Fluent38_4 EXCEPT ![a] = TRUE]
/\ Fluent33_8' = [Fluent33_8 EXCEPT ![v] = FALSE]
/\ Fluent43_17' = [Fluent43_17 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent53_0, Fluent52_0, Fluent3_26, Fluent2_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent27_0, Fluent24_6, Fluent34_8, Fluent23_6, Fluent39_4, Fluent56_6, Fluent48_23, Fluent6_6, Fluent5_6, Fluent9_2, Fluent44_17>>

proc_write_exclusive(c,a,v) ==
/\ exclusive[c][a]
/\ ~(bus_in_use)
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<shared,proc_read,proc_write,bus_in_use,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ Fluent55_6' = [Fluent55_6 EXCEPT ![c] = TRUE]
/\ Fluent23_6' = [Fluent23_6 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent3_26, Fluent2_26, Fluent10_2, Fluent28_0, Fluent27_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent39_4, Fluent56_6, Fluent33_8, Fluent48_23, Fluent6_6, Fluent5_6, Fluent9_2, Fluent43_17, Fluent44_17>>

issue_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
/\ bus_upgrade' = [C \in Core |-> [A \in Address |-> (bus_upgrade[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<exclusive,shared,proc_read,bus_read_for_ownership,bus_transfer>>
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent3_26, Fluent2_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent27_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent23_6, Fluent39_4, Fluent56_6, Fluent33_8, Fluent48_23, Fluent6_6, Fluent5_6, Fluent9_2, Fluent43_17, Fluent44_17>>

do_bus_upgrade(c,a) ==
/\ bus_upgrade[c][a]
/\ bus_upgrade' = [bus_upgrade EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<exclusive,proc_read,proc_write,bus_in_use,bus_read_for_ownership,bus_transfer>>
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent3_26, Fluent2_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent27_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent23_6, Fluent39_4, Fluent56_6, Fluent33_8, Fluent48_23, Fluent6_6, Fluent5_6, Fluent9_2, Fluent43_17, Fluent44_17>>

complete_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ proc_write[c][a][v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_upgrade[C][A])))
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
/\ bus_in_use' = FALSE
/\ UNCHANGED <<exclusive,proc_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ Fluent27_0' = [Fluent27_0 EXCEPT ![c] = TRUE]
/\ Fluent33_8' = [Fluent33_8 EXCEPT ![v] = FALSE]
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent3_26, Fluent2_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent23_6, Fluent39_4, Fluent56_6, Fluent48_23, Fluent6_6, Fluent5_6, Fluent9_2, Fluent43_17, Fluent44_17>>

evict_modified(c,a) ==
/\ ~(bus_in_use)
/\ UNCHANGED <<exclusive,shared,proc_read,proc_write,bus_in_use,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent3_26, Fluent2_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent27_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent23_6, Fluent39_4, Fluent56_6, Fluent33_8, Fluent48_23, Fluent6_6, Fluent5_6, Fluent9_2, Fluent43_17, Fluent44_17>>

evict_exclusive_or_shared(c,a) ==
/\ ~(bus_in_use)
/\ (exclusive[c][a] \/ shared[c][a])
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent3_26, Fluent2_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent27_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent23_6, Fluent39_4, Fluent56_6, Fluent33_8, Fluent48_23, Fluent6_6, Fluent5_6, Fluent9_2, Fluent43_17, Fluent44_17>>

Next ==
\E c \in Core :
\E a \in Address :
\E v \in Value :
\/ issue_proc_read_invalid(c,a)
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
