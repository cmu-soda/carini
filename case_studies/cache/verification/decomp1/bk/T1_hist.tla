--------------------------- MODULE T1_hist ---------------------------


CONSTANTS Address, Core, Value

VARIABLES shared, Fluent80_2, bus_transfer, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, proc_write, bus_read_for_ownership, Fluent46_5, Fluent47_5, exclusive, Fluent64_14, Fluent76_16, bus_read, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, bus_in_use, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, proc_read, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9, bus_upgrade

vars == <<shared, Fluent80_2, bus_transfer, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, proc_write, bus_read_for_ownership, Fluent46_5, Fluent47_5, exclusive, Fluent64_14, Fluent76_16, bus_read, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, bus_in_use, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, proc_read, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9, bus_upgrade>>

CandSep ==
/\ \A var0 \in Value : (Fluent105_10[var0]) => (~(Fluent106_10[var0]))
/\ \A var0 \in Address : (Fluent49_1[var0]) => (Fluent48_1[var0])
/\ \A var0 \in Value : \E var1 \in Core : (Fluent46_5[var1][var0]) => (Fluent47_5[var1])
/\ \A var0 \in Address : (Fluent94_18[var0]) => (Fluent95_18[var0])
/\ \A var0 \in Value : (Fluent81_2[var0]) => (Fluent80_2[var0])
/\ \A var0 \in Core : (Fluent77_16[var0]) => (Fluent76_16[var0])
/\ \A var0 \in Core : (Fluent5_17[var0]) => (Fluent6_17[var0])
/\ \A var0 \in Address : (Fluent68_14[var0]) => (Fluent69_14[var0])
/\ \A var0 \in Core : (Fluent18_0[var0]) => (Fluent19_0[var0])
/\ \A var0 \in Address : (Fluent16_9[var0]) => (Fluent15_9[var0])
/\ \A var0 \in Core : (Fluent38_0[var0]) => (Fluent39_0[var0])
/\ \A var0 \in Address : (Fluent93_4[var0]) => (Fluent92_4[var0])
/\ \A var0 \in Core : (Fluent26_0[var0]) => (~(Fluent25_0[var0]))
/\ \A var0 \in Address : (Fluent64_14[var0]) => (Fluent63_14[var0])
/\ \A var0 \in Core : (Fluent74_0[var0]) => (Fluent73_0[var0])

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
/\ Fluent80_2 = [ x0 \in Value |-> FALSE]
/\ Fluent105_10 = [ x0 \in Value |-> FALSE]
/\ Fluent77_16 = [ x0 \in Core |-> FALSE]
/\ Fluent81_2 = [ x0 \in Value |-> FALSE]
/\ Fluent5_17 = [ x0 \in Core |-> FALSE]
/\ Fluent48_1 = [ x0 \in Address |-> FALSE]
/\ Fluent95_18 = [ x0 \in Address |-> FALSE]
/\ Fluent26_0 = [ x0 \in Core |-> FALSE]
/\ Fluent49_1 = [ x0 \in Address |-> FALSE]
/\ Fluent68_14 = [ x0 \in Address |-> FALSE]
/\ Fluent25_0 = [ x0 \in Core |-> FALSE]
/\ Fluent46_5 = [ x0 \in Core |-> [ x1 \in Value |-> FALSE]]
/\ Fluent47_5 = [ x0 \in Core |-> FALSE]
/\ Fluent64_14 = [ x0 \in Address |-> FALSE]
/\ Fluent76_16 = [ x0 \in Core |-> FALSE]
/\ Fluent106_10 = [ x0 \in Value |-> FALSE]
/\ Fluent73_0 = [ x0 \in Core |-> FALSE]
/\ Fluent93_4 = [ x0 \in Address |-> FALSE]
/\ Fluent74_0 = [ x0 \in Core |-> FALSE]
/\ Fluent6_17 = [ x0 \in Core |-> FALSE]
/\ Fluent92_4 = [ x0 \in Address |-> FALSE]
/\ Fluent38_0 = [ x0 \in Core |-> FALSE]
/\ Fluent39_0 = [ x0 \in Core |-> FALSE]
/\ Fluent94_18 = [ x0 \in Address |-> FALSE]
/\ Fluent19_0 = [ x0 \in Core |-> FALSE]
/\ Fluent18_0 = [ x0 \in Core |-> FALSE]
/\ Fluent69_14 = [ x0 \in Address |-> FALSE]
/\ Fluent16_9 = [ x0 \in Address |-> FALSE]
/\ Fluent63_14 = [ x0 \in Address |-> FALSE]
/\ Fluent15_9 = [ x0 \in Address |-> FALSE]

issue_proc_read_invalid(c,a) ==
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_read' = [proc_read EXCEPT![c][a] = TRUE]
/\ bus_read' = [C \in Core |-> [A \in Address |-> (bus_read[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<exclusive,shared,proc_write,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ Fluent48_1' = [Fluent48_1 EXCEPT ![a] = TRUE]
/\ Fluent95_18' = [Fluent95_18 EXCEPT ![a] = TRUE]
/\ Fluent25_0' = [x0 \in Core |-> TRUE]
/\ Fluent46_5' = [x0 \in Core |-> [x1 \in Value |-> TRUE]]
/\ Fluent47_5' = [Fluent47_5 EXCEPT ![c] = TRUE]
/\ Fluent92_4' = [Fluent92_4 EXCEPT ![a] = TRUE]
/\ Fluent69_14' = [Fluent69_14 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent26_0, Fluent49_1, Fluent68_14, Fluent64_14, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, Fluent6_17, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent16_9, Fluent63_14, Fluent15_9>>

do_bus_read_invalid(c,a) ==
/\ bus_read[c][a]
/\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<exclusive,shared,proc_read,proc_write,bus_in_use,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ Fluent105_10' = [x0 \in Value |-> FALSE]
/\ Fluent49_1' = [Fluent49_1 EXCEPT ![a] = TRUE]
/\ Fluent25_0' = [x0 \in Core |-> FALSE]
/\ Fluent47_5' = [Fluent47_5 EXCEPT ![c] = FALSE]
/\ Fluent19_0' = [Fluent19_0 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent80_2, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent68_14, Fluent46_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9>>

do_bus_read_valid(c,a,v) ==
/\ bus_read[c][a]
/\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read_for_ownership,bus_upgrade>>
/\ Fluent80_2' = [Fluent80_2 EXCEPT ![v] = TRUE]
/\ Fluent68_14' = [Fluent68_14 EXCEPT ![a] = TRUE]
/\ Fluent6_17' = [x0 \in Core |-> TRUE]
/\ Fluent39_0' = [x0 \in Core |-> TRUE]
/\ UNCHANGED<<Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, Fluent92_4, Fluent38_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9>>

complete_proc_read_invalid_shared(c,a,v) ==
/\ proc_read[c][a]
/\ bus_transfer[v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_read[C][A])))
/\ bus_transfer' = [V \in Value |-> FALSE]
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ bus_in_use' = FALSE
/\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<exclusive,proc_write,bus_read,bus_read_for_ownership,bus_upgrade>>
/\ Fluent81_2' = [Fluent81_2 EXCEPT ![v] = TRUE]
/\ Fluent5_17' = [Fluent5_17 EXCEPT ![c] = TRUE]
/\ Fluent25_0' = [x0 \in Core |-> FALSE]
/\ Fluent93_4' = [Fluent93_4 EXCEPT ![a] = TRUE]
/\ Fluent63_14' = [Fluent63_14 EXCEPT ![a] = TRUE]
/\ Fluent15_9' = [Fluent15_9 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent77_16, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent73_0, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9>>

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ proc_read[c][a]
/\ (\A V \in Value : ~(bus_transfer[V]))
/\ (\A C \in Core : (\A A \in Address : ~(bus_read[C][A])))
/\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
/\ bus_in_use' = FALSE
/\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<shared,proc_write,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ Fluent105_10' = [Fluent105_10 EXCEPT ![v] = TRUE]
/\ Fluent76_16' = [Fluent76_16 EXCEPT ![c] = TRUE]
/\ Fluent106_10' = [Fluent106_10 EXCEPT ![v] = Fluent105_10[v]]
/\ Fluent94_18' = [Fluent94_18 EXCEPT ![a] = TRUE]
/\ Fluent19_0' = [Fluent19_0 EXCEPT ![c] = TRUE]
/\ Fluent18_0' = [x0 \in Core |-> TRUE]
/\ Fluent69_14' = [Fluent69_14 EXCEPT ![a] = Fluent68_14[a]]
/\ UNCHANGED<<Fluent80_2, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent73_0, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent16_9, Fluent63_14, Fluent15_9>>

issue_proc_write_invalid(c,a,v) ==
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
/\ bus_read_for_ownership' = [C \in Core |-> [A \in Address |-> (bus_read_for_ownership[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<exclusive,shared,proc_read,bus_read,bus_upgrade,bus_transfer>>
/\ Fluent26_0' = [Fluent26_0 EXCEPT ![c] = Fluent25_0[c]]
/\ Fluent73_0' = [Fluent73_0 EXCEPT ![c] = TRUE]
/\ Fluent39_0' = [Fluent39_0 EXCEPT ![c] = TRUE]
/\ Fluent15_9' = [Fluent15_9 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14>>

do_bus_read_for_ownership_invalid(c,a) ==
/\ bus_read_for_ownership[c][a]
/\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<exclusive,shared,proc_read,proc_write,bus_in_use,bus_read,bus_upgrade,bus_transfer>>
/\ Fluent73_0' = [Fluent73_0 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9>>

do_bus_read_for_ownership_valid(c,a,v) ==
/\ bus_read_for_ownership[c][a]
/\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read,bus_upgrade>>
/\ Fluent80_2' = [Fluent80_2 EXCEPT ![v] = TRUE]
/\ Fluent73_0' = [Fluent73_0 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9>>

complete_proc_write_invalid(c,a,v) ==
/\ proc_write[c][a][v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_read_for_ownership[C][A])))
/\ bus_transfer' = [V \in Value |-> FALSE]
/\ bus_in_use' = FALSE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
/\ UNCHANGED <<exclusive,shared,proc_read,bus_read,bus_read_for_ownership,bus_upgrade>>
/\ Fluent74_0' = [x0 \in Core |-> Fluent73_0[c]]
/\ Fluent38_0' = [Fluent38_0 EXCEPT ![c] = TRUE]
/\ Fluent16_9' = [Fluent16_9 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent6_17, Fluent92_4, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent63_14, Fluent15_9>>

proc_write_exclusive(c,a,v) ==
/\ exclusive[c][a]
/\ ~(bus_in_use)
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<shared,proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ Fluent77_16' = [Fluent77_16 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9>>

issue_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
/\ bus_upgrade' = [C \in Core |-> [A \in Address |-> (bus_upgrade[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<exclusive,shared,proc_read,bus_read,bus_read_for_ownership,bus_transfer>>
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9>>

do_bus_upgrade(c,a) ==
/\ bus_upgrade[c][a]
/\ bus_upgrade' = [bus_upgrade EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<exclusive,proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_transfer>>
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9>>

complete_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ proc_write[c][a][v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_upgrade[C][A])))
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
/\ bus_in_use' = FALSE
/\ UNCHANGED <<exclusive,proc_read,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ Fluent64_14' = [Fluent64_14 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9>>

evict_modified(c,a) ==
/\ ~(bus_in_use)
/\ UNCHANGED <<exclusive,shared,proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9>>

evict_exclusive_or_shared(c,a) ==
/\ ~(bus_in_use)
/\ (exclusive[c][a] \/ shared[c][a])
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9>>

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
