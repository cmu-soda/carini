--------------------------- MODULE T1_hist ---------------------------


CONSTANTS Address, Core, Value

VARIABLES memory, Fluent31_17, bus_transfer, Fluent16_14, proc_write, bus_read_for_ownership, modified, Fluent26_17, Fluent21_25, cache, Fluent3_6, Fluent2_6, Fluent30_17, bus_read, Fluent17_14, bus_in_use, Fluent15_14, Fluent20_25, proc_read, Fluent37_6, invalid, Fluent27_17, Fluent38_6, Fluent25_17, bus_upgrade

vars == <<memory, Fluent31_17, bus_transfer, Fluent16_14, proc_write, bus_read_for_ownership, modified, Fluent26_17, Fluent21_25, cache, Fluent3_6, Fluent2_6, Fluent30_17, bus_read, Fluent17_14, bus_in_use, Fluent15_14, Fluent20_25, proc_read, Fluent37_6, invalid, Fluent27_17, Fluent38_6, Fluent25_17, bus_upgrade>>

CandSep ==
/\ \A var0 \in Core : (Fluent27_17[var0]) => ((Fluent25_17[var0]) => (Fluent26_17[var0]))
/\ \A var0 \in Core : (Fluent31_17[var0]) => (Fluent30_17[var0])
/\ \A var0 \in Core : (Fluent20_25[var0]) => (~(Fluent21_25[var0]))
/\ \A var0 \in Address : (Fluent17_14[var0]) => ((Fluent15_14[var0]) => (Fluent16_14[var0]))
/\ \A var0 \in Core : (Fluent3_6[var0]) => (Fluent2_6[var0])
/\ \A var0 \in Core : (Fluent37_6[var0]) => (~(Fluent38_6[var0]))

Init ==
/\ (memory \in [Address -> Value])
/\ (cache \in [Core -> [Address -> Value]])
/\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
/\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]
/\ proc_read = [c \in Core |-> [a \in Address |-> FALSE]]
/\ proc_write = [c \in Core |-> [a \in Address |-> [v \in Value |-> FALSE]]]
/\ bus_in_use = FALSE
/\ bus_read = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_read_for_ownership = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_upgrade = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_transfer = [v \in Value |-> FALSE]
/\ Fluent31_17 = [ x0 \in Core |-> FALSE]
/\ Fluent3_6 = [ x0 \in Core |-> FALSE]
/\ Fluent2_6 = [ x0 \in Core |-> FALSE]
/\ Fluent30_17 = [ x0 \in Core |-> FALSE]
/\ Fluent17_14 = [ x0 \in Address |-> FALSE]
/\ Fluent15_14 = [ x0 \in Address |-> FALSE]
/\ Fluent16_14 = [ x0 \in Address |-> FALSE]
/\ Fluent20_25 = [ x0 \in Core |-> FALSE]
/\ Fluent37_6 = [ x0 \in Core |-> FALSE]
/\ Fluent27_17 = [ x0 \in Core |-> FALSE]
/\ Fluent26_17 = [ x0 \in Core |-> FALSE]
/\ Fluent38_6 = [ x0 \in Core |-> FALSE]
/\ Fluent25_17 = [ x0 \in Core |-> FALSE]
/\ Fluent21_25 = [ x0 \in Core |-> FALSE]

issue_proc_read_invalid(c,a) ==
/\ invalid[c][a]
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_read' = [proc_read EXCEPT![c][a] = TRUE]
/\ bus_read' = [C \in Core |-> [A \in Address |-> (bus_read[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<memory,cache,modified,invalid,proc_write,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent31_17, Fluent3_6, Fluent2_6, Fluent30_17, Fluent17_14, Fluent15_14, Fluent16_14, Fluent20_25, Fluent37_6, Fluent27_17, Fluent26_17, Fluent38_6, Fluent25_17, Fluent21_25>>

do_bus_read_invalid(c,a) ==
/\ bus_read[c][a]
/\ invalid[c][a]
/\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<memory,cache,modified,invalid,proc_read,proc_write,bus_in_use,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent31_17, Fluent3_6, Fluent2_6, Fluent30_17, Fluent17_14, Fluent15_14, Fluent16_14, Fluent20_25, Fluent37_6, Fluent27_17, Fluent26_17, Fluent38_6, Fluent25_17, Fluent21_25>>

do_bus_read_valid(c,a,v) ==
/\ bus_read[c][a]
/\ ~(invalid[c][a])
/\ cache[c][a] = v
/\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ (modified[c][a] => memory' = [memory EXCEPT![a] = v])
/\ (~(modified[c][a]) => memory' = memory)
/\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
/\ UNCHANGED <<cache,invalid,proc_read,proc_write,bus_in_use,bus_read_for_ownership,bus_upgrade>>
/\ Fluent2_6' = [x0 \in Core |-> TRUE]
/\ Fluent30_17' = [Fluent30_17 EXCEPT ![c] = FALSE]
/\ Fluent15_14' = [Fluent15_14 EXCEPT ![a] = TRUE]
/\ Fluent38_6' = [[x0 \in Core |-> Fluent37_6[c]] EXCEPT ![c] = FALSE]
/\ Fluent25_17' = [Fluent25_17 EXCEPT ![c] = TRUE]
/\ Fluent21_25' = [x0 \in Core |-> TRUE]
/\ UNCHANGED<<Fluent31_17, Fluent3_6, Fluent17_14, Fluent16_14, Fluent20_25, Fluent37_6, Fluent27_17, Fluent26_17>>

complete_proc_read_invalid_shared(c,a,v) ==
/\ invalid[c][a]
/\ proc_read[c][a]
/\ bus_transfer[v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_read[C][A])))
/\ bus_transfer' = [V \in Value |-> FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ bus_in_use' = FALSE
/\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<memory,modified,proc_write,bus_read,bus_read_for_ownership,bus_upgrade>>
/\ Fluent3_6' = [Fluent3_6 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent31_17, Fluent2_6, Fluent30_17, Fluent17_14, Fluent15_14, Fluent16_14, Fluent20_25, Fluent37_6, Fluent27_17, Fluent26_17, Fluent38_6, Fluent25_17, Fluent21_25>>

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ invalid[c][a]
/\ proc_read[c][a]
/\ (\A V \in Value : ~(bus_transfer[V]))
/\ (\A C \in Core : (\A A \in Address : ~(bus_read[C][A])))
/\ memory[a] = v
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ bus_in_use' = FALSE
/\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<memory,modified,proc_write,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ Fluent31_17' = [Fluent31_17 EXCEPT ![c] = Fluent30_17[c]]
/\ Fluent30_17' = [Fluent30_17 EXCEPT ![c] = TRUE]
/\ Fluent17_14' = [[x0 \in Address |-> TRUE] EXCEPT ![a] = FALSE]
/\ Fluent20_25' = [Fluent20_25 EXCEPT ![c] = Fluent21_25[c]]
/\ Fluent37_6' = [Fluent37_6 EXCEPT ![c] = TRUE]
/\ Fluent27_17' = [x0 \in Core |-> TRUE]
/\ Fluent26_17' = [Fluent26_17 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent3_6, Fluent2_6, Fluent15_14, Fluent16_14, Fluent38_6, Fluent25_17, Fluent21_25>>

issue_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
/\ bus_read_for_ownership' = [C \in Core |-> [A \in Address |-> (bus_read_for_ownership[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<memory,cache,modified,invalid,proc_read,bus_read,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent31_17, Fluent3_6, Fluent2_6, Fluent30_17, Fluent17_14, Fluent15_14, Fluent16_14, Fluent20_25, Fluent37_6, Fluent27_17, Fluent26_17, Fluent38_6, Fluent25_17, Fluent21_25>>

do_bus_read_for_ownership_invalid(c,a) ==
/\ bus_read_for_ownership[c][a]
/\ invalid[c][a]
/\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<memory,cache,modified,invalid,proc_read,proc_write,bus_in_use,bus_read,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent31_17, Fluent3_6, Fluent2_6, Fluent30_17, Fluent17_14, Fluent15_14, Fluent16_14, Fluent20_25, Fluent37_6, Fluent27_17, Fluent26_17, Fluent38_6, Fluent25_17, Fluent21_25>>

do_bus_read_for_ownership_valid(c,a,v) ==
/\ bus_read_for_ownership[c][a]
/\ ~(invalid[c][a])
/\ cache[c][a] = v
/\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ (modified[c][a] => memory' = [memory EXCEPT![a] = v])
/\ (~(modified[c][a]) => memory' = memory)
/\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
/\ UNCHANGED <<cache,proc_read,proc_write,bus_in_use,bus_read,bus_upgrade>>
/\ UNCHANGED<<Fluent31_17, Fluent3_6, Fluent2_6, Fluent30_17, Fluent17_14, Fluent15_14, Fluent16_14, Fluent20_25, Fluent37_6, Fluent27_17, Fluent26_17, Fluent38_6, Fluent25_17, Fluent21_25>>

complete_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ proc_write[c][a][v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_read_for_ownership[C][A])))
/\ bus_transfer' = [V \in Value |-> FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ bus_in_use' = FALSE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
/\ UNCHANGED <<memory,proc_read,bus_read,bus_read_for_ownership,bus_upgrade>>
/\ UNCHANGED<<Fluent31_17, Fluent3_6, Fluent2_6, Fluent30_17, Fluent17_14, Fluent15_14, Fluent16_14, Fluent20_25, Fluent37_6, Fluent27_17, Fluent26_17, Fluent38_6, Fluent25_17, Fluent21_25>>

proc_write_exclusive(c,a,v) ==
/\ ~(bus_in_use)
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,invalid,proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent31_17, Fluent3_6, Fluent2_6, Fluent30_17, Fluent17_14, Fluent15_14, Fluent16_14, Fluent20_25, Fluent37_6, Fluent27_17, Fluent26_17, Fluent38_6, Fluent25_17, Fluent21_25>>

issue_proc_write_shared(c,a,v) ==
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
/\ bus_upgrade' = [C \in Core |-> [A \in Address |-> (bus_upgrade[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<memory,cache,modified,invalid,proc_read,bus_read,bus_read_for_ownership,bus_transfer>>
/\ Fluent16_14' = [Fluent16_14 EXCEPT ![a] = TRUE]
/\ Fluent26_17' = [Fluent26_17 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent31_17, Fluent3_6, Fluent2_6, Fluent30_17, Fluent17_14, Fluent15_14, Fluent20_25, Fluent37_6, Fluent27_17, Fluent38_6, Fluent25_17, Fluent21_25>>

do_bus_upgrade(c,a) ==
/\ bus_upgrade[c][a]
/\ bus_upgrade' = [bus_upgrade EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<memory,cache,modified,proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_transfer>>
/\ UNCHANGED<<Fluent31_17, Fluent3_6, Fluent2_6, Fluent30_17, Fluent17_14, Fluent15_14, Fluent16_14, Fluent20_25, Fluent37_6, Fluent27_17, Fluent26_17, Fluent38_6, Fluent25_17, Fluent21_25>>

complete_proc_write_shared(c,a,v) ==
/\ proc_write[c][a][v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_upgrade[C][A])))
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
/\ bus_in_use' = FALSE
/\ UNCHANGED <<memory,invalid,proc_read,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent31_17, Fluent3_6, Fluent2_6, Fluent30_17, Fluent17_14, Fluent15_14, Fluent16_14, Fluent20_25, Fluent37_6, Fluent27_17, Fluent26_17, Fluent38_6, Fluent25_17, Fluent21_25>>

evict_modified(c,a) ==
/\ ~(bus_in_use)
/\ modified[c][a]
/\ memory' = [memory EXCEPT![a] = cache[c][a]]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<cache,proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent31_17, Fluent3_6, Fluent2_6, Fluent30_17, Fluent17_14, Fluent15_14, Fluent16_14, Fluent20_25, Fluent37_6, Fluent27_17, Fluent26_17, Fluent38_6, Fluent25_17, Fluent21_25>>

evict_exclusive_or_shared(c,a) ==
/\ ~(bus_in_use)
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<memory,cache,modified,proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent31_17, Fluent3_6, Fluent2_6, Fluent30_17, Fluent17_14, Fluent15_14, Fluent16_14, Fluent20_25, Fluent37_6, Fluent27_17, Fluent26_17, Fluent38_6, Fluent25_17, Fluent21_25>>

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

Safety == (\A C \in Core : (\A A \in Address : ((~(invalid[C][A]) /\ ~(modified[C][A])) => cache[C][A] = memory[A])))
=============================================================================
