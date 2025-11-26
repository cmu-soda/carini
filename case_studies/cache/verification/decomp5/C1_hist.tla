--------------------------- MODULE C1_hist ---------------------------


CONSTANTS Address, Core, Value

VARIABLES memory, Fluent49_23, Fluent2_26, Fluent28_0, Fluent27_0, Fluent24_6, Fluent23_6, modified, Fluent48_23, Fluent43_17, cache, Fluent53_0, Fluent52_0, bus_read, Fluent3_26, Fluent10_2, Fluent55_6, Fluent38_4, Fluent34_8, Fluent39_4, Fluent56_6, Fluent33_8, invalid, Fluent6_6, Fluent5_6, Fluent9_2, Fluent44_17

vars == <<memory, Fluent49_23, Fluent2_26, Fluent28_0, Fluent27_0, Fluent24_6, Fluent23_6, modified, Fluent48_23, Fluent43_17, cache, Fluent53_0, Fluent52_0, bus_read, Fluent3_26, Fluent10_2, Fluent55_6, Fluent38_4, Fluent34_8, Fluent39_4, Fluent56_6, Fluent33_8, invalid, Fluent6_6, Fluent5_6, Fluent9_2, Fluent44_17>>

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
/\ (memory \in [Address -> Value])
/\ (cache \in [Core -> [Address -> Value]])
/\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
/\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]
/\ bus_read = [c \in Core |-> [a \in Address |-> FALSE]]
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
/\ invalid[c][a]
/\ bus_read' = [C \in Core |-> [A \in Address |-> (bus_read[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<memory,cache,modified,invalid>>
/\ Fluent2_26' = [Fluent2_26 EXCEPT ![c] = TRUE]
/\ Fluent24_6' = [Fluent24_6 EXCEPT ![c] = TRUE]
/\ Fluent34_8' = [x0 \in Value |-> FALSE]
/\ Fluent5_6' = [Fluent5_6 EXCEPT ![c] = TRUE]
/\ Fluent44_17' = [Fluent44_17 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent3_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent27_0, Fluent38_4, Fluent23_6, Fluent39_4, Fluent56_6, Fluent33_8, Fluent48_23, Fluent6_6, Fluent9_2, Fluent43_17>>
/\ CandSep'

do_bus_read_invalid(c,a) ==
/\ invalid[c][a]
/\ bus_read[c][a]
/\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<memory,cache,modified,invalid>>
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent3_26, Fluent2_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent27_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent23_6, Fluent39_4, Fluent56_6, Fluent33_8, Fluent48_23, Fluent6_6, Fluent5_6, Fluent9_2, Fluent43_17, Fluent44_17>>
/\ CandSep'

do_bus_read_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ cache[c][a] = v
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ (modified[c][a] => memory' = [memory EXCEPT![a] = v])
/\ (~(modified[c][a]) => memory' = memory)
/\ bus_read[c][a]
/\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<cache,invalid>>
/\ Fluent10_2' = [Fluent10_2 EXCEPT ![v] = TRUE]
/\ Fluent28_0' = [x0 \in Core |-> TRUE]
/\ Fluent39_4' = [x0 \in Address |-> TRUE]
/\ Fluent44_17' = [Fluent44_17 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent3_26, Fluent2_26, Fluent55_6, Fluent27_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent23_6, Fluent56_6, Fluent33_8, Fluent48_23, Fluent6_6, Fluent5_6, Fluent9_2, Fluent43_17>>
/\ CandSep'

complete_proc_read_invalid_shared(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_read[C][A])))
/\ UNCHANGED <<memory,modified,bus_read>>
/\ Fluent3_26' = [Fluent3_26 EXCEPT ![c] = TRUE]
/\ Fluent9_2' = [Fluent9_2 EXCEPT ![v] = TRUE]
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent2_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent27_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent23_6, Fluent39_4, Fluent56_6, Fluent33_8, Fluent48_23, Fluent6_6, Fluent5_6, Fluent43_17, Fluent44_17>>
/\ CandSep'

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ invalid[c][a]
/\ memory[a] = v
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_read[C][A])))
/\ UNCHANGED <<memory,modified,bus_read>>
/\ Fluent56_6' = [Fluent56_6 EXCEPT ![c] = TRUE]
/\ Fluent6_6' = [Fluent6_6 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent3_26, Fluent2_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent27_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent23_6, Fluent39_4, Fluent33_8, Fluent48_23, Fluent5_6, Fluent9_2, Fluent43_17, Fluent44_17>>
/\ CandSep'

issue_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,invalid,bus_read>>
/\ Fluent53_0' = [x0 \in Core |-> TRUE]
/\ Fluent34_8' = [Fluent34_8 EXCEPT ![v] = TRUE]
/\ Fluent39_4' = [Fluent39_4 EXCEPT ![a] = TRUE]
/\ Fluent33_8' = [Fluent33_8 EXCEPT ![v] = TRUE]
/\ Fluent48_23' = [Fluent48_23 EXCEPT ![c] = TRUE]
/\ Fluent44_17' = [Fluent44_17 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent49_23, Fluent52_0, Fluent3_26, Fluent2_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent27_0, Fluent24_6, Fluent38_4, Fluent23_6, Fluent56_6, Fluent6_6, Fluent5_6, Fluent9_2, Fluent43_17>>
/\ CandSep'

do_bus_read_for_ownership_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,invalid,bus_read>>
/\ Fluent48_23' = [Fluent48_23 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent3_26, Fluent2_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent27_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent23_6, Fluent39_4, Fluent56_6, Fluent33_8, Fluent6_6, Fluent5_6, Fluent9_2, Fluent43_17, Fluent44_17>>
/\ CandSep'

do_bus_read_for_ownership_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ cache[c][a] = v
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ (modified[c][a] => memory' = [memory EXCEPT![a] = v])
/\ (~(modified[c][a]) => memory' = memory)
/\ UNCHANGED <<cache,bus_read>>
/\ Fluent52_0' = [Fluent52_0 EXCEPT ![c] = TRUE]
/\ Fluent10_2' = [Fluent10_2 EXCEPT ![v] = TRUE]
/\ Fluent48_23' = [Fluent48_23 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent3_26, Fluent2_26, Fluent55_6, Fluent28_0, Fluent27_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent23_6, Fluent39_4, Fluent56_6, Fluent33_8, Fluent6_6, Fluent5_6, Fluent9_2, Fluent43_17, Fluent44_17>>
/\ CandSep'

complete_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,bus_read>>
/\ Fluent49_23' = [x0 \in Core |-> Fluent48_23[c]]
/\ Fluent38_4' = [Fluent38_4 EXCEPT ![a] = TRUE]
/\ Fluent33_8' = [Fluent33_8 EXCEPT ![v] = FALSE]
/\ Fluent43_17' = [Fluent43_17 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent53_0, Fluent52_0, Fluent3_26, Fluent2_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent27_0, Fluent24_6, Fluent34_8, Fluent23_6, Fluent39_4, Fluent56_6, Fluent48_23, Fluent6_6, Fluent5_6, Fluent9_2, Fluent44_17>>
/\ CandSep'

proc_write_exclusive(c,a,v) ==
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,invalid,bus_read>>
/\ Fluent55_6' = [Fluent55_6 EXCEPT ![c] = TRUE]
/\ Fluent23_6' = [Fluent23_6 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent3_26, Fluent2_26, Fluent10_2, Fluent28_0, Fluent27_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent39_4, Fluent56_6, Fluent33_8, Fluent48_23, Fluent6_6, Fluent5_6, Fluent9_2, Fluent43_17, Fluent44_17>>
/\ CandSep'

do_bus_upgrade(c,a) ==
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<memory,cache,modified,bus_read>>
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent3_26, Fluent2_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent27_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent23_6, Fluent39_4, Fluent56_6, Fluent33_8, Fluent48_23, Fluent6_6, Fluent5_6, Fluent9_2, Fluent43_17, Fluent44_17>>
/\ CandSep'

complete_proc_write_shared(c,a,v) ==
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,invalid,bus_read>>
/\ Fluent27_0' = [Fluent27_0 EXCEPT ![c] = TRUE]
/\ Fluent33_8' = [Fluent33_8 EXCEPT ![v] = FALSE]
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent3_26, Fluent2_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent23_6, Fluent39_4, Fluent56_6, Fluent48_23, Fluent6_6, Fluent5_6, Fluent9_2, Fluent43_17, Fluent44_17>>
/\ CandSep'

evict_modified(c,a) ==
/\ modified[c][a]
/\ memory' = [memory EXCEPT![a] = cache[c][a]]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<cache,bus_read>>
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent3_26, Fluent2_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent27_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent23_6, Fluent39_4, Fluent56_6, Fluent33_8, Fluent48_23, Fluent6_6, Fluent5_6, Fluent9_2, Fluent43_17, Fluent44_17>>
/\ CandSep'

evict_exclusive_or_shared(c,a) ==
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<memory,cache,modified,bus_read>>
/\ UNCHANGED<<Fluent49_23, Fluent53_0, Fluent52_0, Fluent3_26, Fluent2_26, Fluent10_2, Fluent55_6, Fluent28_0, Fluent27_0, Fluent24_6, Fluent38_4, Fluent34_8, Fluent23_6, Fluent39_4, Fluent56_6, Fluent33_8, Fluent48_23, Fluent6_6, Fluent5_6, Fluent9_2, Fluent43_17, Fluent44_17>>
/\ CandSep'

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
\/ do_bus_upgrade(c,a)
\/ complete_proc_write_shared(c,a,v)
\/ evict_modified(c,a)
\/ evict_exclusive_or_shared(c,a)

Spec == (Init /\ [][Next]_vars)

Safety == (\A C \in Core : (\A A \in Address : ((~(invalid[C][A]) /\ ~(modified[C][A])) => cache[C][A] = memory[A])))
=============================================================================
