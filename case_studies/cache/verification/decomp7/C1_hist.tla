--------------------------- MODULE C1_hist ---------------------------


CONSTANTS Address, Core, Value

VARIABLES Fluent4_2, Fluent28_22, shared, Fluent3_2, Fluent29_22, cache, memory, proc_write, Fluent19_22, proc_read, invalid, Fluent14_9, exclusive, modified, Fluent13_9, Fluent20_22

vars == <<Fluent4_2, Fluent28_22, shared, Fluent3_2, Fluent29_22, cache, memory, proc_write, Fluent19_22, proc_read, invalid, Fluent14_9, exclusive, modified, Fluent13_9, Fluent20_22>>

CandSep ==
/\ \A var0 \in Address : (Fluent13_9[var0]) => (~(Fluent14_9[var0]))
/\ \A var0 \in Address : (Fluent19_22[var0]) => (Fluent20_22[var0])
/\ \A var0 \in Value : (Fluent3_2[var0]) => (Fluent4_2[var0])
/\ \A var0 \in Address : (Fluent28_22[var0]) => (Fluent29_22[var0])

Init ==
/\ (memory \in [Address -> Value])
/\ (cache \in [Core -> [Address -> Value]])
/\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
/\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
/\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
/\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]
/\ proc_read = [c \in Core |-> [a \in Address |-> FALSE]]
/\ proc_write = [c \in Core |-> [a \in Address |-> [v \in Value |-> FALSE]]]
/\ Fluent4_2 = [ x0 \in Value |-> FALSE]
/\ Fluent28_22 = [ x0 \in Address |-> FALSE]
/\ Fluent3_2 = [ x0 \in Value |-> FALSE]
/\ Fluent29_22 = [ x0 \in Address |-> FALSE]
/\ Fluent19_22 = [ x0 \in Address |-> FALSE]
/\ Fluent14_9 = [ x0 \in Address |-> FALSE]
/\ Fluent13_9 = [ x0 \in Address |-> FALSE]
/\ Fluent20_22 = [ x0 \in Address |-> FALSE]

issue_proc_read_invalid(c,a) ==
/\ invalid[c][a]
/\ proc_read' = [proc_read EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<proc_write,memory,cache,modified,exclusive,shared,invalid>>
/\ Fluent14_9' = [Fluent14_9 EXCEPT ![a] = TRUE]
/\ Fluent13_9' = [Fluent13_9 EXCEPT ![a] = FALSE]
/\ Fluent20_22' = [Fluent20_22 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent4_2, Fluent28_22, Fluent3_2, Fluent29_22, Fluent19_22>>
/\ CandSep'

do_bus_read_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<proc_read,proc_write,memory,cache,modified,exclusive,shared,invalid>>
/\ Fluent14_9' = [Fluent14_9 EXCEPT ![a] = FALSE]
/\ UNCHANGED<<Fluent4_2, Fluent28_22, Fluent3_2, Fluent29_22, Fluent19_22, Fluent13_9, Fluent20_22>>
/\ CandSep'

do_bus_read_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ cache[c][a] = v
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ (modified[c][a] => memory' = [memory EXCEPT![a] = v])
/\ (~(modified[c][a]) => memory' = memory)
/\ UNCHANGED <<proc_read,proc_write,cache,invalid>>
/\ Fluent4_2' = [Fluent4_2 EXCEPT ![v] = TRUE]
/\ Fluent19_22' = [Fluent19_22 EXCEPT ![a] = TRUE]
/\ Fluent14_9' = [Fluent14_9 EXCEPT ![a] = FALSE]
/\ UNCHANGED<<Fluent28_22, Fluent3_2, Fluent29_22, Fluent13_9, Fluent20_22>>
/\ CandSep'

complete_proc_read_invalid_shared(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ proc_read[c][a]
/\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<proc_write,memory,modified,exclusive>>
/\ Fluent3_2' = [Fluent3_2 EXCEPT ![v] = TRUE]
/\ UNCHANGED<<Fluent4_2, Fluent28_22, Fluent29_22, Fluent19_22, Fluent14_9, Fluent13_9, Fluent20_22>>
/\ CandSep'

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ invalid[c][a]
/\ memory[a] = v
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ proc_read[c][a]
/\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<proc_write,memory,modified,shared>>
/\ Fluent13_9' = [Fluent13_9 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent4_2, Fluent28_22, Fluent3_2, Fluent29_22, Fluent19_22, Fluent14_9, Fluent20_22>>
/\ CandSep'

issue_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
/\ UNCHANGED <<proc_read,memory,cache,modified,exclusive,shared,invalid>>
/\ Fluent28_22' = [Fluent28_22 EXCEPT ![a] = TRUE]
/\ Fluent29_22' = [Fluent29_22 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent4_2, Fluent3_2, Fluent19_22, Fluent14_9, Fluent13_9, Fluent20_22>>
/\ CandSep'

do_bus_read_for_ownership_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<proc_read,proc_write,memory,cache,modified,exclusive,shared,invalid>>
/\ Fluent28_22' = [Fluent28_22 EXCEPT ![a] = FALSE]
/\ UNCHANGED<<Fluent4_2, Fluent3_2, Fluent29_22, Fluent19_22, Fluent14_9, Fluent13_9, Fluent20_22>>
/\ CandSep'

do_bus_read_for_ownership_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ cache[c][a] = v
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ (modified[c][a] => memory' = [memory EXCEPT![a] = v])
/\ (~(modified[c][a]) => memory' = memory)
/\ UNCHANGED <<proc_read,proc_write,cache>>
/\ Fluent4_2' = [Fluent4_2 EXCEPT ![v] = TRUE]
/\ Fluent28_22' = [Fluent28_22 EXCEPT ![a] = FALSE]
/\ UNCHANGED<<Fluent3_2, Fluent29_22, Fluent19_22, Fluent14_9, Fluent13_9, Fluent20_22>>
/\ CandSep'

complete_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ proc_write[c][a][v]
/\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
/\ UNCHANGED <<proc_read,memory,exclusive,shared>>
/\ Fluent29_22' = [Fluent29_22 EXCEPT ![a] = FALSE]
/\ UNCHANGED<<Fluent4_2, Fluent28_22, Fluent3_2, Fluent19_22, Fluent14_9, Fluent13_9, Fluent20_22>>
/\ CandSep'

proc_write_exclusive(c,a,v) ==
/\ exclusive[c][a]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<proc_read,proc_write,memory,invalid,shared>>
/\ UNCHANGED<<Fluent4_2, Fluent28_22, Fluent3_2, Fluent29_22, Fluent19_22, Fluent14_9, Fluent13_9, Fluent20_22>>
/\ CandSep'

issue_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
/\ UNCHANGED <<proc_read,memory,cache,modified,exclusive,shared,invalid>>
/\ UNCHANGED<<Fluent4_2, Fluent28_22, Fluent3_2, Fluent29_22, Fluent19_22, Fluent14_9, Fluent13_9, Fluent20_22>>
/\ CandSep'

do_bus_upgrade(c,a) ==
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<proc_read,proc_write,memory,cache,modified,exclusive>>
/\ UNCHANGED<<Fluent4_2, Fluent28_22, Fluent3_2, Fluent29_22, Fluent19_22, Fluent14_9, Fluent13_9, Fluent20_22>>
/\ CandSep'

complete_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ proc_write[c][a][v]
/\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
/\ UNCHANGED <<proc_read,memory,invalid,exclusive>>
/\ UNCHANGED<<Fluent4_2, Fluent28_22, Fluent3_2, Fluent29_22, Fluent19_22, Fluent14_9, Fluent13_9, Fluent20_22>>
/\ CandSep'

evict_modified(c,a) ==
/\ modified[c][a]
/\ memory' = [memory EXCEPT![a] = cache[c][a]]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<proc_read,proc_write,cache,exclusive,shared>>
/\ UNCHANGED<<Fluent4_2, Fluent28_22, Fluent3_2, Fluent29_22, Fluent19_22, Fluent14_9, Fluent13_9, Fluent20_22>>
/\ CandSep'

evict_exclusive_or_shared(c,a) ==
/\ (exclusive[c][a] \/ shared[c][a])
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<proc_read,proc_write,memory,cache,modified>>
/\ UNCHANGED<<Fluent4_2, Fluent28_22, Fluent3_2, Fluent29_22, Fluent19_22, Fluent14_9, Fluent13_9, Fluent20_22>>
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
\/ issue_proc_write_shared(c,a,v)
\/ do_bus_upgrade(c,a)
\/ complete_proc_write_shared(c,a,v)
\/ evict_modified(c,a)
\/ evict_exclusive_or_shared(c,a)

Spec == (Init /\ [][Next]_vars)

Safety == (\A C \in Core : (\A A \in Address : ((~(invalid[C][A]) /\ ~(modified[C][A])) => cache[C][A] = memory[A])))
=============================================================================
