--------------------------- MODULE C1_hist ---------------------------


CONSTANTS Address, Core, Value

VARIABLES Fluent10_18, shared, cache, memory, Fluent3_7, Fluent9_18, bus_in_use, proc_write, proc_read, invalid, exclusive, modified, Fluent4_7

vars == <<Fluent10_18, shared, cache, memory, Fluent3_7, Fluent9_18, bus_in_use, proc_write, proc_read, invalid, exclusive, modified, Fluent4_7>>

CandSep ==
/\ \A var0 \in Address : (Fluent9_18[var0]) => (Fluent10_18[var0])
/\ \A var0 \in Value : (Fluent3_7[var0]) => (Fluent4_7[var0])

Init ==
/\ (memory \in [Address -> Value])
/\ (cache \in [Core -> [Address -> Value]])
/\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
/\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
/\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
/\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]
/\ proc_read = [c \in Core |-> [a \in Address |-> FALSE]]
/\ proc_write = [c \in Core |-> [a \in Address |-> [v \in Value |-> FALSE]]]
/\ bus_in_use = FALSE
/\ Fluent10_18 = [ x0 \in Address |-> FALSE]
/\ Fluent4_7 = [ x0 \in Value |-> FALSE]
/\ Fluent9_18 = [ x0 \in Address |-> FALSE]
/\ Fluent3_7 = [ x0 \in Value |-> FALSE]

issue_proc_read_invalid(c,a) ==
/\ invalid[c][a]
/\ proc_read' = [proc_read EXCEPT![c][a] = TRUE]
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ UNCHANGED <<proc_write,memory,cache,modified,exclusive,shared,invalid>>
/\ Fluent10_18' = [Fluent10_18 EXCEPT ![a] = TRUE]
/\ Fluent9_18' = [Fluent9_18 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent4_7, Fluent3_7>>
/\ CandSep'

do_bus_read_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<bus_in_use,proc_read,proc_write,memory,cache,modified,exclusive,shared,invalid>>
/\ Fluent9_18' = [Fluent9_18 EXCEPT ![a] = FALSE]
/\ UNCHANGED<<Fluent10_18, Fluent4_7, Fluent3_7>>
/\ CandSep'

do_bus_read_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ cache[c][a] = v
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ (modified[c][a] => memory' = [memory EXCEPT![a] = v])
/\ (~(modified[c][a]) => memory' = memory)
/\ UNCHANGED <<bus_in_use,proc_read,proc_write,cache,invalid>>
/\ Fluent4_7' = [Fluent4_7 EXCEPT ![v] = TRUE]
/\ Fluent9_18' = [Fluent9_18 EXCEPT ![a] = FALSE]
/\ UNCHANGED<<Fluent10_18, Fluent3_7>>
/\ CandSep'

complete_proc_read_invalid_shared(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ proc_read[c][a]
/\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
/\ bus_in_use' = FALSE
/\ UNCHANGED <<proc_write,memory,modified,exclusive>>
/\ Fluent3_7' = [Fluent3_7 EXCEPT ![v] = TRUE]
/\ UNCHANGED<<Fluent10_18, Fluent4_7, Fluent9_18>>
/\ CandSep'

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ invalid[c][a]
/\ memory[a] = v
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ proc_read[c][a]
/\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
/\ bus_in_use' = FALSE
/\ UNCHANGED <<proc_write,memory,modified,shared>>
/\ Fluent10_18' = [Fluent10_18 EXCEPT ![a] = FALSE]
/\ UNCHANGED<<Fluent4_7, Fluent9_18, Fluent3_7>>
/\ CandSep'

issue_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ UNCHANGED <<proc_read,memory,cache,modified,exclusive,shared,invalid>>
/\ UNCHANGED<<Fluent10_18, Fluent4_7, Fluent9_18, Fluent3_7>>
/\ CandSep'

do_bus_read_for_ownership_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<bus_in_use,proc_read,proc_write,memory,cache,modified,exclusive,shared,invalid>>
/\ UNCHANGED<<Fluent10_18, Fluent4_7, Fluent9_18, Fluent3_7>>
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
/\ UNCHANGED <<bus_in_use,proc_read,proc_write,cache>>
/\ Fluent4_7' = [Fluent4_7 EXCEPT ![v] = TRUE]
/\ UNCHANGED<<Fluent10_18, Fluent9_18, Fluent3_7>>
/\ CandSep'

complete_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ proc_write[c][a][v]
/\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
/\ bus_in_use' = FALSE
/\ UNCHANGED <<proc_read,memory,exclusive,shared>>
/\ UNCHANGED<<Fluent10_18, Fluent4_7, Fluent9_18, Fluent3_7>>
/\ CandSep'

proc_write_exclusive(c,a,v) ==
/\ exclusive[c][a]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ ~(bus_in_use)
/\ UNCHANGED <<bus_in_use,proc_read,proc_write,memory,invalid,shared>>
/\ UNCHANGED<<Fluent10_18, Fluent4_7, Fluent9_18, Fluent3_7>>
/\ CandSep'

issue_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ UNCHANGED <<proc_read,memory,cache,modified,exclusive,shared,invalid>>
/\ UNCHANGED<<Fluent10_18, Fluent4_7, Fluent9_18, Fluent3_7>>
/\ CandSep'

do_bus_upgrade(c,a) ==
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<bus_in_use,proc_read,proc_write,memory,cache,modified,exclusive>>
/\ UNCHANGED<<Fluent10_18, Fluent4_7, Fluent9_18, Fluent3_7>>
/\ CandSep'

complete_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ proc_write[c][a][v]
/\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
/\ bus_in_use' = FALSE
/\ UNCHANGED <<proc_read,memory,invalid,exclusive>>
/\ UNCHANGED<<Fluent10_18, Fluent4_7, Fluent9_18, Fluent3_7>>
/\ CandSep'

evict_modified(c,a) ==
/\ modified[c][a]
/\ memory' = [memory EXCEPT![a] = cache[c][a]]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ ~(bus_in_use)
/\ UNCHANGED <<bus_in_use,proc_read,proc_write,cache,exclusive,shared>>
/\ UNCHANGED<<Fluent10_18, Fluent4_7, Fluent9_18, Fluent3_7>>
/\ CandSep'

evict_exclusive_or_shared(c,a) ==
/\ (exclusive[c][a] \/ shared[c][a])
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ ~(bus_in_use)
/\ UNCHANGED <<bus_in_use,proc_read,proc_write,memory,cache,modified>>
/\ UNCHANGED<<Fluent10_18, Fluent4_7, Fluent9_18, Fluent3_7>>
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
