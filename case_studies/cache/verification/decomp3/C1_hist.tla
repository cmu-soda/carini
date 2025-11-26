--------------------------- MODULE C1_hist ---------------------------


CONSTANTS Address, Core, Value

VARIABLES shared, cache, memory, invalid, exclusive, modified, Fluent107_7, Fluent108_7

vars == <<shared, cache, memory, invalid, exclusive, modified, Fluent107_7, Fluent108_7>>

CandSep ==
\A var0 \in Value : (Fluent108_7[var0]) => (Fluent107_7[var0])

Init ==
/\ (memory \in [Address -> Value])
/\ (cache \in [Core -> [Address -> Value]])
/\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
/\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
/\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
/\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]
/\ Fluent107_7 = [ x0 \in Value |-> FALSE]
/\ Fluent108_7 = [ x0 \in Value |-> FALSE]

issue_proc_read_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,exclusive,shared,invalid>>
/\ Fluent107_7' = [x0 \in Value |-> FALSE]
/\ UNCHANGED<<Fluent108_7>>
/\ CandSep'

do_bus_read_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,exclusive,shared,invalid>>
/\ UNCHANGED<<Fluent107_7, Fluent108_7>>
/\ CandSep'

do_bus_read_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ cache[c][a] = v
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ (modified[c][a] => memory' = [memory EXCEPT![a] = v])
/\ (~(modified[c][a]) => memory' = memory)
/\ UNCHANGED <<cache,invalid>>
/\ Fluent107_7' = [Fluent107_7 EXCEPT ![v] = TRUE]
/\ Fluent108_7' = [Fluent108_7 EXCEPT ![v] = TRUE]
/\ UNCHANGED<<>>
/\ CandSep'

complete_proc_read_invalid_shared(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,modified,exclusive>>
/\ Fluent108_7' = [x0 \in Value |-> FALSE]
/\ UNCHANGED<<Fluent107_7>>
/\ CandSep'

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ invalid[c][a]
/\ memory[a] = v
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,modified,shared>>
/\ UNCHANGED<<Fluent107_7, Fluent108_7>>
/\ CandSep'

issue_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,exclusive,shared,invalid>>
/\ UNCHANGED<<Fluent107_7, Fluent108_7>>
/\ CandSep'

do_bus_read_for_ownership_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,exclusive,shared,invalid>>
/\ UNCHANGED<<Fluent107_7, Fluent108_7>>
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
/\ UNCHANGED <<cache>>
/\ UNCHANGED<<Fluent107_7, Fluent108_7>>
/\ CandSep'

complete_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,exclusive,shared>>
/\ UNCHANGED<<Fluent107_7, Fluent108_7>>
/\ CandSep'

proc_write_exclusive(c,a,v) ==
/\ exclusive[c][a]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,invalid,shared>>
/\ UNCHANGED<<Fluent107_7, Fluent108_7>>
/\ CandSep'

issue_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ UNCHANGED <<memory,cache,modified,exclusive,shared,invalid>>
/\ UNCHANGED<<Fluent107_7, Fluent108_7>>
/\ CandSep'

do_bus_upgrade(c,a) ==
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<memory,cache,modified,exclusive>>
/\ UNCHANGED<<Fluent107_7, Fluent108_7>>
/\ CandSep'

complete_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,invalid,exclusive>>
/\ UNCHANGED<<Fluent107_7, Fluent108_7>>
/\ CandSep'

evict_modified(c,a) ==
/\ modified[c][a]
/\ memory' = [memory EXCEPT![a] = cache[c][a]]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<cache,exclusive,shared>>
/\ UNCHANGED<<Fluent107_7, Fluent108_7>>
/\ CandSep'

evict_exclusive_or_shared(c,a) ==
/\ (exclusive[c][a] \/ shared[c][a])
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<memory,cache,modified>>
/\ UNCHANGED<<Fluent107_7, Fluent108_7>>
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
