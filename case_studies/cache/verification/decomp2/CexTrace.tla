--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS a1, a2, Address, Value, v1, v2, c1, c2, Core

VARIABLES shared, cache, memory, err, Fluent117_1, Fluent116_1, invalid, exclusive, modified, cexTraceIdx

vars == <<shared, cache, memory, err, Fluent117_1, Fluent116_1, invalid, exclusive, modified, cexTraceIdx>>

NoErr == err = FALSE

CandSep == (\A var0 \in Address : (Fluent117_1[var0] => ~(Fluent116_1[var0])))

Init ==
/\ (memory \in [Address -> Value])
/\ (cache \in [Core -> [Address -> Value]])
/\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
/\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
/\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
/\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]
/\ Fluent117_1 = [x0 \in Address |-> FALSE]
/\ Fluent116_1 = [x0 \in Address |-> FALSE]
/\ cexTraceIdx = 0
/\ err = FALSE

issue_proc_read_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,exclusive,shared,invalid>>
/\ UNCHANGED <<Fluent117_1,Fluent116_1>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

do_bus_read_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,exclusive,shared,invalid>>
/\ UNCHANGED <<Fluent117_1,Fluent116_1>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

do_bus_read_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ cache[c][a] = v
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ (modified[c][a] => memory' = [memory EXCEPT![a] = v])
/\ (~(modified[c][a]) => memory' = memory)
/\ UNCHANGED <<cache,invalid>>
/\ UNCHANGED <<Fluent117_1,Fluent116_1>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

complete_proc_read_invalid_shared(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,modified,exclusive>>
/\ UNCHANGED <<Fluent117_1,Fluent116_1>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ invalid[c][a]
/\ memory[a] = v
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,modified,shared>>
/\ UNCHANGED <<Fluent117_1,Fluent116_1>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

issue_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,exclusive,shared,invalid>>
/\ Fluent117_1' = [Fluent117_1 EXCEPT![a] = FALSE]
/\ Fluent116_1' = [Fluent116_1 EXCEPT![a] = TRUE]
/\ UNCHANGED <<>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

do_bus_read_for_ownership_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,exclusive,shared,invalid>>
/\ Fluent116_1' = [Fluent116_1 EXCEPT![a] = FALSE]
/\ UNCHANGED <<Fluent117_1>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

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
/\ Fluent116_1' = [Fluent116_1 EXCEPT![a] = FALSE]
/\ UNCHANGED <<Fluent117_1>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

complete_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,exclusive,shared>>
/\ Fluent117_1' = [Fluent117_1 EXCEPT![a] = TRUE]
/\ UNCHANGED <<Fluent116_1>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

proc_write_exclusive(c,a,v) ==
/\ exclusive[c][a]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,invalid,shared>>
/\ UNCHANGED <<Fluent117_1,Fluent116_1>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

issue_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ UNCHANGED <<memory,cache,modified,exclusive,shared,invalid>>
/\ UNCHANGED <<Fluent117_1,Fluent116_1>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

do_bus_upgrade(c,a) ==
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<memory,cache,modified,exclusive>>
/\ UNCHANGED <<Fluent117_1,Fluent116_1>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

complete_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,invalid,exclusive>>
/\ UNCHANGED <<Fluent117_1,Fluent116_1>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

evict_modified(c,a) ==
/\ modified[c][a]
/\ memory' = [memory EXCEPT![a] = cache[c][a]]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<cache,exclusive,shared>>
/\ UNCHANGED <<Fluent117_1,Fluent116_1>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

evict_exclusive_or_shared(c,a) ==
/\ (exclusive[c][a] \/ shared[c][a])
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<memory,cache,modified>>
/\ UNCHANGED <<Fluent117_1,Fluent116_1>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

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

TraceConstraint ==
/\ cexTraceIdx = 0 => do_bus_read_invalid(c1,a1) /\ err' = err
/\ cexTraceIdx = 1 => issue_proc_read_invalid(c1,a2) /\ err' = err
/\ cexTraceIdx = 2 => do_bus_read_invalid(c2,a2) /\ err' = err
/\ cexTraceIdx = 3 => complete_proc_read_invalid_exclusive(c1,a2,v1) /\ err' = err
/\ cexTraceIdx = 4 => issue_proc_write_invalid(c2,a2,v2) /\ err' = err
/\ cexTraceIdx = 5 => do_bus_read_for_ownership_valid(c1,a2,v1) /\ err' = err
/\ cexTraceIdx = 6 => complete_proc_write_invalid(c2,a2,v2) /\ err' = err
/\ cexTraceIdx = 7 => issue_proc_read_invalid(c1,a2) /\ err' = err
/\ cexTraceIdx = 8 => do_bus_read_valid(c2,a2,v2) /\ err' = err
/\ cexTraceIdx = 9 => complete_proc_read_invalid_shared(c1,a1,v2) /\ err' = TRUE
/\ cexTraceIdx >= 10 => FALSE

InternalAction == UNCHANGED<<cexTraceIdx,err>>

TraceConstraintSpec == Init /\ [][Next /\ (TraceConstraint \/ InternalAction)]_vars
=============================================================================
