--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS a1, c3, a2, Address, Value, v1, v2, c1, c2, Core

VARIABLES cache, memory, Fluent122_14, err, Fluent123_14, invalid, modified, cexTraceIdx

vars == <<cache, memory, Fluent122_14, err, Fluent123_14, invalid, modified, cexTraceIdx>>

NoErr == err = FALSE

CandSep == (\A var0 \in Address : (Fluent123_14[var0] => Fluent122_14[var0]))

Init ==
/\ (memory \in [Address -> Value])
/\ (cache \in [Core -> [Address -> Value]])
/\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
/\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]
/\ Fluent122_14 = [x0 \in Address |-> FALSE]
/\ Fluent123_14 = [x0 \in Address |-> FALSE]
/\ cexTraceIdx = 0
/\ err = FALSE

issue_proc_read_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,invalid>>
/\ Fluent122_14' = [Fluent122_14 EXCEPT![a] = TRUE]
/\ UNCHANGED <<Fluent123_14>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

do_bus_read_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,invalid>>
/\ UNCHANGED <<Fluent122_14,Fluent123_14>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

do_bus_read_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ cache[c][a] = v
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ (modified[c][a] => memory' = [memory EXCEPT![a] = v])
/\ (~(modified[c][a]) => memory' = memory)
/\ UNCHANGED <<cache,invalid>>
/\ Fluent123_14' = [Fluent123_14 EXCEPT![a] = TRUE]
/\ UNCHANGED <<Fluent122_14>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

complete_proc_read_invalid_shared(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,modified>>
/\ Fluent123_14' = [Fluent123_14 EXCEPT![a] = FALSE]
/\ UNCHANGED <<Fluent122_14>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ invalid[c][a]
/\ memory[a] = v
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,modified>>
/\ UNCHANGED <<Fluent122_14,Fluent123_14>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

issue_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,invalid>>
/\ UNCHANGED <<Fluent122_14,Fluent123_14>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

do_bus_read_for_ownership_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,invalid>>
/\ UNCHANGED <<Fluent122_14,Fluent123_14>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

do_bus_read_for_ownership_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ cache[c][a] = v
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ (modified[c][a] => memory' = [memory EXCEPT![a] = v])
/\ (~(modified[c][a]) => memory' = memory)
/\ UNCHANGED <<cache>>
/\ UNCHANGED <<Fluent122_14,Fluent123_14>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

complete_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory>>
/\ UNCHANGED <<Fluent122_14,Fluent123_14>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

proc_write_exclusive(c,a,v) ==
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,invalid>>
/\ Fluent122_14' = [Fluent122_14 EXCEPT![a] = FALSE]
/\ UNCHANGED <<Fluent123_14>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

do_bus_upgrade(c,a) ==
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<memory,cache,modified>>
/\ UNCHANGED <<Fluent122_14,Fluent123_14>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

complete_proc_write_shared(c,a,v) ==
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,invalid>>
/\ UNCHANGED <<Fluent122_14,Fluent123_14>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

evict_modified(c,a) ==
/\ modified[c][a]
/\ memory' = [memory EXCEPT![a] = cache[c][a]]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<cache>>
/\ UNCHANGED <<Fluent122_14,Fluent123_14>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

evict_exclusive_or_shared(c,a) ==
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<memory,cache,modified>>
/\ UNCHANGED <<Fluent122_14,Fluent123_14>>
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
\/ do_bus_upgrade(c,a)
\/ complete_proc_write_shared(c,a,v)
\/ evict_modified(c,a)
\/ evict_exclusive_or_shared(c,a)

Spec == (Init /\ [][Next]_vars)

Safety == (\A C \in Core : (\A A \in Address : ((~(invalid[C][A]) /\ ~(modified[C][A])) => cache[C][A] = memory[A])))

TraceConstraint ==
/\ cexTraceIdx = 0 => issue_proc_write_invalid(c1,a1,v1) /\ err' = err
/\ cexTraceIdx = 1 => issue_proc_read_invalid(c1,a1) /\ err' = err
/\ cexTraceIdx = 2 => issue_proc_read_invalid(c1,a2) /\ err' = err
/\ cexTraceIdx = 3 => do_bus_read_for_ownership_invalid(c2,a1) /\ err' = err
/\ cexTraceIdx = 4 => do_bus_read_for_ownership_invalid(c3,a1) /\ err' = err
/\ cexTraceIdx = 5 => complete_proc_write_invalid(c1,a1,v2) /\ err' = err
/\ cexTraceIdx = 6 => do_bus_read_valid(c1,a1,v2) /\ err' = err
/\ cexTraceIdx = 7 => complete_proc_read_invalid_shared(c1,a2,v2) /\ err' = TRUE
/\ cexTraceIdx >= 8 => FALSE

InternalAction == UNCHANGED<<cexTraceIdx,err>>

TraceConstraintSpec == Init /\ [][Next /\ (TraceConstraint \/ InternalAction)]_vars
=============================================================================
