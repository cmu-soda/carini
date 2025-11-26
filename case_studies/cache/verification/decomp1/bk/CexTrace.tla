--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS a1, c3, a2, Address, Value, v1, v2, c1, c2, Core

VARIABLES cache, memory, err, invalid, modified, Fluent73_0, Fluent74_0, cexTraceIdx

vars == <<cache, memory, err, invalid, modified, Fluent73_0, Fluent74_0, cexTraceIdx>>

NoErr == err = FALSE

CandSep == (\A var0 \in Core : (Fluent74_0[var0] => Fluent73_0[var0]))

Init ==
/\ (memory \in [Address -> Value])
/\ (cache \in [Core -> [Address -> Value]])
/\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
/\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]
/\ Fluent73_0 = [x0 \in Core |-> FALSE]
/\ Fluent74_0 = [x0 \in Core |-> FALSE]
/\ cexTraceIdx = 0
/\ err = FALSE

issue_proc_read_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,invalid>>
/\ UNCHANGED <<Fluent73_0,Fluent74_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

do_bus_read_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,invalid>>
/\ UNCHANGED <<Fluent73_0,Fluent74_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

do_bus_read_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ cache[c][a] = v
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ (modified[c][a] => memory' = [memory EXCEPT![a] = v])
/\ (~(modified[c][a]) => memory' = memory)
/\ UNCHANGED <<cache,invalid>>
/\ UNCHANGED <<Fluent73_0,Fluent74_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

complete_proc_read_invalid_shared(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,modified>>
/\ UNCHANGED <<Fluent73_0,Fluent74_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ invalid[c][a]
/\ memory[a] = v
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,modified>>
/\ UNCHANGED <<Fluent73_0,Fluent74_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

issue_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,invalid>>
/\ Fluent73_0' = [Fluent73_0 EXCEPT![c] = TRUE]
/\ UNCHANGED <<Fluent74_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

do_bus_read_for_ownership_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,invalid>>
/\ Fluent73_0' = [Fluent73_0 EXCEPT![c] = TRUE]
/\ UNCHANGED <<Fluent74_0>>
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
/\ Fluent73_0' = [Fluent73_0 EXCEPT![c] = TRUE]
/\ UNCHANGED <<Fluent74_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

complete_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory>>
/\ Fluent74_0' = [x0 \in Core |-> Fluent73_0[c]]
/\ UNCHANGED <<Fluent73_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

proc_write_exclusive(c,a,v) ==
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,invalid>>
/\ UNCHANGED <<Fluent73_0,Fluent74_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

do_bus_upgrade(c,a) ==
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<memory,cache,modified>>
/\ UNCHANGED <<Fluent73_0,Fluent74_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

complete_proc_write_shared(c,a,v) ==
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,invalid>>
/\ UNCHANGED <<Fluent73_0,Fluent74_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

evict_modified(c,a) ==
/\ modified[c][a]
/\ memory' = [memory EXCEPT![a] = cache[c][a]]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<cache>>
/\ UNCHANGED <<Fluent73_0,Fluent74_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

evict_exclusive_or_shared(c,a) ==
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<memory,cache,modified>>
/\ UNCHANGED <<Fluent73_0,Fluent74_0>>
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
/\ cexTraceIdx = 0 => issue_proc_read_invalid(c3,a1) /\ err' = err
/\ cexTraceIdx = 1 => do_bus_read_invalid(c1,a1) /\ err' = err
/\ cexTraceIdx = 2 => do_bus_read_invalid(c3,a1) /\ err' = err
/\ cexTraceIdx = 3 => complete_proc_read_invalid_exclusive(c2,a1,v1) /\ err' = err
/\ cexTraceIdx = 4 => do_bus_read_invalid(c1,a1) /\ err' = err
/\ cexTraceIdx = 5 => complete_proc_read_invalid_exclusive(c1,a1,v1) /\ err' = err
/\ cexTraceIdx = 6 => proc_write_exclusive(c1,a1,v2) /\ err' = err
/\ cexTraceIdx = 7 => evict_modified(c1,a1) /\ err' = TRUE
/\ cexTraceIdx >= 8 => FALSE

InternalAction == UNCHANGED<<cexTraceIdx,err>>

TraceConstraintSpec == Init /\ [][Next /\ (TraceConstraint \/ InternalAction)]_vars
=============================================================================
