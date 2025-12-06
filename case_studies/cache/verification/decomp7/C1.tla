---- MODULE C1 ----

CONSTANTS Address, Core, Value

VARIABLES memory, cache, modified, invalid, exclusive, shared, proc_read, proc_write

vars == <<memory, cache, modified, invalid, exclusive, shared, proc_read, proc_write>>


Init ==
    /\ memory \in [Address -> Value]
    /\ cache \in [Core -> [Address -> Value]]
    /\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]
    /\ proc_read = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ proc_write = [c \in Core |-> [a \in Address |-> [v \in Value |-> FALSE]]]

issue_proc_read_invalid(c, a) ==
    /\ invalid[c][a]
    /\ proc_read' = [proc_read EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<proc_write, memory, cache, modified, exclusive, shared, invalid>>

do_bus_read_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<proc_read, proc_write, memory, cache, modified, exclusive, shared, invalid>>

do_bus_read_valid(c, a, v) ==
    /\ ~invalid[c][a]
    /\ cache[c][a] = v
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ modified[c][a] => memory' = [memory EXCEPT![a] = v]
    /\ ~modified[c][a] => memory' = memory
    /\ UNCHANGED<<proc_read, proc_write, cache, invalid>>

complete_proc_read_invalid_shared(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ proc_read[c][a]
    /\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<proc_write, memory, modified, exclusive>>

complete_proc_read_invalid_exclusive(c, a, v) ==
    /\ invalid[c][a]
    /\ memory[a] = v
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ proc_read[c][a]
    /\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<proc_write, memory, modified, shared>>

issue_proc_write_invalid(c, a, v) ==
    /\ invalid[c][a]
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
    /\ UNCHANGED<<proc_read, memory, cache, modified, exclusive, shared, invalid>>

do_bus_read_for_ownership_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<proc_read, proc_write, memory, cache, modified, exclusive, shared, invalid>>

do_bus_read_for_ownership_valid(c, a, v) ==
    /\ ~invalid[c][a]
    /\ cache[c][a] = v
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ modified[c][a] => memory' = [memory EXCEPT![a] = v]
    /\ ~modified[c][a] => memory' = memory
    /\ UNCHANGED<<proc_read, proc_write, cache>>

complete_proc_write_invalid(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ proc_write[c][a][v]
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
    /\ UNCHANGED<<proc_read, memory, exclusive, shared>>

proc_write_exclusive(c, a, v) ==
    /\ exclusive[c][a]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ UNCHANGED<<proc_read, proc_write, memory, invalid, shared>>

issue_proc_write_shared(c, a, v) ==
    /\ shared[c][a]
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
    /\ UNCHANGED<<proc_read, memory, cache, modified, exclusive, shared, invalid>>

do_bus_upgrade(c, a) ==
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<proc_read, proc_write, memory, cache, modified, exclusive>>

complete_proc_write_shared(c, a, v) ==
    /\ shared[c][a]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ proc_write[c][a][v]
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
    /\ UNCHANGED<<proc_read, memory, invalid, exclusive>>

evict_modified(c, a) ==
    /\ modified[c][a]
    /\ memory' = [memory EXCEPT![a] = cache[c][a]]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<proc_read, proc_write, cache, exclusive, shared>>

evict_exclusive_or_shared(c, a) ==
    /\ exclusive[c][a] \/ shared[c][a]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<proc_read, proc_write, memory, cache, modified>>

Next ==
    \E c \in Core : \E a \in Address : \E v \in Value :
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

Spec == Init /\ [][Next]_vars

\* safety !invalid(C, A) & !modified(C, A) -> cache(C, A) = memory(A)
Safety == \A C \in Core : \A A \in Address : (~invalid[C][A] /\ ~modified[C][A]) => cache[C][A] = memory[A]

======
