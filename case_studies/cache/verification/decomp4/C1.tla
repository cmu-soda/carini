---- MODULE C1 ----

CONSTANTS Address, Core, Value

\* mutable function memory(address) : value
VARIABLE memory

\* mutable function cache(core, address) : value
VARIABLE cache

\* mutable relation modified(core, address)
\* mutable relation exclusive(core, address)
\* mutable relation shared(core, address)
\* mutable relation invalid(core, address)
VARIABLES modified, exclusive, shared, invalid

\* mutable relation bus_in_use()
VARIABLES bus_in_use

vars == <<memory, cache, modified, exclusive, shared, invalid, bus_in_use>>


Init ==
    /\ memory \in [Address -> Value]
    /\ cache \in [Core -> [Address -> Value]]
    /\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]
    /\ bus_in_use = FALSE

issue_proc_read_invalid(c, a) ==
    /\ invalid[c][a]
    /\ ~bus_in_use
    /\ bus_in_use' = TRUE
    /\ UNCHANGED<<memory, cache, modified, exclusive, shared, invalid>>

do_bus_read_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<memory, cache, modified, exclusive, shared, invalid, bus_in_use>>

do_bus_read_valid(c, a, v) ==
    /\ ~invalid[c][a]
    /\ cache[c][a] = v
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ modified[c][a] => memory' = [memory EXCEPT![a] = v]
    /\ ~modified[c][a] => memory' = memory
    /\ UNCHANGED<<cache, invalid, bus_in_use>>

complete_proc_read_invalid_shared(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ bus_in_use' = FALSE
    /\ UNCHANGED<<memory, modified, exclusive>>

complete_proc_read_invalid_exclusive(c, a, v) ==
    /\ invalid[c][a]
    /\ memory[a] = v
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ bus_in_use' = FALSE
    /\ UNCHANGED<<memory, modified, shared>>

issue_proc_write_invalid(c, a, v) ==
    /\ invalid[c][a]
    /\ ~bus_in_use
    /\ bus_in_use' = TRUE
    /\ UNCHANGED<<memory, cache, modified, exclusive, shared, invalid>>

do_bus_read_for_ownership_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<memory, cache, modified, exclusive, shared, invalid, bus_in_use>>

do_bus_read_for_ownership_valid(c, a, v) ==
    /\ ~invalid[c][a]
    /\ cache[c][a] = v
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ modified[c][a] => memory' = [memory EXCEPT![a] = v]
    /\ ~modified[c][a] => memory' = memory
    /\ UNCHANGED<<cache, bus_in_use>>

complete_proc_write_invalid(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ bus_in_use' = FALSE
    /\ UNCHANGED<<memory, exclusive, shared>>

proc_write_exclusive(c, a, v) ==
    /\ exclusive[c][a]
    /\ ~bus_in_use
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ UNCHANGED<<memory, shared, invalid, bus_in_use>>

issue_proc_write_shared(c, a, v) ==
    /\ shared[c][a]
    /\ ~bus_in_use
    /\ bus_in_use' = TRUE
    /\ UNCHANGED<<memory, cache, modified, exclusive, shared, invalid>>

do_bus_upgrade(c, a) ==
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, cache, modified, exclusive, bus_in_use>>

complete_proc_write_shared(c, a, v) ==
    /\ shared[c][a]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ bus_in_use' = FALSE
    /\ UNCHANGED<<memory, exclusive, invalid>>

evict_modified(c, a) ==
    /\ ~bus_in_use
    /\ modified[c][a]
    /\ memory' = [memory EXCEPT![a] = cache[c][a]]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<cache, exclusive, shared, bus_in_use>>

evict_exclusive_or_shared(c, a) ==
    /\ ~bus_in_use
    /\ exclusive[c][a] \/ shared[c][a]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<memory, cache, modified, bus_in_use>>

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
