---- MODULE C1 ----

CONSTANTS Address, Core, Value

VARIABLES memory, cache, modified, exclusive

vars == <<memory, cache, modified, exclusive>>


Init ==
    /\ memory \in [Address -> Value]
    /\ cache \in [Core -> [Address -> Value]]
    /\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]

do_bus_read_valid(c, a, v) ==
    /\ cache[c][a] = v
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ modified[c][a] => memory' = [memory EXCEPT![a] = v]
    /\ ~modified[c][a] => memory' = memory
    /\ UNCHANGED<<cache>>

complete_proc_read_invalid_shared(c, a, v) ==
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ UNCHANGED<<memory, modified, exclusive>>

complete_proc_read_invalid_exclusive(c, a, v) ==
    /\ memory[a] = v
    /\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ UNCHANGED<<memory, modified>>

do_bus_read_for_ownership_valid(c, a, v) ==
    /\ cache[c][a] = v
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ modified[c][a] => memory' = [memory EXCEPT![a] = v]
    /\ ~modified[c][a] => memory' = memory
    /\ UNCHANGED<<cache>>

complete_proc_write_invalid(c, a, v) ==
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ UNCHANGED<<memory, exclusive>>

proc_write_exclusive(c, a, v) ==
    /\ exclusive[c][a]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ UNCHANGED<<memory>>

complete_proc_write_shared(c, a, v) ==
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ UNCHANGED<<memory, exclusive>>

evict_modified(c, a) ==
    /\ modified[c][a]
    /\ memory' = [memory EXCEPT![a] = cache[c][a]]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<cache, exclusive>>

evict_exclusive(c, a) ==
    /\ exclusive[c][a]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, cache, modified>>

evict_shared(c, a) ==
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, cache, modified>>

Next ==
    \E c \in Core : \E a \in Address : \E v \in Value :
        \/ do_bus_read_valid(c,a,v)
        \/ complete_proc_read_invalid_shared(c,a,v)
        \/ complete_proc_read_invalid_exclusive(c,a,v)
        \/ do_bus_read_for_ownership_valid(c,a,v)
        \/ complete_proc_write_invalid(c,a,v)
        \/ proc_write_exclusive(c,a,v)
        \/ complete_proc_write_shared(c,a,v)
        \/ evict_modified(c,a)
        \/ evict_exclusive(c,a)
        \/ evict_shared(c,a)

Spec == Init /\ [][Next]_vars

Safety == \A C \in Core : \A A \in Address : exclusive[C][A] => cache[C][A] = memory[A]

======
