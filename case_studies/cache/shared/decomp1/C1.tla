---- MODULE C1 ----

CONSTANTS Address, Core, Value

VARIABLE memory, cache, modified, shared

vars == <<memory, cache, modified, shared>>


Init ==
    /\ memory \in [Address -> Value]
    /\ cache \in [Core -> [Address -> Value]]
    /\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ shared = [c \in Core |-> [a \in Address |-> FALSE]]

do_bus_read_valid(c, a, v) ==
    /\ cache[c][a] = v
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ modified[c][a] => memory' = [memory EXCEPT![a] = v]
    /\ ~modified[c][a] => memory' = memory
    /\ UNCHANGED<<cache>>

complete_proc_read_invalid_shared(c, a, v) ==
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ UNCHANGED<<memory, modified>>

complete_proc_read_invalid_exclusive(c, a, v) ==
    /\ memory[a] = v
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ UNCHANGED<<memory, modified, shared>>

do_bus_read_for_ownership_valid(c, a, v) ==
    /\ cache[c][a] = v
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ modified[c][a] => memory' = [memory EXCEPT![a] = v]
    /\ ~modified[c][a] => memory' = memory
    /\ UNCHANGED<<cache>>

complete_proc_write_invalid(c, a, v) ==
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ UNCHANGED<<memory, shared>>

proc_write_exclusive(c, a, v) ==
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ UNCHANGED<<memory, shared>>

issue_proc_write_shared(c, a, v) ==
    /\ shared[c][a]
    /\ UNCHANGED<<memory, cache, modified, shared>>

do_bus_upgrade(c, a) ==
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, cache, modified>>

complete_proc_write_shared(c, a, v) ==
    /\ shared[c][a]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ UNCHANGED<<memory>>

evict_modified(c, a) ==
    /\ modified[c][a]
    /\ memory' = [memory EXCEPT![a] = cache[c][a]]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<cache, shared>>

evict_exclusive(c, a) ==
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, cache, modified>>

evict_shared(c, a) ==
    /\ shared[c][a]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, cache, modified>>

Next ==
    \E c \in Core : \E a \in Address : \E v \in Value :
        \/ do_bus_read_valid(c,a,v)
        \/ complete_proc_read_invalid_shared(c,a,v)
        \/ complete_proc_read_invalid_exclusive(c,a,v)
        \/ do_bus_read_for_ownership_valid(c,a,v)
        \/ complete_proc_write_invalid(c,a,v)
        \/ proc_write_exclusive(c,a,v)
        \/ issue_proc_write_shared(c,a,v)
        \/ do_bus_upgrade(c,a)
        \/ complete_proc_write_shared(c,a,v)
        \/ evict_modified(c,a)
        \/ evict_exclusive(c,a)
        \/ evict_shared(c,a)

Spec == Init /\ [][Next]_vars

Safety == \A C \in Core : \A A \in Address : shared[C][A] => cache[C][A] = memory[A]

======
