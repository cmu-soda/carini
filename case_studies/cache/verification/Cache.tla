---- MODULE Cache ----

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

\* mutable relation proc_read(core, address)
\* mutable relation proc_write(core, address, value)
VARIABLES proc_read, proc_write

\* mutable relation bus_in_use()
VARIABLES bus_in_use

\* mutable relation bus_read(core, address)
\* mutable relation bus_read_for_ownership(core, address)
\* mutable relation bus_upgrade(core, address)
VARIABLES bus_read, bus_read_for_ownership, bus_upgrade

\* mutable relation bus_transfer(value)
VARIABLE bus_transfer

vars == <<memory, cache, modified, exclusive, shared, invalid, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>


Init ==
    /\ memory \in [Address -> Value]
    /\ cache \in [Core -> [Address -> Value]]
    /\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]
    /\ proc_read = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ proc_write = [c \in Core |-> [a \in Address |-> [v \in Value |-> FALSE]]]
    /\ bus_in_use = FALSE
    /\ bus_read = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ bus_read_for_ownership = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ bus_upgrade = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ bus_transfer = [v \in Value |-> FALSE]

issue_proc_read_invalid(c, a) ==
    \* invalid(c, a) &
    /\ invalid[c][a]

    \* !bus_in_use &
    /\ ~bus_in_use

    \* new(bus_in_use) &
    /\ bus_in_use' = TRUE
    
    \* (forall C, A. new(proc_read(C, A)) <-> proc_read(C, A) | C = c & A = a) &
    /\ proc_read' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : proc_read'[C][A] = (proc_read[C][A] \/ (C = c /\ A = a))

    \* (forall C, A. new(bus_read(C, A)) <-> bus_read(C,A) | C != c & A = a)
    /\ bus_read' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : bus_read'[C][A] = (bus_read[C][A] \/ (C # c /\ A = a))

    /\ UNCHANGED<<memory, cache, modified, exclusive, shared, invalid, proc_write, bus_read_for_ownership, bus_upgrade, bus_transfer>>

do_bus_read_invalid(c, a) ==
    \* bus_read(c, a) &
    /\ bus_read[c][a]

    \* invalid(c, a) &
    /\ invalid[c][a]

    \* (forall C, A. new(bus_read(C, A)) <-> bus_read(C, A) & !(C = c & A = a))
    /\ bus_read' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : bus_read'[C][A] = (bus_read[C][A] /\ ~(C = c /\ A = a))

    /\ UNCHANGED<<memory, cache, modified, exclusive, shared, invalid, proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade, bus_transfer>>

do_bus_read_valid(c, a, v) ==
    \* bus_read(c, a) &
    /\ bus_read[c][a]

    \* !invalid(c, a) &
    /\ ~invalid[c][a]

    \* cache(c, a) = v &
    /\ cache[c][a] = v

    \* (forall C, A. new(bus_read(C, A)) <-> bus_read(C, A) & !(C = c & A = a)) &
    /\ bus_read' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : bus_read'[C][A] = (bus_read[C][A] /\ ~(C = c /\ A = a))

    \* (forall C, A. new(shared(C, A)) <-> shared(C, A) | C = c & A = a) &
    /\ shared' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : shared'[C][A] = (shared[C][A] \/ (C = c /\ A = a))

    \* (forall C, A. new(modified(C, A)) <-> modified(C, A) & !(C = c & A = a)) &
    /\ modified' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : modified'[C][A] = (modified[C][A] /\ ~(C = c /\ A = a))

    \* (forall C, A. new(exclusive(C, A)) <-> exclusive(C, A) & !(C = c & A = a)) &
    /\ exclusive' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : exclusive'[C][A] = (exclusive[C][A] /\ ~(C = c /\ A = a))

    \* (modified(c, a) ->  # write back
    \*   (forall A.
    \*      (A != a ->
    \*        (new(memory(A)) = memory(A)))) &
    \*    (new(memory(a)) = v)) &
    /\ modified[c][a] => memory' = [memory EXCEPT![a] = v]

    \* (!modified(c, a) ->
    \*   (forall A. new(memory(A)) = memory(A))) &
    /\ ~modified[c][a] => memory' = memory

    \* (forall V. new(bus_transfer(V)) <-> bus_transfer(V) | V = v)
    /\ bus_transfer' \in [Value -> BOOLEAN]
    /\ \A V \in Value : bus_transfer'[V] = (bus_transfer[V] \/ (V = v))

    /\ UNCHANGED<<cache, invalid, proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade>>

complete_proc_read_invalid_shared(c, a, v) ==
    \* invalid(c, a) &
    /\ invalid[c][a]

    \* proc_read(c, a) &
    /\ proc_read[c][a]

    \* bus_transfer(v) &
    /\ bus_transfer[v]

    \* (forall C, A. !bus_read(C, A)) &
    /\ \A C \in Core : \A A \in Address : ~bus_read[C][A]

    \* (forall V. !new(bus_transfer(V))) &
    /\ bus_transfer' = [V \in Value |-> FALSE]

    \* (forall C, A. new(invalid(C, A)) <-> invalid(C, A) & !(C = c & A = a)) &
    /\ invalid' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : invalid'[C][A] = (invalid[C][A] /\ ~(C = c /\ A = a))

    \* (forall C, A. new(shared(C, A)) <-> shared(C, A) | C = c & A = a) &
    /\ shared' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : shared'[C][A] = (shared[C][A] \/ (C = c /\ A = a))

    \* (forall C, A.
    \*   !(C = c & A = a) ->
    \*   (new(cache(C, A)) = cache(C, A))) &
    \* new(cache(c, a)) = v &
    /\ cache' = [cache EXCEPT![c][a] = v]

    \* !new(bus_in_use) &
    /\ bus_in_use' = FALSE

    \* (forall C, A. new(proc_read(C, A)) <-> proc_read(C, A) & !(C = c & A = a))
    /\ proc_read' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : proc_read'[C][A] = (proc_read[C][A] /\ ~(C = c /\ A = a))

    /\ UNCHANGED<<memory, modified, exclusive, proc_write, bus_read, bus_read_for_ownership, bus_upgrade>>

complete_proc_read_invalid_exclusive(c, a, v) ==
    \* invalid(c, a) &
    /\ invalid[c][a]

    \* proc_read(c, a) &
    /\ proc_read[c][a]

    \* (forall V. !bus_transfer(V)) &
    /\ \A V \in Value : ~bus_transfer[V]

    \* (forall C, A. !bus_read(C, A)) &
    /\ \A C \in Core : \A A \in Address : ~bus_read[C][A]

    \* memory(a) = v &
    /\ memory[a] = v

    \* (forall C, A. new(invalid(C, A)) <-> invalid(C, A) & !(C = c & A = a)) &
    /\ invalid' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : invalid'[C][A] = (invalid[C][A] /\ ~(C = c /\ A = a))

    \* (forall C, A. new(exclusive(C, A)) <-> exclusive(C, A) | C = c & A = a) &
    /\ exclusive' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : exclusive'[C][A] = (exclusive[C][A] \/ (C = c /\ A = a))

    \* (forall C, A.
    \*    !(C = c & A = a) ->
    \*    (new(cache(C, A)) = cache(C, A))) &
    \* new(cache(c, a)) = v &
    /\ cache' = [cache EXCEPT![c][a] = v]

    \* !new(bus_in_use) &
    /\ bus_in_use' = FALSE

    \* (forall C, A. new(proc_read(C, A)) <-> proc_read(C, A) & !(C = c & A = a))
    /\ proc_read' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : proc_read'[C][A] = (proc_read[C][A] /\ ~(C = c /\ A = a))

    /\ UNCHANGED<<memory, modified, shared, proc_write, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>

issue_proc_write_invalid(c, a, v) ==
    \* invalid(c, a) &
    /\ invalid[c][a]

    \* !bus_in_use &
    /\ ~bus_in_use

    \* new(bus_in_use) &
    /\ bus_in_use' = TRUE

    \* (forall C, A, V. new(proc_write(C, A, V)) <-> proc_write(C, A, V) | C = c & A = a & V = v) &
    /\ proc_write' \in [Core -> [Address -> [Value -> BOOLEAN]]]
    /\ \A C \in Core : \A A \in Address : \A V \in Value : proc_write'[C][A][V] = (proc_write[C][A][V] \/ (C = c /\ A = a /\ V = v))

    \* (forall C, A. new(bus_read_for_ownership(C, A)) <-> bus_read_for_ownership(C,A) | C != c & A = a)
    /\ bus_read_for_ownership' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : bus_read_for_ownership'[C][A] = (bus_read_for_ownership[C][A] \/ (C # c /\ A = a))

    /\ UNCHANGED<<memory, cache, modified, exclusive, shared, invalid, proc_read, bus_read, bus_upgrade, bus_transfer>>

do_bus_read_for_ownership_invalid(c, a) ==
    \* bus_read_for_ownership(c, a) &
    /\ bus_read_for_ownership[c][a]
    
    \* invalid(c, a) &
    /\ invalid[c][a]

    \* (forall C, A. new(bus_read_for_ownership(C, A)) <-> bus_read_for_ownership(C, A) & !(C = c & A = a))
    /\ bus_read_for_ownership' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : bus_read_for_ownership'[C][A] = (bus_read_for_ownership[C][A] /\ ~(C = c /\ A = a))

    /\ UNCHANGED<<memory, cache, modified, exclusive, shared, invalid, proc_read, proc_write, bus_in_use, bus_read, bus_upgrade, bus_transfer>>

do_bus_read_for_ownership_valid(c, a, v) ==
    \* bus_read_for_ownership(c, a) &
    /\ bus_read_for_ownership[c][a]

    \* !invalid(c, a) &
    /\ ~invalid[c][a]

    \* cache(c, a) = v &
    /\ cache[c][a] = v

    \* (forall C, A. new(bus_read_for_ownership(C, A)) <-> bus_read_for_ownership(C, A) & !(C = c & A = a)) &
    /\ bus_read_for_ownership' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : bus_read_for_ownership'[C][A] = (bus_read_for_ownership[C][A] /\ ~(C = c /\ A = a))

    \* (forall C, A. new(invalid(C, A)) <-> invalid(C, A) | C = c & A = a) &
    /\ invalid' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : invalid'[C][A] = (invalid[C][A] \/ (C = c /\ A = a))

    \* (forall C, A. new(shared(C, A)) <-> shared(C, A) & !(C = c & A = a)) &
    /\ shared' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : shared'[C][A] = (shared[C][A] /\ ~(C = c /\ A = a))

    \* (forall C, A. new(modified(C, A)) <-> modified(C, A) & !(C = c & A = a)) &
    /\ modified' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : modified'[C][A] = (modified[C][A] /\ ~(C = c /\ A = a))

    \* (forall C, A. new(exclusive(C, A)) <-> exclusive(C, A) & !(C = c & A = a)) &
    /\ exclusive' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : exclusive'[C][A] = (exclusive[C][A] /\ ~(C = c /\ A = a))

    \* (modified(c, a) ->  # write back
    \*   (forall A.
    \*      (A != a ->
    \*        (new(memory(A)) = memory(A)))) &
    \*    (new(memory(a)) = v)) &
    /\ modified[c][a] => memory' = [memory EXCEPT![a] = v]

    \* (!modified(c, a) ->
    \*   (forall A. new(memory(A)) = memory(A))) &
    /\ ~modified[c][a] => memory' = memory

    \* (forall V. new(bus_transfer(V)) <-> bus_transfer(V) | V = v)
    /\ bus_transfer' \in [Value -> BOOLEAN]
    /\ \A V \in Value : bus_transfer'[V] = (bus_transfer[V] \/ (V = v))

    /\ UNCHANGED<<cache, proc_read, proc_write, bus_in_use, bus_read, bus_upgrade>>

complete_proc_write_invalid(c, a, v) ==
    \* invalid(c, a) &
    /\ invalid[c][a]

    \* proc_write(c, a, v) &
    /\ proc_write[c][a][v]

    \* (forall C, A. !bus_read_for_ownership(C, A)) &
    /\ \A C \in Core : \A A \in Address : ~bus_read_for_ownership[C][A]

    \* (forall V. !new(bus_transfer(V))) &
    /\ bus_transfer' = [V \in Value |-> FALSE]

    \* (forall C, A. new(invalid(C, A)) <-> invalid(C, A) & !(C = c & A = a)) &
    /\ invalid' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : invalid'[C][A] = (invalid[C][A] /\ ~(C = c /\ A = a))

    \* (forall C, A. new(modified(C, A)) <-> modified(C, A) | C = c & A = a) &
    /\ modified' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : modified'[C][A] = (modified[C][A] \/ (C = c /\ A = a))

    \* (forall C, A.
    \*    !(C = c & A = a) ->
    \*    (new(cache(C, A)) = cache(C, A))) &
    \* new(cache(c, a)) = v &
    /\ cache' = [cache EXCEPT![c][a] = v]

    \* !new(bus_in_use) &
    /\ bus_in_use' = FALSE

    \* (forall C, A, V. new(proc_write(C, A, V)) <-> proc_write(C, A, V) & !(C = c & A = a & V = v))
    /\ proc_write' \in [Core -> [Address -> [Value -> BOOLEAN]]]
    /\ \A C \in Core : \A A \in Address : \A V \in Value : proc_write'[C][A][V] = (proc_write[C][A][V] /\ ~(C = c /\ A = a /\ V = v))

    /\ UNCHANGED<<memory, exclusive, shared, proc_read, bus_read, bus_read_for_ownership, bus_upgrade>>

proc_write_exclusive(c, a, v) ==
    \* exclusive(c, a) &
    /\ exclusive[c][a]

    \* !bus_in_use &
    /\ ~bus_in_use

    \* (forall C, A. new(exclusive(C, A)) <-> exclusive(C, A) & !(C = c & A = a)) &
    /\ exclusive' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : exclusive'[C][A] = (exclusive[C][A] /\ ~(C = c /\ A = a))

    \* (forall C, A. new(modified(C, A)) <-> modified(C, A) | C = c & A = a) &
    /\ modified' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : modified'[C][A] = (modified[C][A] \/ (C = c /\ A = a))

    \* (forall C, A.
    \*    !(C = c & A = a) ->
    \*    (new(cache(C, A)) = cache(C, A))) &
    \* new(cache(c, a)) = v
    /\ cache' = [cache EXCEPT![c][a] = v]

    /\ UNCHANGED<<memory, shared, invalid, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>

issue_proc_write_shared(c, a, v) ==
    \* shared(c, a) &
    /\ shared[c][a]

    \* !bus_in_use &
    /\ ~bus_in_use

    \* new(bus_in_use) &
    /\ bus_in_use' = TRUE

    \* (forall C, A, V. new(proc_write(C, A, V)) <-> proc_write(C, A, V) | C = c & A = a & V = v) &
    /\ proc_write' \in [Core -> [Address -> [Value -> BOOLEAN]]]
    /\ \A C \in Core : \A A \in Address : \A V \in Value : proc_write'[C][A][V] = (proc_write[C][A][V] \/ (C = c /\ A = a /\ V = v))

    \* (forall C, A. new(bus_upgrade(C, A)) <-> bus_upgrade(C,A) | C != c & A = a)
    /\ bus_upgrade' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : bus_upgrade'[C][A] = (bus_upgrade[C][A] \/ (C # c /\ A = a))

    /\ UNCHANGED<<memory, cache, modified, exclusive, shared, invalid, proc_read, bus_read, bus_read_for_ownership, bus_transfer>>

do_bus_upgrade(c, a) ==
    \* bus_upgrade(c, a) &
    /\ bus_upgrade[c][a]

    \* (forall C, A. new(bus_upgrade(C, A)) <-> bus_upgrade(C, A) & !(C = c & A = a)) &
    /\ bus_upgrade' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : bus_upgrade'[C][A] = (bus_upgrade[C][A] /\ ~(C = c /\ A = a))

    \* (forall C, A. new(invalid(C, A)) <-> invalid(C, A) | C = c & A = a) &
    /\ invalid' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : invalid'[C][A] = (invalid[C][A] \/ (C = c /\ A = a))

    \* (forall C, A. new(shared(C, A)) <-> shared(C, A) & !(C = c & A = a))
    /\ shared' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : shared'[C][A] = (shared[C][A] /\ ~(C = c /\ A = a))

    /\ UNCHANGED<<memory, cache, modified, exclusive, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_transfer>>

complete_proc_write_shared(c, a, v) ==
    \* shared(c, a) &
    /\ shared[c][a]

    \* proc_write(c, a, v) &
    /\ proc_write[c][a][v]

    \* (forall C, A. !bus_upgrade(C, A)) &
    /\ \A C \in Core : \A A \in Address : ~bus_upgrade[C][A]

    \* (forall C, A. new(shared(C, A)) <-> shared(C, A) & !(C = c & A = a)) &
    /\ shared' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : shared'[C][A] = (shared[C][A] /\ ~(C = c /\ A = a))

    \* (forall C, A. new(modified(C, A)) <-> modified(C, A) | C = c & A = a) &
    /\ modified' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : modified'[C][A] = (modified[C][A] \/ (C = c /\ A = a))

    \* (forall C, A.
    \*    !(C = c & A = a) ->
    \*    (new(cache(C, A)) = cache(C, A))) &
    \* new(cache(c, a)) = v &
    /\ cache' = [cache EXCEPT![c][a] = v]

    \* (forall C, A, V. new(proc_write(C, A, V)) <-> proc_write(C, A, V) & !(C = c & A = a & V = v)) &
    /\ proc_write' \in [Core -> [Address -> [Value -> BOOLEAN]]]
    /\ \A C \in Core : \A A \in Address : \A V \in Value : proc_write'[C][A][V] = (proc_write[C][A][V] /\ ~(C = c /\ A = a /\ V = v))

    \* !new(bus_in_use)
    /\ bus_in_use' = FALSE

    /\ UNCHANGED<<memory, exclusive, invalid, proc_read, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>

evict_modified(c, a) ==
    \* !bus_in_use &
    /\ ~bus_in_use

    \* modified(c, a) &
    /\ modified[c][a]

    \* (forall A.
    \*   (A != a ->
    \*    (new(memory(A)) = memory(A)))) &
    \* new(memory(a)) = cache(c, a) &  # write back
    /\ memory' = [memory EXCEPT![a] = cache[c][a]]

    \* (forall C, A. new(modified(C, A)) <-> modified(C, A) & !(C = c & A = a)) &
    /\ modified' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : modified'[C][A] = (modified[C][A] /\ ~(C = c /\ A = a))

    \* (forall C, A. new(invalid(C, A)) <-> invalid(C, A) | C = c & A = a)
    /\ invalid' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : invalid'[C][A] = (invalid[C][A] \/ (C = c /\ A = a))

    /\ UNCHANGED<<cache, exclusive, shared, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>

evict_exclusive_or_shared(c, a) ==
    \* !bus_in_use &
    /\ ~bus_in_use

    \* (exclusive(c, a) | shared(c, a)) &
    /\ exclusive[c][a] \/ shared[c][a]

    \* (forall C, A. new(exclusive(C, A)) <-> exclusive(C, A) & !(C = c & A = a)) &
    /\ exclusive' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : exclusive'[C][A] = (exclusive[C][A] /\ ~(C = c /\ A = a))

    \* (forall C, A. new(shared(C, A)) <-> shared(C, A) & !(C = c & A = a)) &
    /\ shared' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : shared'[C][A] = (shared[C][A] /\ ~(C = c /\ A = a))

    \* (forall C, A. new(invalid(C, A)) <-> invalid(C, A) | C = c & A = a)
    /\ invalid' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : invalid'[C][A] = (invalid[C][A] \/ (C = c /\ A = a))

    /\ UNCHANGED<<memory, cache, modified, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>

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
