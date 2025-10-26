---- MODULE C1 ----

CONSTANTS Address, Core, Value

VARIABLES memory, cache, modified, invalid

vars == <<memory, cache, modified, invalid>>


Init ==
    /\ memory \in [Address -> Value]
    /\ cache \in [Core -> [Address -> Value]]
    /\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]

issue_proc_read_invalid(c, a) ==
    \* invalid(c, a) &
    /\ invalid[c][a]

    /\ UNCHANGED<<memory, cache, modified, invalid>>

do_bus_read_invalid(c, a) ==
    \* invalid(c, a) &
    /\ invalid[c][a]

    /\ UNCHANGED<<memory, cache, modified, invalid>>

do_bus_read_valid(c, a, v) ==
    \* !invalid(c, a) &
    /\ ~invalid[c][a]

    \* cache(c, a) = v &
    /\ cache[c][a] = v

    \* (forall C, A. new(modified(C, A)) <-> modified(C, A) & !(C = c & A = a)) &
    /\ modified' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : modified'[C][A] = (modified[C][A] /\ ~(C = c /\ A = a))

    \* (modified(c, a) ->  # write back
    \*   (forall A.
    \*      (A != a ->
    \*        (new(memory(A)) = memory(A)))) &
    \*    (new(memory(a)) = v)) &
    /\ modified[c][a] => memory' = [memory EXCEPT![a] = v]

    \* (!modified(c, a) ->
    \*   (forall A. new(memory(A)) = memory(A))) &
    /\ ~modified[c][a] => memory' = memory

    /\ UNCHANGED<<cache, invalid>>

complete_proc_read_invalid_shared(c, a, v) ==
    \* invalid(c, a) &
    /\ invalid[c][a]

    \* (forall C, A. new(invalid(C, A)) <-> invalid(C, A) & !(C = c & A = a)) &
    /\ invalid' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : invalid'[C][A] = (invalid[C][A] /\ ~(C = c /\ A = a))

    \* (forall C, A.
    \*   !(C = c & A = a) ->
    \*   (new(cache(C, A)) = cache(C, A))) &
    \* new(cache(c, a)) = v &
    /\ cache' = [cache EXCEPT![c][a] = v]

    /\ UNCHANGED<<memory, modified>>

complete_proc_read_invalid_exclusive(c, a, v) ==
    \* invalid(c, a) &
    /\ invalid[c][a]

    \* memory(a) = v &
    /\ memory[a] = v

    \* (forall C, A. new(invalid(C, A)) <-> invalid(C, A) & !(C = c & A = a)) &
    /\ invalid' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : invalid'[C][A] = (invalid[C][A] /\ ~(C = c /\ A = a))

    \* (forall C, A.
    \*    !(C = c & A = a) ->
    \*    (new(cache(C, A)) = cache(C, A))) &
    \* new(cache(c, a)) = v &
    /\ cache' = [cache EXCEPT![c][a] = v]

    /\ UNCHANGED<<memory, modified>>

issue_proc_write_invalid(c, a, v) ==
    \* invalid(c, a) &
    /\ invalid[c][a]

    /\ UNCHANGED<<memory, cache, modified, invalid>>

do_bus_read_for_ownership_invalid(c, a) ==
    \* invalid(c, a) &
    /\ invalid[c][a]

    /\ UNCHANGED<<memory, cache, modified, invalid>>

do_bus_read_for_ownership_valid(c, a, v) ==
    \* !invalid(c, a) &
    /\ ~invalid[c][a]

    \* cache(c, a) = v &
    /\ cache[c][a] = v

    \* (forall C, A. new(invalid(C, A)) <-> invalid(C, A) | C = c & A = a) &
    /\ invalid' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : invalid'[C][A] = (invalid[C][A] \/ (C = c /\ A = a))

    \* (forall C, A. new(modified(C, A)) <-> modified(C, A) & !(C = c & A = a)) &
    /\ modified' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : modified'[C][A] = (modified[C][A] /\ ~(C = c /\ A = a))

    \* (modified(c, a) ->  # write back
    \*   (forall A.
    \*      (A != a ->
    \*        (new(memory(A)) = memory(A)))) &
    \*    (new(memory(a)) = v)) &
    /\ modified[c][a] => memory' = [memory EXCEPT![a] = v]

    \* (!modified(c, a) ->
    \*   (forall A. new(memory(A)) = memory(A))) &
    /\ ~modified[c][a] => memory' = memory

    /\ UNCHANGED<<cache>>

complete_proc_write_invalid(c, a, v) ==
    \* invalid(c, a) &
    /\ invalid[c][a]

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

    /\ UNCHANGED<<memory>>

proc_write_exclusive(c, a, v) ==
    \* (forall C, A. new(modified(C, A)) <-> modified(C, A) | C = c & A = a) &
    /\ modified' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : modified'[C][A] = (modified[C][A] \/ (C = c /\ A = a))

    \* (forall C, A.
    \*    !(C = c & A = a) ->
    \*    (new(cache(C, A)) = cache(C, A))) &
    \* new(cache(c, a)) = v
    /\ cache' = [cache EXCEPT![c][a] = v]

    /\ UNCHANGED<<memory, invalid>>

do_bus_upgrade(c, a) ==
    \* (forall C, A. new(invalid(C, A)) <-> invalid(C, A) | C = c & A = a) &
    /\ invalid' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : invalid'[C][A] = (invalid[C][A] \/ (C = c /\ A = a))

    /\ UNCHANGED<<memory, cache, modified>>

complete_proc_write_shared(c, a, v) ==
    \* (forall C, A. new(modified(C, A)) <-> modified(C, A) | C = c & A = a) &
    /\ modified' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : modified'[C][A] = (modified[C][A] \/ (C = c /\ A = a))

    \* (forall C, A.
    \*    !(C = c & A = a) ->
    \*    (new(cache(C, A)) = cache(C, A))) &
    \* new(cache(c, a)) = v &
    /\ cache' = [cache EXCEPT![c][a] = v]

    /\ UNCHANGED<<memory, invalid>>

evict_modified(c, a) ==
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

    /\ UNCHANGED<<cache>>

evict_exclusive_or_shared(c, a) ==
    \* (forall C, A. new(invalid(C, A)) <-> invalid(C, A) | C = c & A = a)
    /\ invalid' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : invalid'[C][A] = (invalid[C][A] \/ (C = c /\ A = a))

    /\ UNCHANGED<<memory, cache, modified>>

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
        \*\/ issue_proc_write_shared(c,a,v)
        \/ do_bus_upgrade(c,a)
        \/ complete_proc_write_shared(c,a,v)
        \/ evict_modified(c,a)
        \/ evict_exclusive_or_shared(c,a)

Spec == Init /\ [][Next]_vars

\* safety !invalid(C, A) & !modified(C, A) -> cache(C, A) = memory(A)
Safety == \A C \in Core : \A A \in Address : (~invalid[C][A] /\ ~modified[C][A]) => cache[C][A] = memory[A]

======
