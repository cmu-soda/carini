---- MODULE T1 ----

CONSTANTS Address, Core, Value

\* mutable relation exclusive(core, address)
\* mutable relation shared(core, address)
VARIABLES exclusive, shared

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

vars == <<exclusive, shared, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>


Init ==
    /\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ proc_read = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ proc_write = [c \in Core |-> [a \in Address |-> [v \in Value |-> FALSE]]]
    /\ bus_in_use = FALSE
    /\ bus_read = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ bus_read_for_ownership = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ bus_upgrade = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ bus_transfer = [v \in Value |-> FALSE]

issue_proc_read_invalid(c, a) ==
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

    /\ UNCHANGED<<exclusive, shared, proc_write, bus_read_for_ownership, bus_upgrade, bus_transfer>>

do_bus_read_invalid(c, a) ==
    \* bus_read(c, a) &
    /\ bus_read[c][a]

    \* (forall C, A. new(bus_read(C, A)) <-> bus_read(C, A) & !(C = c & A = a))
    /\ bus_read' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : bus_read'[C][A] = (bus_read[C][A] /\ ~(C = c /\ A = a))

    /\ UNCHANGED<<exclusive, shared, proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade, bus_transfer>>

do_bus_read_valid(c, a, v) ==
    \* bus_read(c, a) &
    /\ bus_read[c][a]

    \* (forall C, A. new(bus_read(C, A)) <-> bus_read(C, A) & !(C = c & A = a)) &
    /\ bus_read' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : bus_read'[C][A] = (bus_read[C][A] /\ ~(C = c /\ A = a))

    \* (forall C, A. new(shared(C, A)) <-> shared(C, A) | C = c & A = a) &
    /\ shared' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : shared'[C][A] = (shared[C][A] \/ (C = c /\ A = a))

    \* (forall C, A. new(exclusive(C, A)) <-> exclusive(C, A) & !(C = c & A = a)) &
    /\ exclusive' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : exclusive'[C][A] = (exclusive[C][A] /\ ~(C = c /\ A = a))

    \* (forall V. new(bus_transfer(V)) <-> bus_transfer(V) | V = v)
    /\ bus_transfer' \in [Value -> BOOLEAN]
    /\ \A V \in Value : bus_transfer'[V] = (bus_transfer[V] \/ (V = v))

    /\ UNCHANGED<<proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade>>

complete_proc_read_invalid_shared(c, a, v) ==
    \* proc_read(c, a) &
    /\ proc_read[c][a]

    \* bus_transfer(v) &
    /\ bus_transfer[v]

    \* (forall C, A. !bus_read(C, A)) &
    /\ \A C \in Core : \A A \in Address : ~bus_read[C][A]

    \* (forall V. !new(bus_transfer(V))) &
    /\ bus_transfer' = [V \in Value |-> FALSE]

    \* (forall C, A. new(shared(C, A)) <-> shared(C, A) | C = c & A = a) &
    /\ shared' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : shared'[C][A] = (shared[C][A] \/ (C = c /\ A = a))

    \* !new(bus_in_use) &
    /\ bus_in_use' = FALSE

    \* (forall C, A. new(proc_read(C, A)) <-> proc_read(C, A) & !(C = c & A = a))
    /\ proc_read' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : proc_read'[C][A] = (proc_read[C][A] /\ ~(C = c /\ A = a))

    /\ UNCHANGED<<exclusive, proc_write, bus_read, bus_read_for_ownership, bus_upgrade>>

complete_proc_read_invalid_exclusive(c, a, v) ==
    \* proc_read(c, a) &
    /\ proc_read[c][a]

    \* (forall V. !bus_transfer(V)) &
    /\ \A V \in Value : ~bus_transfer[V]

    \* (forall C, A. !bus_read(C, A)) &
    /\ \A C \in Core : \A A \in Address : ~bus_read[C][A]

    \* (forall C, A. new(exclusive(C, A)) <-> exclusive(C, A) | C = c & A = a) &
    /\ exclusive' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : exclusive'[C][A] = (exclusive[C][A] \/ (C = c /\ A = a))

    \* !new(bus_in_use) &
    /\ bus_in_use' = FALSE

    \* (forall C, A. new(proc_read(C, A)) <-> proc_read(C, A) & !(C = c & A = a))
    /\ proc_read' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : proc_read'[C][A] = (proc_read[C][A] /\ ~(C = c /\ A = a))

    /\ UNCHANGED<<shared, proc_write, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>

issue_proc_write_invalid(c, a, v) ==
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

    /\ UNCHANGED<<exclusive, shared, proc_read, bus_read, bus_upgrade, bus_transfer>>

do_bus_read_for_ownership_invalid(c, a) ==
    \* bus_read_for_ownership(c, a) &
    /\ bus_read_for_ownership[c][a]
    
    \* (forall C, A. new(bus_read_for_ownership(C, A)) <-> bus_read_for_ownership(C, A) & !(C = c & A = a))
    /\ bus_read_for_ownership' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : bus_read_for_ownership'[C][A] = (bus_read_for_ownership[C][A] /\ ~(C = c /\ A = a))

    /\ UNCHANGED<<exclusive, shared, proc_read, proc_write, bus_in_use, bus_read, bus_upgrade, bus_transfer>>

do_bus_read_for_ownership_valid(c, a, v) ==
    \* bus_read_for_ownership(c, a) &
    /\ bus_read_for_ownership[c][a]

    \* (forall C, A. new(bus_read_for_ownership(C, A)) <-> bus_read_for_ownership(C, A) & !(C = c & A = a)) &
    /\ bus_read_for_ownership' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : bus_read_for_ownership'[C][A] = (bus_read_for_ownership[C][A] /\ ~(C = c /\ A = a))

    \* (forall C, A. new(shared(C, A)) <-> shared(C, A) & !(C = c & A = a)) &
    /\ shared' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : shared'[C][A] = (shared[C][A] /\ ~(C = c /\ A = a))

    \* (forall C, A. new(exclusive(C, A)) <-> exclusive(C, A) & !(C = c & A = a)) &
    /\ exclusive' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : exclusive'[C][A] = (exclusive[C][A] /\ ~(C = c /\ A = a))

    \* (forall V. new(bus_transfer(V)) <-> bus_transfer(V) | V = v)
    /\ bus_transfer' \in [Value -> BOOLEAN]
    /\ \A V \in Value : bus_transfer'[V] = (bus_transfer[V] \/ (V = v))

    /\ UNCHANGED<<proc_read, proc_write, bus_in_use, bus_read, bus_upgrade>>

complete_proc_write_invalid(c, a, v) ==
    \* proc_write(c, a, v) &
    /\ proc_write[c][a][v]

    \* (forall C, A. !bus_read_for_ownership(C, A)) &
    /\ \A C \in Core : \A A \in Address : ~bus_read_for_ownership[C][A]

    \* (forall V. !new(bus_transfer(V))) &
    /\ bus_transfer' = [V \in Value |-> FALSE]

    \* !new(bus_in_use) &
    /\ bus_in_use' = FALSE

    \* (forall C, A, V. new(proc_write(C, A, V)) <-> proc_write(C, A, V) & !(C = c & A = a & V = v))
    /\ proc_write' \in [Core -> [Address -> [Value -> BOOLEAN]]]
    /\ \A C \in Core : \A A \in Address : \A V \in Value : proc_write'[C][A][V] = (proc_write[C][A][V] /\ ~(C = c /\ A = a /\ V = v))

    /\ UNCHANGED<<exclusive, shared, proc_read, bus_read, bus_read_for_ownership, bus_upgrade>>

proc_write_exclusive(c, a, v) ==
    \* exclusive(c, a) &
    /\ exclusive[c][a]

    \* !bus_in_use &
    /\ ~bus_in_use

    \* (forall C, A. new(exclusive(C, A)) <-> exclusive(C, A) & !(C = c & A = a)) &
    /\ exclusive' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : exclusive'[C][A] = (exclusive[C][A] /\ ~(C = c /\ A = a))

    /\ UNCHANGED<<shared, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>

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

    /\ UNCHANGED<<exclusive, shared, proc_read, bus_read, bus_read_for_ownership, bus_transfer>>

do_bus_upgrade(c, a) ==
    \* bus_upgrade(c, a) &
    /\ bus_upgrade[c][a]

    \* (forall C, A. new(bus_upgrade(C, A)) <-> bus_upgrade(C, A) & !(C = c & A = a)) &
    /\ bus_upgrade' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : bus_upgrade'[C][A] = (bus_upgrade[C][A] /\ ~(C = c /\ A = a))

    \* (forall C, A. new(shared(C, A)) <-> shared(C, A) & !(C = c & A = a))
    /\ shared' \in [Core -> [Address -> BOOLEAN]]
    /\ \A C \in Core : \A A \in Address : shared'[C][A] = (shared[C][A] /\ ~(C = c /\ A = a))

    /\ UNCHANGED<<exclusive, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_transfer>>

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

    \* (forall C, A, V. new(proc_write(C, A, V)) <-> proc_write(C, A, V) & !(C = c & A = a & V = v)) &
    /\ proc_write' \in [Core -> [Address -> [Value -> BOOLEAN]]]
    /\ \A C \in Core : \A A \in Address : \A V \in Value : proc_write'[C][A][V] = (proc_write[C][A][V] /\ ~(C = c /\ A = a /\ V = v))

    \* !new(bus_in_use)
    /\ bus_in_use' = FALSE

    /\ UNCHANGED<<exclusive, proc_read, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>

evict_modified(c, a) ==
    \* !bus_in_use &
    /\ ~bus_in_use

    /\ UNCHANGED<<exclusive, shared, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>

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

    /\ UNCHANGED<<proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>

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

======
