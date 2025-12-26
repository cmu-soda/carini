---- MODULE T1 ----

CONSTANTS Address, Core, Value

VARIABLES memory, cache, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer, bus_mode, upgrading, upgraded

vars == <<memory, cache, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer, bus_mode, upgrading, upgraded>>

CandSep ==
    /\ bus_mode # "bad"
    /\ \A C \in Core, A \in Address : upgraded[C][A] => upgrading[C][A]

Init ==
    /\ memory \in [Address -> Value]
    /\ cache \in [Core -> [Address -> Value]]
    /\ proc_read = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ proc_write = [c \in Core |-> [a \in Address |-> [v \in Value |-> FALSE]]]
    /\ bus_in_use = FALSE
    /\ bus_read = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ bus_read_for_ownership = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ bus_upgrade = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ bus_transfer = [v \in Value |-> FALSE]
    /\ bus_mode = "not_used"
    /\ upgrading = [C \in Core |-> [a \in Address |-> FALSE]]
    /\ upgraded = [C \in Core |-> [a \in Address |-> FALSE]]

issue_proc_read_invalid(c, a) ==
    /\ ~bus_in_use
    /\ bus_in_use' = TRUE
    /\ proc_read' = [proc_read EXCEPT![c][a] = TRUE]
    /\ bus_read' = [C \in Core |-> [A \in Address |-> bus_read[C][A] \/ (C # c /\ A = a)]]
    /\ UNCHANGED<<memory, cache, proc_write, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ UNCHANGED<<upgrading, upgraded>>
    /\ bus_mode' = IF bus_mode = "not_used" THEN "read" ELSE "bad"

do_bus_read_invalid(c, a) ==
    /\ bus_read[c][a]
    /\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, cache, proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ UNCHANGED<<bus_mode, upgrading, upgraded>>

do_bus_read_valid(c, a, v) ==
    /\ bus_read[c][a]
    /\ cache[c][a] = v
    /\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
    /\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
    /\ UNCHANGED<<memory, cache, proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade>>
    /\ UNCHANGED<<bus_mode, upgrading, upgraded>>

do_bus_read_modified(c, a, v) ==
    /\ bus_read[c][a]
    /\ cache[c][a] = v
    /\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
    /\ memory' = [memory EXCEPT![a] = v]
    /\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
    /\ UNCHANGED<<cache, proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade>>
    /\ UNCHANGED<<bus_mode, upgrading, upgraded>>

complete_proc_read_invalid_shared(c, a, v) ==
    /\ proc_read[c][a]
    /\ bus_transfer[v]
    /\ \A C \in Core : \A A \in Address : ~bus_read[C][A]
    /\ bus_transfer' = [V \in Value |-> FALSE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ bus_in_use' = FALSE
    /\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, proc_write, bus_read, bus_read_for_ownership, bus_upgrade>>
    /\ UNCHANGED<<upgrading, upgraded>>
    /\ bus_mode' = IF bus_mode = "read" THEN "not_used" ELSE "bad"

complete_proc_read_invalid_exclusive(c, a, v) ==
    /\ proc_read[c][a]
    /\ \A V \in Value : ~bus_transfer[V]
    /\ \A C \in Core : \A A \in Address : ~bus_read[C][A]
    /\ memory[a] = v
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ bus_in_use' = FALSE
    /\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, proc_write, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ UNCHANGED<<upgrading, upgraded>>
    /\ bus_mode' = IF bus_mode = "read" THEN "not_used" ELSE "bad"

issue_proc_write_invalid(c, a, v) ==
    /\ ~bus_in_use
    /\ bus_in_use' = TRUE
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
    /\ bus_read_for_ownership' = [C \in Core |-> [A \in Address |-> bus_read_for_ownership[C][A] \/ (C # c /\ A = a)]]
    /\ UNCHANGED<<memory, cache, proc_read, bus_read, bus_upgrade, bus_transfer>>
    /\ UNCHANGED<<upgrading, upgraded>>
    /\ bus_mode' = IF bus_mode = "not_used" THEN "write" ELSE "bad"

do_bus_read_for_ownership_invalid(c, a) ==
    /\ bus_read_for_ownership[c][a]
    /\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, cache, proc_read, proc_write, bus_in_use, bus_read, bus_upgrade, bus_transfer>>
    /\ UNCHANGED<<bus_mode, upgrading, upgraded>>

do_bus_read_for_ownership_valid(c, a, v) ==
    /\ bus_read_for_ownership[c][a]
    /\ cache[c][a] = v
    /\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
    /\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
    /\ UNCHANGED<<memory, cache, proc_read, proc_write, bus_in_use, bus_read, bus_upgrade>>
    /\ UNCHANGED<<bus_mode, upgrading, upgraded>>

do_bus_read_for_ownership_modified(c, a, v) ==
    /\ bus_read_for_ownership[c][a]
    /\ cache[c][a] = v
    /\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
    /\ memory' = [memory EXCEPT![a] = v]
    /\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
    /\ UNCHANGED<<cache, proc_read, proc_write, bus_in_use, bus_read, bus_upgrade>>
    /\ UNCHANGED<<bus_mode, upgrading, upgraded>>

complete_proc_write_invalid(c, a, v) ==
    /\ proc_write[c][a][v]
    /\ \A C \in Core : \A A \in Address : ~bus_read_for_ownership[C][A]
    /\ bus_transfer' = [V \in Value |-> FALSE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ bus_in_use' = FALSE
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
    /\ UNCHANGED<<memory, proc_read, bus_read, bus_read_for_ownership, bus_upgrade>>
    /\ UNCHANGED<<upgrading, upgraded>>
    /\ bus_mode' = IF bus_mode = "write" THEN "not_used" ELSE "bad"

proc_write_exclusive(c, a, v) ==
    /\ ~bus_in_use
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ UNCHANGED<<memory, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ UNCHANGED<<upgrading, upgraded>>
    /\ bus_mode' = IF bus_mode = "not_used" THEN "not_used" ELSE "bad"

issue_proc_write_shared(c, a, v) ==
    /\ ~bus_in_use
    /\ bus_in_use' = TRUE
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
    /\ bus_upgrade' = [C \in Core |-> [A \in Address |-> bus_upgrade[C][A] \/ (C # c /\ A = a)]]
    /\ UNCHANGED<<memory, cache, proc_read, bus_read, bus_read_for_ownership, bus_transfer>>
    /\ UNCHANGED<<upgraded>>
    /\ bus_mode' = IF bus_mode = "not_used" THEN "write" ELSE "bad"
    /\ upgrading' = [C \in Core |-> [A \in Address |-> upgrading[C][A] \/ (C # c /\ A = a)]]

do_bus_upgrade(c, a) ==
    /\ bus_upgrade[c][a]
    /\ bus_upgrade' = [bus_upgrade EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, cache, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_transfer>>
    /\ UNCHANGED<<bus_mode, upgrading>>
    /\ upgraded' = [upgraded EXCEPT![c][a] = TRUE]

complete_proc_write_shared(c, a, v) ==
    /\ proc_write[c][a][v]
    /\ \A C \in Core : \A A \in Address : ~bus_upgrade[C][A]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
    /\ bus_in_use' = FALSE
    /\ UNCHANGED<<memory, proc_read, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ bus_mode' = IF bus_mode = "write" THEN "not_used" ELSE "bad"
    /\ upgrading' = [upgrading EXCEPT![c][a] = FALSE]
    /\ upgraded' = [upgraded EXCEPT![c][a] = FALSE]

evict_modified(c, a) ==
    /\ ~bus_in_use
    /\ memory' = [memory EXCEPT![a] = cache[c][a]]
    /\ UNCHANGED<<cache, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ UNCHANGED<<upgrading, upgraded>>
    /\ bus_mode' = IF bus_mode = "not_used" THEN "not_used" ELSE "bad"

evict_exclusive_or_shared(c, a) ==
    /\ ~bus_in_use
    /\ UNCHANGED<<memory, cache, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ UNCHANGED<<upgrading, upgraded>>
    /\ bus_mode' = IF bus_mode = "not_used" THEN "not_used" ELSE "bad"

Next ==
    \E c \in Core : \E a \in Address : \E v \in Value :
        \/ issue_proc_read_invalid(c,a)
        \/ do_bus_read_invalid(c,a)
        \/ do_bus_read_valid(c,a,v)
        \/ do_bus_read_modified(c,a,v)
        \/ complete_proc_read_invalid_shared(c,a,v)
        \/ complete_proc_read_invalid_exclusive(c,a,v)
        \/ issue_proc_write_invalid(c,a,v)
        \/ do_bus_read_for_ownership_invalid(c,a)
        \/ do_bus_read_for_ownership_valid(c,a,v)
        \/ do_bus_read_for_ownership_modified(c,a,v)
        \/ complete_proc_write_invalid(c,a,v)
        \/ proc_write_exclusive(c,a,v)
        \/ issue_proc_write_shared(c,a,v)
        \/ do_bus_upgrade(c,a)
        \/ complete_proc_write_shared(c,a,v)
        \/ evict_modified(c,a)
        \/ evict_exclusive_or_shared(c,a)

Spec == Init /\ [][Next]_vars

======
