---- MODULE T1 ----

CONSTANTS Address, Core, Value

VARIABLES memory, cache, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer,
    good, in_read, in_write, issue_core, issue_addr, read_snoop, ownership_snoop, upgrade_snoop, transfer

vars == <<memory, cache, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer,
    good, in_read, in_write, issue_core, issue_addr, read_snoop, ownership_snoop, upgrade_snoop, transfer>>

CandSep ==
    /\ good

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

    /\ good = TRUE
    /\ in_read = FALSE
    /\ in_write = FALSE
    /\ issue_core \in Core
    /\ issue_addr \in Address
    /\ read_snoop = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ ownership_snoop = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ upgrade_snoop = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ transfer = FALSE

issue_proc_read_invalid(c, a) ==
    /\ ~bus_in_use
    /\ bus_in_use' = TRUE
    /\ proc_read' = [proc_read EXCEPT![c][a] = TRUE]
    /\ bus_read' = [C \in Core |-> [A \in Address |-> bus_read[C][A] \/ (C # c /\ A = a)]]
    /\ UNCHANGED<<memory, cache, proc_write, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ in_read' = TRUE
    /\ issue_core' = c
    /\ issue_addr' = a
    /\ read_snoop' = [C \in Core |-> [A \in Address |-> (read_snoop[C][A] \/ (C # c /\ A = a))]] \* all other cores snoop on the read
    /\ good' = ~in_read /\ ~in_write \* multiple issues cannot happen concurrently
    /\ UNCHANGED<<in_write, ownership_snoop, upgrade_snoop, transfer>>

do_bus_read_invalid(c, a) ==
    /\ bus_read[c][a]
    /\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, cache, proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ read_snoop' = [read_snoop EXCEPT![c][a] = FALSE]
    /\ good' = read_snoop[c][a]
    /\ UNCHANGED<<in_read, in_write, issue_core, issue_addr, ownership_snoop, upgrade_snoop, transfer>>

do_bus_read_valid(c, a, v) ==
    /\ bus_read[c][a]
    /\ cache[c][a] = v
    /\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
    /\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
    /\ UNCHANGED<<memory, cache, proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade>>
    /\ read_snoop' = [read_snoop EXCEPT![c][a] = FALSE]
    /\ good' = read_snoop[c][a]
    /\ transfer' = TRUE
    /\ UNCHANGED<<in_read, in_write, issue_core, issue_addr, ownership_snoop, upgrade_snoop>>

do_bus_read_modified(c, a, v) ==
    /\ bus_read[c][a]
    /\ cache[c][a] = v
    /\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
    /\ memory' = [memory EXCEPT![a] = v]
    /\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
    /\ UNCHANGED<<cache, proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade>>
    /\ read_snoop' = [read_snoop EXCEPT![c][a] = FALSE]
    /\ good' = read_snoop[c][a]
    /\ transfer' = TRUE
    /\ UNCHANGED<<in_read, in_write, issue_core, issue_addr, ownership_snoop, upgrade_snoop>>

complete_proc_read_invalid_shared(c, a, v) ==
    /\ proc_read[c][a]
    /\ bus_transfer[v]
    /\ \A C \in Core : \A A \in Address : ~bus_read[C][A]
    /\ bus_transfer' = [V \in Value |-> FALSE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ bus_in_use' = FALSE
    /\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, proc_write, bus_read, bus_read_for_ownership, bus_upgrade>>
    /\ in_read' = FALSE \* issue complete
    /\ good' = /\ \A C \in Core, A \in Address : ~read_snoop[C][A] \* all snoops must be complete
               /\ issue_core = c
               /\ issue_addr = a
               /\ transfer
               /\ in_read
    /\ transfer' = FALSE
    /\ UNCHANGED<<in_write, issue_core, issue_addr, read_snoop, ownership_snoop, upgrade_snoop>>

complete_proc_read_invalid_exclusive(c, a, v) ==
    /\ proc_read[c][a]
    /\ \A V \in Value : ~bus_transfer[V]
    /\ \A C \in Core : \A A \in Address : ~bus_read[C][A]
    /\ memory[a] = v
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ bus_in_use' = FALSE
    /\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, proc_write, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ in_read' = FALSE \* issue complete
    /\ good' = /\ \A C \in Core, A \in Address : ~read_snoop[C][A] \* all snoops must be complete
               /\ issue_core = c
               /\ issue_addr = a
               /\ ~transfer
               /\ in_read
    /\ UNCHANGED<<in_write, issue_core, issue_addr, read_snoop, ownership_snoop, upgrade_snoop, transfer>>

issue_proc_write_invalid(c, a, v) ==
    /\ ~bus_in_use
    /\ bus_in_use' = TRUE
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
    /\ bus_read_for_ownership' = [C \in Core |-> [A \in Address |-> bus_read_for_ownership[C][A] \/ (C # c /\ A = a)]]
    /\ UNCHANGED<<memory, cache, proc_read, bus_read, bus_upgrade, bus_transfer>>
    /\ in_write' = TRUE
    /\ issue_core' = c
    /\ issue_addr' = a
    /\ ownership_snoop' = [C \in Core |-> [A \in Address |-> (ownership_snoop[C][A] \/ (C # c /\ A = a))]] \* all other cores snoop on the ownerhsip request
    /\ good' = ~in_read /\ ~in_write \* multiple issues cannot happen concurrently
    /\ UNCHANGED<<in_read, read_snoop, upgrade_snoop, transfer>>

do_bus_read_for_ownership_invalid(c, a) ==
    /\ bus_read_for_ownership[c][a]
    /\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, cache, proc_read, proc_write, bus_in_use, bus_read, bus_upgrade, bus_transfer>>
    /\ ownership_snoop' = [ownership_snoop EXCEPT![c][a] = FALSE]
    /\ good' = ownership_snoop[c][a]
    /\ UNCHANGED<<in_read, in_write, issue_core, issue_addr, read_snoop, upgrade_snoop, transfer>>

do_bus_read_for_ownership_valid(c, a, v) ==
    /\ bus_read_for_ownership[c][a]
    /\ cache[c][a] = v
    /\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
    /\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
    /\ UNCHANGED<<memory, cache, proc_read, proc_write, bus_in_use, bus_read, bus_upgrade>>
    /\ ownership_snoop' = [ownership_snoop EXCEPT![c][a] = FALSE]
    /\ good' = ownership_snoop[c][a]
    /\ transfer' = TRUE
    /\ UNCHANGED<<in_read, in_write, issue_core, issue_addr, read_snoop, upgrade_snoop>>

do_bus_read_for_ownership_modified(c, a, v) ==
    /\ bus_read_for_ownership[c][a]
    /\ cache[c][a] = v
    /\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
    /\ memory' = [memory EXCEPT![a] = v]
    /\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
    /\ UNCHANGED<<cache, proc_read, proc_write, bus_in_use, bus_read, bus_upgrade>>
    /\ ownership_snoop' = [ownership_snoop EXCEPT![c][a] = FALSE]
    /\ good' = ownership_snoop[c][a]
    /\ transfer' = TRUE
    /\ UNCHANGED<<in_read, in_write, issue_core, issue_addr, read_snoop, upgrade_snoop>>

complete_proc_write_invalid(c, a, v) ==
    /\ proc_write[c][a][v]
    /\ \A C \in Core : \A A \in Address : ~bus_read_for_ownership[C][A]
    /\ bus_transfer' = [V \in Value |-> FALSE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ bus_in_use' = FALSE
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
    /\ UNCHANGED<<memory, proc_read, bus_read, bus_read_for_ownership, bus_upgrade>>
    /\ in_write' = FALSE \* issue complete
    /\ good' = /\ \A C \in Core, A \in Address : ~ownership_snoop[C][A] \* all snoops must be complete
               /\ issue_core = c
               /\ issue_addr = a
               /\ in_write
    /\ transfer' = FALSE
    /\ UNCHANGED<<in_read, issue_core, issue_addr, read_snoop, ownership_snoop, upgrade_snoop>>

proc_write_exclusive(c, a, v) ==
    /\ ~bus_in_use
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ UNCHANGED<<memory, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ UNCHANGED<<in_read, in_write, issue_core, issue_addr, read_snoop, ownership_snoop, upgrade_snoop, good, transfer>>

issue_proc_write_shared(c, a, v) ==
    /\ ~bus_in_use
    /\ bus_in_use' = TRUE
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
    /\ bus_upgrade' = [C \in Core |-> [A \in Address |-> bus_upgrade[C][A] \/ (C # c /\ A = a)]]
    /\ UNCHANGED<<memory, cache, proc_read, bus_read, bus_read_for_ownership, bus_transfer>>
    /\ in_write' = TRUE
    /\ issue_core' = c
    /\ issue_addr' = a
    /\ upgrade_snoop' = [C \in Core |-> [A \in Address |-> (upgrade_snoop[C][A] \/ (C # c /\ A = a))]] \* all other cores snoop on the upgrade request
    /\ good' = ~in_read /\ ~in_write \* multiple issues cannot happen concurrently
    /\ UNCHANGED<<in_read, read_snoop, ownership_snoop, transfer>>

\* better name: invalidate_after_bus_upgrade_signal
\* another loc has upgraded so (c,a) must invalidate
do_bus_upgrade(c, a) ==
    /\ bus_upgrade[c][a]
    /\ bus_upgrade' = [bus_upgrade EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, cache, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_transfer>>
    /\ upgrade_snoop' = [upgrade_snoop EXCEPT![c][a] = FALSE]
    /\ good' = upgrade_snoop[c][a]
    /\ UNCHANGED<<in_read, in_write, issue_core, issue_addr, read_snoop, ownership_snoop, transfer>>

complete_proc_write_shared(c, a, v) ==
    /\ proc_write[c][a][v]
    /\ \A C \in Core : \A A \in Address : ~bus_upgrade[C][A]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
    /\ bus_in_use' = FALSE
    /\ UNCHANGED<<memory, proc_read, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ in_write' = FALSE \* issue complete
    /\ upgrade_snoop' = [upgrade_snoop EXCEPT![c][a] = FALSE]
    /\ good' = /\ \A C \in Core, A \in Address : ~upgrade_snoop[C][A]
               /\ issue_core = c
               /\ issue_addr = a
               /\ in_write
    /\ UNCHANGED<<in_read, issue_core, issue_addr, read_snoop, ownership_snoop, transfer>>

evict_modified(c, a) ==
    /\ ~bus_in_use
    /\ memory' = [memory EXCEPT![a] = cache[c][a]]
    /\ UNCHANGED<<cache, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ good' = ~in_read /\ ~in_write
    /\ UNCHANGED<<in_read, in_write, issue_core, issue_addr, read_snoop, ownership_snoop, upgrade_snoop, transfer>>

evict_exclusive_or_shared(c, a) ==
    /\ ~bus_in_use
    /\ UNCHANGED<<memory, cache, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ good' = ~in_read /\ ~in_write
    /\ UNCHANGED<<in_read, in_write, issue_core, issue_addr, read_snoop, ownership_snoop, upgrade_snoop, transfer>>

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
