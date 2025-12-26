---- MODULE T1 ----

CONSTANTS Address, Core, Value

VARIABLES memory, cache, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer,
    good, read_issuer, read_snoop, write_issuer, ownership_snoop, upgrade_snoop,
    
    state, transfer

vars == <<memory, cache, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer,
    good, read_issuer, read_snoop, write_issuer, ownership_snoop, upgrade_snoop,

    state, transfer>>

CandSep ==
    /\ good

    /\ \A C \in Core, A \in Address : state[C][A] # "bad"

    \*/\ \A C1,C2 \in Core, A1,A2 \in Address : (state[C1][A1] = "read" /\ state[C2][A2] = "read") => (C1 = C2 /\ A1 = A2)
    \*/\ \A C1,C2 \in Core, A1,A2 \in Address : (state[C1][A1] = "write" /\ state[C2][A2] = "write") => (C1 = C2 /\ A1 = A2)
    \*/\ \A C1,C2 \in Core, A1,A2 \in Address : (state[C1][A1] = "read" /\ state[C2][A2] = "write") => (C1 = C2 /\ A1 = A2)

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
    /\ read_issuer = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ read_snoop = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ write_issuer = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ ownership_snoop = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ upgrade_snoop = [c \in Core |-> [a \in Address |-> FALSE]]

    /\ state = [c \in Core |-> [a \in Address |-> "NA"]]
    /\ transfer = FALSE

issue_proc_read_invalid(c, a) ==
    /\ ~bus_in_use
    /\ bus_in_use' = TRUE
    /\ proc_read' = [proc_read EXCEPT![c][a] = TRUE]
    /\ bus_read' = [C \in Core |-> [A \in Address |-> bus_read[C][A] \/ (C # c /\ A = a)]]
    /\ UNCHANGED<<memory, cache, proc_write, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ read_issuer' = [read_issuer EXCEPT![c][a] = TRUE]
    /\ read_snoop' = [C \in Core |-> [A \in Address |-> (read_snoop[C][A] \/ (C # c /\ A = a))]] \* all other cores snoop on the read
    /\ good' = \A C \in Core, A \in Address : ~read_issuer[C][A] \* multiple issues cannot happen concurrently
    /\ UNCHANGED<<write_issuer, ownership_snoop, upgrade_snoop>>

    /\ UNCHANGED<<transfer>>
    /\ LET state_val == IF (\A C \in Core, A \in Address : state[C][A] = "NA") THEN "read" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]

do_bus_read_invalid(c, a) ==
    /\ bus_read[c][a]
    /\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, cache, proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ read_snoop' = [read_snoop EXCEPT![c][a] = FALSE]
    /\ good' = ~read_issuer[c][a] /\ read_snoop[c][a] \* the issuer does not snoop
    /\ UNCHANGED<<read_issuer, write_issuer, ownership_snoop, upgrade_snoop>>

    /\ UNCHANGED<<transfer>>
    /\ LET state_val == IF (state[c][a] = "read") THEN "bad" ELSE state[c][a] IN
       state' = [state EXCEPT![c][a] = state_val]

do_bus_read_valid(c, a, v) ==
    /\ bus_read[c][a]
    /\ cache[c][a] = v
    /\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
    /\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
    /\ UNCHANGED<<memory, cache, proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade>>
    /\ read_snoop' = [read_snoop EXCEPT![c][a] = FALSE]
    /\ good' = ~read_issuer[c][a] /\ read_snoop[c][a] \* the issuer does not snoop
    /\ UNCHANGED<<read_issuer, write_issuer, ownership_snoop, upgrade_snoop>>

    /\ LET state_val == IF (state[c][a] = "read") THEN "bad" ELSE state[c][a] IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ transfer' = TRUE

do_bus_read_modified(c, a, v) ==
    /\ bus_read[c][a]
    /\ cache[c][a] = v
    /\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
    /\ memory' = [memory EXCEPT![a] = v]
    /\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
    /\ UNCHANGED<<cache, proc_read, proc_write, bus_in_use, bus_read_for_ownership, bus_upgrade>>
    /\ read_snoop' = [read_snoop EXCEPT![c][a] = FALSE]
    /\ good' = ~read_issuer[c][a] /\ read_snoop[c][a] \* the issuer does not snoop
    /\ UNCHANGED<<read_issuer, write_issuer, ownership_snoop, upgrade_snoop>>

    /\ LET state_val == IF (state[c][a] = "read") THEN "bad" ELSE state[c][a] IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ transfer' = TRUE

complete_proc_read_invalid_shared(c, a, v) ==
    /\ proc_read[c][a]
    /\ bus_transfer[v]
    /\ \A C \in Core : \A A \in Address : ~bus_read[C][A]
    /\ bus_transfer' = [V \in Value |-> FALSE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ bus_in_use' = FALSE
    /\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, proc_write, bus_read, bus_read_for_ownership, bus_upgrade>>
    /\ read_issuer' = [read_issuer EXCEPT![c][a] = FALSE] \* issue complete
    /\ good' = /\ \A C \in Core, A \in Address : ~read_snoop[C][A] \* all snoops must be complete
               /\ transfer
    /\ UNCHANGED<<read_snoop, write_issuer, ownership_snoop, upgrade_snoop>>

    /\ LET state_val == IF (state[c][a] = "read") THEN "NA" ELSE "bad" IN \* only allow the issuer to perform this action
       state' = [state EXCEPT![c][a] = state_val]
    /\ transfer' = FALSE

complete_proc_read_invalid_exclusive(c, a, v) ==
    /\ proc_read[c][a]
    /\ \A V \in Value : ~bus_transfer[V]
    /\ \A C \in Core : \A A \in Address : ~bus_read[C][A]
    /\ memory[a] = v
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ bus_in_use' = FALSE
    /\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, proc_write, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ read_issuer' = [read_issuer EXCEPT![c][a] = FALSE] \* issue complete
    /\ good' = /\ \A C \in Core, A \in Address : ~read_snoop[C][A] \* all snoops must be complete
               /\ ~transfer
    /\ UNCHANGED<<read_snoop, write_issuer, ownership_snoop, upgrade_snoop>>

    /\ UNCHANGED<<transfer>>
    /\ LET state_val == IF (state[c][a] = "read") THEN "NA" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]

issue_proc_write_invalid(c, a, v) ==
    /\ ~bus_in_use
    /\ bus_in_use' = TRUE
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
    /\ bus_read_for_ownership' = [C \in Core |-> [A \in Address |-> bus_read_for_ownership[C][A] \/ (C # c /\ A = a)]]
    /\ UNCHANGED<<memory, cache, proc_read, bus_read, bus_upgrade, bus_transfer>>
    /\ write_issuer' = [write_issuer EXCEPT![c][a] = TRUE]
    /\ ownership_snoop' = [C \in Core |-> [A \in Address |-> (ownership_snoop[C][A] \/ (C # c /\ A = a))]] \* all other cores snoop on the ownerhsip request
    /\ good' = TRUE
    /\ UNCHANGED<<read_issuer, read_snoop, upgrade_snoop>>

    /\ UNCHANGED<<transfer>>
    /\ LET state_val == IF (\A C \in Core, A \in Address : state[C][A] = "NA") THEN "write" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]

do_bus_read_for_ownership_invalid(c, a) ==
    /\ bus_read_for_ownership[c][a]
    /\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, cache, proc_read, proc_write, bus_in_use, bus_read, bus_upgrade, bus_transfer>>
    /\ ownership_snoop' = [ownership_snoop EXCEPT![c][a] = FALSE]
    /\ good' = ownership_snoop[c][a]
    /\ UNCHANGED<<read_issuer, read_snoop, write_issuer, upgrade_snoop>>

    /\ UNCHANGED<<state, transfer>>

do_bus_read_for_ownership_valid(c, a, v) ==
    /\ bus_read_for_ownership[c][a]
    /\ cache[c][a] = v
    /\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
    /\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
    /\ UNCHANGED<<memory, cache, proc_read, proc_write, bus_in_use, bus_read, bus_upgrade>>
    /\ ownership_snoop' = [ownership_snoop EXCEPT![c][a] = FALSE]
    /\ good' = ownership_snoop[c][a]
    /\ UNCHANGED<<read_issuer, read_snoop, write_issuer, upgrade_snoop>>

    /\ UNCHANGED<<state>>
    /\ transfer' = TRUE

do_bus_read_for_ownership_modified(c, a, v) ==
    /\ bus_read_for_ownership[c][a]
    /\ cache[c][a] = v
    /\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
    /\ memory' = [memory EXCEPT![a] = v]
    /\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
    /\ UNCHANGED<<cache, proc_read, proc_write, bus_in_use, bus_read, bus_upgrade>>
    /\ ownership_snoop' = [ownership_snoop EXCEPT![c][a] = FALSE]
    /\ good' = ownership_snoop[c][a]
    /\ UNCHANGED<<read_issuer, read_snoop, write_issuer, upgrade_snoop>>

    /\ UNCHANGED<<state>>
    /\ transfer' = TRUE

complete_proc_write_invalid(c, a, v) ==
    /\ proc_write[c][a][v]
    /\ \A C \in Core : \A A \in Address : ~bus_read_for_ownership[C][A]
    /\ bus_transfer' = [V \in Value |-> FALSE]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ bus_in_use' = FALSE
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
    /\ UNCHANGED<<memory, proc_read, bus_read, bus_read_for_ownership, bus_upgrade>>
    /\ write_issuer' = [write_issuer EXCEPT![c][a] = FALSE] \* issue complete
    /\ good' = \A C \in Core, A \in Address : ~ownership_snoop[C][A] \* all snoops must be complete
    /\ UNCHANGED<<read_issuer, read_snoop, ownership_snoop, upgrade_snoop>>

    /\ LET state_val == IF (state[c][a] = "write") THEN "NA" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ transfer' = FALSE

proc_write_exclusive(c, a, v) ==
    /\ ~bus_in_use
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ UNCHANGED<<memory, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ UNCHANGED<<read_issuer, read_snoop, write_issuer, ownership_snoop, upgrade_snoop, good>>

    /\ UNCHANGED<<transfer>>
    /\ LET state_val == IF (\A C \in Core, A \in Address : state[C][A] = "NA") THEN "NA" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]

issue_proc_write_shared(c, a, v) ==
    /\ ~bus_in_use
    /\ bus_in_use' = TRUE
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
    /\ bus_upgrade' = [C \in Core |-> [A \in Address |-> bus_upgrade[C][A] \/ (C # c /\ A = a)]]
    /\ UNCHANGED<<memory, cache, proc_read, bus_read, bus_read_for_ownership, bus_transfer>>
    /\ write_issuer' = [write_issuer EXCEPT![c][a] = TRUE]
    /\ upgrade_snoop' = [C \in Core |-> [A \in Address |-> (upgrade_snoop[C][A] \/ (C # c /\ A = a))]] \* all other cores snoop on the upgrade request
    /\ good' = TRUE
    /\ UNCHANGED<<read_issuer, read_snoop, ownership_snoop>>

    /\ UNCHANGED<<transfer>>
    /\ LET state_val == IF (\A C \in Core, A \in Address : state[C][A] = "NA") THEN "write" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]

\* better name: invalidate_after_bus_upgrade_signal
\* another loc has upgraded so (c,a) must invalidate
do_bus_upgrade(c, a) ==
    /\ bus_upgrade[c][a]
    /\ bus_upgrade' = [bus_upgrade EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<memory, cache, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_transfer>>
    /\ upgrade_snoop' = [upgrade_snoop EXCEPT![c][a] = FALSE]
    /\ good' = upgrade_snoop[c][a]
    /\ UNCHANGED<<read_issuer, read_snoop, write_issuer, ownership_snoop>>

    /\ UNCHANGED<<state, transfer>>

complete_proc_write_shared(c, a, v) ==
    /\ proc_write[c][a][v]
    /\ \A C \in Core : \A A \in Address : ~bus_upgrade[C][A]
    /\ cache' = [cache EXCEPT![c][a] = v]
    /\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
    /\ bus_in_use' = FALSE
    /\ UNCHANGED<<memory, proc_read, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ upgrade_snoop' = [upgrade_snoop EXCEPT![c][a] = FALSE]
    /\ good' = \A C \in Core, A \in Address : ~upgrade_snoop[c][a]
    /\ UNCHANGED<<read_issuer, read_snoop, write_issuer, ownership_snoop>>

    /\ UNCHANGED<<transfer>>
    /\ LET state_val == IF (state[c][a] = "write") THEN "NA" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]

evict_modified(c, a) ==
    /\ ~bus_in_use
    /\ memory' = [memory EXCEPT![a] = cache[c][a]]
    /\ UNCHANGED<<cache, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ UNCHANGED<<read_issuer, read_snoop, write_issuer, ownership_snoop, upgrade_snoop, good>>

    /\ UNCHANGED<<transfer>>
    /\ LET state_val == IF (\A C \in Core, A \in Address : state[C][A] = "NA") THEN "NA" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]

evict_exclusive_or_shared(c, a) ==
    /\ ~bus_in_use
    /\ UNCHANGED<<memory, cache, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>
    /\ UNCHANGED<<read_issuer, read_snoop, write_issuer, ownership_snoop, upgrade_snoop, good>>

    /\ UNCHANGED<<transfer>>
    /\ LET state_val == IF (\A C \in Core, A \in Address : state[C][A] = "NA") THEN "NA" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]

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
