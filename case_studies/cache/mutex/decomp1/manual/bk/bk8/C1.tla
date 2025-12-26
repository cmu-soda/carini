---- MODULE C1 ----

CONSTANTS Address, Core, Value

VARIABLES modified, exclusive, shared, invalid,
    good, read_issuer, read_snoop, write_issuer, ownership_snoop, upgrade_snoop,
    
    \* orig 
    state, transfer

vars == <<modified, exclusive, shared, invalid,
    good, read_issuer, read_snoop, write_issuer, ownership_snoop, upgrade_snoop,

    state, transfer>>

CandSep ==
    /\ good

    /\ \A C \in Core, A \in Address : state[C][A] # "bad"

    \*/\ \A C1,C2 \in Core, A1,A2 \in Address : (state[C1][A1] = "read" /\ state[C2][A2] = "read") => (C1 = C2 /\ A1 = A2)
    \*/\ \A C1,C2 \in Core, A1,A2 \in Address : (state[C1][A1] = "write" /\ state[C2][A2] = "write") => (C1 = C2 /\ A1 = A2)
    \*/\ \A C1,C2 \in Core, A1,A2 \in Address : (state[C1][A1] = "read" /\ state[C2][A2] = "write") => (C1 = C2 /\ A1 = A2)

Init ==
    /\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]

    /\ good = TRUE
    /\ read_issuer = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ read_snoop = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ write_issuer = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ ownership_snoop = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ upgrade_snoop = [c \in Core |-> [a \in Address |-> FALSE]]

    /\ state = [c \in Core |-> [a \in Address |-> "NA"]]
    /\ transfer = FALSE

issue_proc_read_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, exclusive, shared, invalid>>
    /\ read_issuer' = [read_issuer EXCEPT![c][a] = TRUE]
    /\ read_snoop' = [C \in Core |-> [A \in Address |-> (read_snoop[C][A] \/ (C # c /\ A = a))]] \* all other cores snoop on the read
    /\ good' = \A C \in Core, A \in Address : ~read_issuer[C][A] \* multiple issues cannot happen concurrently
    /\ UNCHANGED<<write_issuer, ownership_snoop, upgrade_snoop>>

    /\ UNCHANGED<<transfer>>
    /\ LET state_val == IF (\A C \in Core, A \in Address : state[C][A] = "NA") THEN "read" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ CandSep'

do_bus_read_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, exclusive, shared, invalid>>
    /\ read_snoop' = [read_snoop EXCEPT![c][a] = FALSE]
    /\ good' = ~read_issuer[c][a] /\ read_snoop[c][a] \* the issuer does not snoop
    /\ UNCHANGED<<read_issuer, write_issuer, ownership_snoop, upgrade_snoop>>

    /\ UNCHANGED<<transfer>>
    /\ LET state_val == IF (state[c][a] = "read") THEN "bad" ELSE state[c][a] IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ CandSep'

do_bus_read_valid(c, a, v) ==
    /\ ~invalid[c][a]
    /\ ~modified[c][a]
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<invalid>>
    /\ read_snoop' = [read_snoop EXCEPT![c][a] = FALSE]
    /\ good' = ~read_issuer[c][a] /\ read_snoop[c][a] \* the issuer does not snoop
    /\ UNCHANGED<<read_issuer, write_issuer, ownership_snoop, upgrade_snoop>>

    /\ LET state_val == IF (state[c][a] = "read") THEN "bad" ELSE state[c][a] IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ transfer' = TRUE
    /\ CandSep'

do_bus_read_modified(c, a, v) ==
    /\ ~invalid[c][a]
    /\ modified[c][a]
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<invalid>>
    /\ read_snoop' = [read_snoop EXCEPT![c][a] = FALSE]
    /\ good' = ~read_issuer[c][a] /\ read_snoop[c][a] \* the issuer does not snoop
    /\ UNCHANGED<<read_issuer, write_issuer, ownership_snoop, upgrade_snoop>>

    /\ LET state_val == IF (state[c][a] = "read") THEN "bad" ELSE state[c][a] IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ transfer' = TRUE
    /\ CandSep'

complete_proc_read_invalid_shared(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<modified, exclusive>>
    /\ read_issuer' = [read_issuer EXCEPT![c][a] = FALSE] \* issue complete
    /\ good' = /\ \A C \in Core, A \in Address : ~read_snoop[C][A] \* all snoops must be complete
               /\ transfer
    /\ UNCHANGED<<read_snoop, write_issuer, ownership_snoop, upgrade_snoop>>

    /\ LET state_val == IF (state[c][a] = "read") THEN "NA" ELSE "bad" IN \* only allow the issuer to perform this action
       state' = [state EXCEPT![c][a] = state_val]
    /\ transfer' = FALSE
    /\ CandSep'

complete_proc_read_invalid_exclusive(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<modified, shared>>
    /\ read_issuer' = [read_issuer EXCEPT![c][a] = FALSE] \* issue complete
    /\ good' = /\ \A C \in Core, A \in Address : ~read_snoop[C][A] \* all snoops must be complete
               /\ ~transfer
    /\ UNCHANGED<<read_snoop, write_issuer, ownership_snoop, upgrade_snoop>>

    /\ UNCHANGED<<transfer>>
    /\ LET state_val == IF (state[c][a] = "read") THEN "NA" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ CandSep'

issue_proc_write_invalid(c, a, v) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, exclusive, shared, invalid>>
    /\ write_issuer' = [write_issuer EXCEPT![c][a] = TRUE]
    /\ ownership_snoop' = [C \in Core |-> [A \in Address |-> (ownership_snoop[C][A] \/ (C # c /\ A = a))]] \* all other cores snoop on the ownerhsip request
    /\ good' = TRUE
    /\ UNCHANGED<<read_issuer, read_snoop, upgrade_snoop>>

    /\ UNCHANGED<<transfer>>
    /\ LET state_val == IF (\A C \in Core, A \in Address : state[C][A] = "NA") THEN "write" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ CandSep'

do_bus_read_for_ownership_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, exclusive, shared, invalid>>
    /\ ownership_snoop' = [ownership_snoop EXCEPT![c][a] = FALSE]
    /\ good' = ownership_snoop[c][a]
    /\ UNCHANGED<<read_issuer, read_snoop, write_issuer, upgrade_snoop>>

    /\ UNCHANGED<<state, transfer>>
    /\ CandSep'

do_bus_read_for_ownership_valid(c, a, v) ==
    /\ ~invalid[c][a]
    /\ ~modified[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ ownership_snoop' = [ownership_snoop EXCEPT![c][a] = FALSE]
    /\ good' = ownership_snoop[c][a]
    /\ UNCHANGED<<read_issuer, read_snoop, write_issuer, upgrade_snoop>>

    /\ UNCHANGED<<state>>
    /\ transfer' = TRUE
    /\ CandSep'

do_bus_read_for_ownership_modified(c, a, v) ==
    /\ ~invalid[c][a]
    /\ modified[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ ownership_snoop' = [ownership_snoop EXCEPT![c][a] = FALSE]
    /\ good' = ownership_snoop[c][a]
    /\ UNCHANGED<<read_issuer, read_snoop, write_issuer, upgrade_snoop>>

    /\ UNCHANGED<<state>>
    /\ transfer' = TRUE
    /\ CandSep'

complete_proc_write_invalid(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<exclusive, shared>>
    /\ write_issuer' = [write_issuer EXCEPT![c][a] = FALSE] \* issue complete
    /\ good' = \A C \in Core, A \in Address : ~ownership_snoop[C][A] \* all snoops must be complete
    /\ UNCHANGED<<read_issuer, read_snoop, ownership_snoop, upgrade_snoop>>

    /\ LET state_val == IF (state[c][a] = "write") THEN "NA" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ transfer' = FALSE
    /\ CandSep'

proc_write_exclusive(c, a, v) ==
    /\ exclusive[c][a]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<shared, invalid>>
    /\ UNCHANGED<<read_issuer, read_snoop, write_issuer, ownership_snoop, upgrade_snoop, good>>

    /\ UNCHANGED<<transfer>>
    /\ LET state_val == IF (\A C \in Core, A \in Address : state[C][A] = "NA") THEN "NA" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ CandSep'

issue_proc_write_shared(c, a, v) ==
    /\ shared[c][a]
    /\ UNCHANGED<<modified, exclusive, shared, invalid>>
    /\ write_issuer' = [write_issuer EXCEPT![c][a] = TRUE]
    /\ upgrade_snoop' = [C \in Core |-> [A \in Address |-> (upgrade_snoop[C][A] \/ (C # c /\ A = a))]] \* all other cores snoop on the upgrade request
    /\ good' = TRUE
    /\ UNCHANGED<<read_issuer, read_snoop, ownership_snoop>>

    /\ UNCHANGED<<transfer>>
    /\ LET state_val == IF (\A C \in Core, A \in Address : state[C][A] = "NA") THEN "write" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ CandSep'

\* better name: invalidate_after_bus_upgrade_signal
\* another loc has upgraded so (c,a) must invalidate
do_bus_upgrade(c, a) ==
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<modified, exclusive>>
    /\ upgrade_snoop' = [upgrade_snoop EXCEPT![c][a] = FALSE]
    /\ good' = upgrade_snoop[c][a]
    /\ UNCHANGED<<read_issuer, read_snoop, write_issuer, ownership_snoop>>

    /\ UNCHANGED<<state, transfer>>
    /\ CandSep'

complete_proc_write_shared(c, a, v) ==
    /\ shared[c][a]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<exclusive, invalid>>
    /\ upgrade_snoop' = [upgrade_snoop EXCEPT![c][a] = FALSE]
    /\ good' = \A C \in Core, A \in Address : ~upgrade_snoop[C][A]
    /\ UNCHANGED<<read_issuer, read_snoop, write_issuer, ownership_snoop>>

    /\ UNCHANGED<<transfer>>
    /\ LET state_val == IF (state[c][a] = "write") THEN "NA" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ CandSep'

evict_modified(c, a) ==
    /\ modified[c][a]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<exclusive, shared>>
    /\ UNCHANGED<<read_issuer, read_snoop, write_issuer, ownership_snoop, upgrade_snoop, good>>

    /\ UNCHANGED<<transfer>>
    /\ LET state_val == IF (\A C \in Core, A \in Address : state[C][A] = "NA") THEN "NA" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ CandSep'

evict_exclusive_or_shared(c, a) ==
    /\ exclusive[c][a] \/ shared[c][a]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<modified>>
    /\ UNCHANGED<<read_issuer, read_snoop, write_issuer, ownership_snoop, upgrade_snoop, good>>

    /\ UNCHANGED<<transfer>>
    /\ LET state_val == IF (\A C \in Core, A \in Address : state[C][A] = "NA") THEN "NA" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ CandSep'

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

Safety ==
  \A C \in Core, A \in Address :
    /\ ~(invalid[C][A] /\ modified[C][A])
    /\ ~(invalid[C][A] /\ exclusive[C][A])
    /\ ~(invalid[C][A] /\ shared[C][A])
    /\ ~(modified[C][A] /\ exclusive[C][A])
    /\ ~(modified[C][A] /\ shared[C][A])
    /\ ~(exclusive[C][A] /\ shared[C][A])

======
