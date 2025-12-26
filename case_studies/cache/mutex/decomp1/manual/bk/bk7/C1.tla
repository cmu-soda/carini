---- MODULE C1 ----

CONSTANTS Address, Core, Value

VARIABLES modified, exclusive, shared, invalid,
    good, read_issuer, read_snoop,
    
    \* orig 
    upgrading, upgraded, state, transfer, write_state

vars == <<modified, exclusive, shared, invalid,
    good, read_issuer, read_snoop,

    upgrading, upgraded, state, transfer, write_state>>

CandSep ==
    /\ good

    /\ \A C \in Core, A \in Address : upgraded[C][A] => upgrading[C][A]
    /\ \A C \in Core, A \in Address : state[C][A] # "bad"
    /\ \A C \in Core, A \in Address : write_state[C][A] # "bad"

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

    /\ upgrading = [C \in Core |-> [a \in Address |-> FALSE]]
    /\ upgraded = [C \in Core |-> [a \in Address |-> FALSE]]
    /\ state = [c \in Core |-> [a \in Address |-> "NA"]]
    /\ transfer = FALSE
    /\ write_state = [c \in Core |-> [a \in Address |-> "NA"]]

issue_proc_read_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, exclusive, shared, invalid>>
    /\ read_issuer' = [read_issuer EXCEPT![c][a] = TRUE]
    /\ read_snoop' = [C \in Core |-> [A \in Address |-> (read_snoop[C][A] \/ (C # c /\ A = a))]] \* all other cores snoop on the read
    /\ good' = \A C \in Core, A \in Address : ~read_issuer[C][A] \* multiple issues cannot happen concurrently

    /\ UNCHANGED<<upgrading, upgraded, transfer, write_state>>
    /\ LET state_val == IF (\A C \in Core, A \in Address : state[C][A] = "NA") THEN "read" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ CandSep'

do_bus_read_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, exclusive, shared, invalid>>
    /\ read_snoop' = [read_snoop EXCEPT![c][a] = FALSE]
    /\ good' = ~read_issuer[c][a] /\ read_snoop[c][a] \* the issuer does not snoop
    /\ UNCHANGED<<read_issuer>>

    /\ UNCHANGED<<upgrading, upgraded, transfer, write_state>>
    /\ LET state_val == IF (state[c][a] = "read") THEN "bad" ELSE state[c][a] IN \* issuer will not perform this
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
    /\ UNCHANGED<<read_issuer>>

    /\ UNCHANGED<<upgrading, upgraded, write_state>>
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
    /\ UNCHANGED<<read_issuer>>

    /\ UNCHANGED<<upgrading, upgraded, write_state>>
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
    /\ good' = \A C \in Core, A \in Address : ~read_snoop[C][A] \* all snoops must be complete
    /\ UNCHANGED<<read_snoop>>

    /\ UNCHANGED<<upgrading, upgraded, write_state>>
    /\ LET state_val == IF (state[c][a] = "read" /\ transfer) THEN "NA" ELSE "bad" IN \* only allow the issuer to perform this action
       state' = [state EXCEPT![c][a] = state_val]
    /\ transfer' = FALSE
    /\ CandSep'

complete_proc_read_invalid_exclusive(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<modified, shared>>
    /\ read_issuer' = [read_issuer EXCEPT![c][a] = FALSE] \* issue complete
    /\ good' = \A C \in Core, A \in Address : ~read_snoop[C][A] \* all snoops must be complete
    /\ UNCHANGED<<read_snoop>>

    /\ UNCHANGED<<upgrading, upgraded, transfer, write_state>>
    /\ LET state_val == IF (state[c][a] = "read" /\ ~transfer) THEN "NA" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ CandSep'

issue_proc_write_invalid(c, a, v) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, exclusive, shared, invalid>>
    /\ UNCHANGED<<read_issuer, read_snoop, good>>

    /\ UNCHANGED<<upgrading, upgraded, transfer>>
    /\ LET state_val == IF (\A C \in Core, A \in Address : state[C][A] = "NA") THEN "write" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ write_state' = [C \in Core |-> [A \in Address |-> IF (C # c /\ A = a) THEN "write" ELSE write_state[C][A]]]
    /\ CandSep'

do_bus_read_for_ownership_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, exclusive, shared, invalid>>
    /\ UNCHANGED<<read_issuer, read_snoop, good>>

    /\ UNCHANGED<<upgrading, upgraded, state, transfer>>
    /\ LET write_state_val == IF (write_state[c][a] = "write") THEN "NA" ELSE "bad" IN
       write_state' = [write_state EXCEPT![c][a] = write_state_val]
    /\ CandSep'

do_bus_read_for_ownership_valid(c, a, v) ==
    /\ ~invalid[c][a]
    /\ ~modified[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<upgrading, upgraded, state>>
    /\ UNCHANGED<<read_issuer, read_snoop, good>>

    /\ transfer' = TRUE
    /\ LET write_state_val == IF (write_state[c][a] = "write") THEN "NA" ELSE "bad" IN
       write_state' = [write_state EXCEPT![c][a] = write_state_val]
    /\ CandSep'

do_bus_read_for_ownership_modified(c, a, v) ==
    /\ ~invalid[c][a]
    /\ modified[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<read_issuer, read_snoop, good>>

    /\ UNCHANGED<<upgrading, upgraded, state>>
    /\ transfer' = TRUE
    /\ LET write_state_val == IF (write_state[c][a] = "write") THEN "NA" ELSE "bad" IN
       write_state' = [write_state EXCEPT![c][a] = write_state_val]
    /\ CandSep'

complete_proc_write_invalid(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<exclusive, shared>>
    /\ UNCHANGED<<read_issuer, read_snoop, good>>

    /\ UNCHANGED<<upgrading, upgraded>>
    /\ LET state_val == IF (state[c][a] = "write") THEN "NA" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ transfer' = FALSE
    /\ LET write_state_val == IF (\A C \in Core, A \in Address : write_state[C][A] = "NA") THEN write_state[c][a] ELSE "bad" IN
       write_state' = [write_state EXCEPT![c][a] = write_state_val]
    /\ CandSep'

proc_write_exclusive(c, a, v) ==
    /\ exclusive[c][a]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<shared, invalid>>
    /\ UNCHANGED<<read_issuer, read_snoop, good>>

    /\ UNCHANGED<<upgrading, upgraded, transfer, write_state>>
    /\ LET state_val == IF (\A C \in Core, A \in Address : state[C][A] = "NA") THEN "NA" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ CandSep'

issue_proc_write_shared(c, a, v) ==
    /\ shared[c][a]
    /\ UNCHANGED<<modified, exclusive, shared, invalid>>
    /\ UNCHANGED<<read_issuer, read_snoop, good>>

    /\ UNCHANGED<<upgraded, transfer, write_state>>
    /\ upgrading' = [C \in Core |-> [A \in Address |-> upgrading[C][A] \/ (C # c /\ A = a)]]
    /\ LET state_val == IF (\A C \in Core, A \in Address : state[C][A] = "NA") THEN "write" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ CandSep'

\* better name: invalidate_after_bus_upgrade_signal
\* another loc has upgraded so (c,a) must invalidate
do_bus_upgrade(c, a) ==
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<modified, exclusive>>
    /\ UNCHANGED<<read_issuer, read_snoop, good>>

    /\ UNCHANGED<<upgrading, state, transfer, write_state>>
    /\ upgraded' = [upgraded EXCEPT![c][a] = TRUE]
    /\ CandSep'

complete_proc_write_shared(c, a, v) ==
    /\ shared[c][a]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<exclusive, invalid>>
    /\ good' = (upgrading = upgraded) \* all other cores have snooped the upgrade signal
    /\ UNCHANGED<<read_issuer, read_snoop>>

    /\ UNCHANGED<<transfer, write_state>>
    /\ upgrading' = [C \in Core |-> [A \in Address |-> FALSE]]
    /\ upgraded' = [C \in Core |-> [A \in Address |-> FALSE]]
    /\ LET state_val == IF (state[c][a] = "write") THEN "NA" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ CandSep'

evict_modified(c, a) ==
    /\ modified[c][a]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<exclusive, shared>>
    /\ UNCHANGED<<read_issuer, read_snoop, good>>

    /\ UNCHANGED<<upgrading, upgraded, transfer, write_state>>
    /\ LET state_val == IF (\A C \in Core, A \in Address : state[C][A] = "NA") THEN "NA" ELSE "bad" IN
       state' = [state EXCEPT![c][a] = state_val]
    /\ CandSep'

evict_exclusive_or_shared(c, a) ==
    /\ exclusive[c][a] \/ shared[c][a]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<modified>>
    /\ UNCHANGED<<read_issuer, read_snoop, good>>

    /\ UNCHANGED<<upgrading, upgraded, transfer, write_state>>
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
