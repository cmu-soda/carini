---- MODULE C1 ----

CONSTANTS Address, Core, Value

VARIABLES modified, exclusive, shared, invalid, bus_mode, upgrading, upgraded

vars == <<modified, exclusive, shared, invalid, bus_mode, upgrading, upgraded>>

CandSep ==
    /\ bus_mode # "bad"
    /\ \A C \in Core, A \in Address : upgraded[C][A] => upgrading[C][A]

Init ==
    /\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]
    /\ bus_mode = "not_used"
    /\ upgrading = [C \in Core |-> [a \in Address |-> FALSE]]
    /\ upgraded = [C \in Core |-> [a \in Address |-> FALSE]]

issue_proc_read_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, exclusive, shared, invalid>>
    /\ UNCHANGED<<upgrading, upgraded>>
    /\ bus_mode' = IF bus_mode = "not_used" THEN "read" ELSE "bad"
    /\ CandSep'

do_bus_read_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, exclusive, shared, invalid>>
    /\ UNCHANGED<<bus_mode, upgrading, upgraded>>
    /\ CandSep'

do_bus_read_valid(c, a, v) ==
    /\ ~invalid[c][a]
    /\ ~modified[c][a]
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<invalid>>
    /\ UNCHANGED<<bus_mode, upgrading, upgraded>>
    /\ CandSep'

do_bus_read_modified(c, a, v) ==
    /\ ~invalid[c][a]
    /\ modified[c][a]
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<invalid>>
    /\ UNCHANGED<<bus_mode, upgrading, upgraded>>
    /\ CandSep'

complete_proc_read_invalid_shared(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<modified, exclusive>>
    /\ UNCHANGED<<upgrading, upgraded>>
    /\ bus_mode' = IF bus_mode = "read" THEN "not_used" ELSE "bad"
    /\ CandSep'

complete_proc_read_invalid_exclusive(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<modified, shared>>
    /\ UNCHANGED<<upgrading, upgraded>>
    /\ bus_mode' = IF bus_mode = "read" THEN "not_used" ELSE "bad"
    /\ CandSep'

issue_proc_write_invalid(c, a, v) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, exclusive, shared, invalid>>
    /\ UNCHANGED<<upgrading, upgraded>>
    /\ bus_mode' = IF bus_mode = "not_used" THEN "write" ELSE "bad"
    /\ CandSep'

do_bus_read_for_ownership_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, exclusive, shared, invalid>>
    /\ UNCHANGED<<bus_mode, upgrading, upgraded>>
    /\ CandSep'

do_bus_read_for_ownership_valid(c, a, v) ==
    /\ ~invalid[c][a]
    /\ ~modified[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<bus_mode, upgrading, upgraded>>
    /\ CandSep'

do_bus_read_for_ownership_modified(c, a, v) ==
    /\ ~invalid[c][a]
    /\ modified[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<bus_mode, upgrading, upgraded>>
    /\ CandSep'

complete_proc_write_invalid(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<exclusive, shared>>
    /\ UNCHANGED<<upgrading, upgraded>>
    /\ bus_mode' = IF bus_mode = "write" THEN "not_used" ELSE "bad"
    /\ CandSep'

proc_write_exclusive(c, a, v) ==
    /\ exclusive[c][a]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<shared, invalid>>
    /\ UNCHANGED<<upgrading, upgraded>>
    /\ bus_mode' = IF bus_mode = "not_used" THEN "not_used" ELSE "bad"
    /\ CandSep'

issue_proc_write_shared(c, a, v) ==
    /\ shared[c][a]
    /\ UNCHANGED<<modified, exclusive, shared, invalid>>
    /\ UNCHANGED<<upgraded>>
    /\ bus_mode' = IF bus_mode = "not_used" THEN "write" ELSE "bad"
    /\ upgrading' = [C \in Core |-> [A \in Address |-> upgrading[C][A] \/ (C # c /\ A = a)]]
    /\ CandSep'

do_bus_upgrade(c, a) ==
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<modified, exclusive>>
    /\ UNCHANGED<<bus_mode, upgrading>>
    /\ upgraded' = [upgraded EXCEPT![c][a] = TRUE]
    /\ CandSep'

complete_proc_write_shared(c, a, v) ==
    /\ shared[c][a]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<exclusive, invalid>>
    /\ bus_mode' = IF bus_mode = "write" THEN "not_used" ELSE "bad"
    /\ upgrading' = [upgrading EXCEPT![c][a] = FALSE]
    /\ upgraded' = [upgraded EXCEPT![c][a] = FALSE]
    /\ CandSep'

evict_modified(c, a) ==
    /\ modified[c][a]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<exclusive, shared>>
    /\ UNCHANGED<<upgrading, upgraded>>
    /\ bus_mode' = IF bus_mode = "not_used" THEN "not_used" ELSE "bad"
    /\ CandSep'

evict_exclusive_or_shared(c, a) ==
    /\ exclusive[c][a] \/ shared[c][a]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<modified>>
    /\ UNCHANGED<<upgrading, upgraded>>
    /\ bus_mode' = IF bus_mode = "not_used" THEN "not_used" ELSE "bad"
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
