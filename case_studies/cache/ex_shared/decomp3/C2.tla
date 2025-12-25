---- MODULE C2 ----

CONSTANTS Address, Core, Value

VARIABLES modified, invalid

vars == <<modified, invalid>>


Init ==
    /\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]

issue_proc_read_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, invalid>>

do_bus_read_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, invalid>>

do_bus_read_valid(c, a, v) ==
    /\ ~invalid[c][a]
    /\ ~modified[c][a]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<invalid>>

do_bus_read_modified(c, a, v) ==
    /\ ~invalid[c][a]
    /\ modified[c][a]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<invalid>>

complete_proc_read_invalid_shared(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<modified>>

complete_proc_read_invalid_exclusive(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<modified>>

issue_proc_write_invalid(c, a, v) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, invalid>>

do_bus_read_for_ownership_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, invalid>>

do_bus_read_for_ownership_valid(c, a, v) ==
    /\ ~invalid[c][a]
    /\ ~modified[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]

do_bus_read_for_ownership_modified(c, a, v) ==
    /\ ~invalid[c][a]
    /\ modified[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]

complete_proc_write_invalid(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]

proc_write_exclusive(c, a, v) ==
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<invalid>>

do_bus_upgrade(c, a) ==
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<modified>>

complete_proc_write_shared(c, a, v) ==
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<invalid>>

evict_modified(c, a) ==
    /\ modified[c][a]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]

evict_exclusive_or_shared(c, a) ==
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<modified>>

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
        \/ do_bus_upgrade(c,a)
        \/ complete_proc_write_shared(c,a,v)
        \/ evict_modified(c,a)
        \/ evict_exclusive_or_shared(c,a)

Spec == Init /\ [][Next]_vars

======
