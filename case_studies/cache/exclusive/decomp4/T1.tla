---- MODULE T1 ----

CONSTANTS Address, Core, Value

VARIABLES modified, shared, invalid

vars == <<modified, shared, invalid>>


Init ==
    /\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]


(* Invalid state actions *)

issue_proc_read_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, shared, invalid>>

do_bus_read_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, shared, invalid>>

complete_proc_read_invalid_shared(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<modified>>

complete_proc_read_invalid_exclusive(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<modified, shared>>

issue_proc_write_invalid(c, a, v) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, shared, invalid>>

complete_proc_write_invalid(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<shared>>

do_bus_read_for_ownership_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, shared, invalid>>


(* Modified state actions *)

do_bus_read_modified(c, a, v) ==
    /\ ~invalid[c][a]
    /\ modified[c][a]
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<invalid>>

do_bus_read_for_ownership_modified(c, a, v) ==
    /\ ~invalid[c][a]
    /\ modified[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]

evict_modified(c, a) ==
    /\ modified[c][a]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<shared>>


(* Shared state actions *)

issue_proc_write_shared(c, a, v) ==
    /\ shared[c][a]
    /\ UNCHANGED<<modified, shared, invalid>>

complete_proc_write_shared(c, a, v) ==
    /\ shared[c][a]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<invalid>>

evict_shared(c, a) ==
    /\ shared[c][a]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<modified>>


(* Exclusive state actions *)

proc_write_exclusive(c, a, v) ==
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<shared, invalid>>

evict_exclusive(c, a) ==
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<modified>>


(* Exclusive or shared state actions *)

do_bus_read_valid(c, a, v) ==
    /\ ~invalid[c][a]
    /\ ~modified[c][a]
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<invalid>>

do_bus_read_for_ownership_valid(c, a, v) ==
    /\ ~invalid[c][a]
    /\ ~modified[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]


(* Invalid or shared state actions *)

do_bus_upgrade(c, a) ==
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
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
        \/ issue_proc_write_shared(c,a,v)
        \/ do_bus_upgrade(c,a)
        \/ complete_proc_write_shared(c,a,v)
        \/ evict_modified(c,a)
        \/ evict_exclusive(c,a)
        \/ evict_shared(c,a)

Spec == Init /\ [][Next]_vars

======
