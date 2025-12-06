--------------------------- MODULE T1_hist ---------------------------


CONSTANTS Address, Core, Value

VARIABLES shared, Fluent157_1, Fluent156_1, exclusive, Fluent155_1

vars == <<shared, Fluent157_1, Fluent156_1, exclusive, Fluent155_1>>

CandSep ==
\A var0 \in Value : (Fluent155_1[var0]) => ((Fluent156_1[var0]) => (Fluent157_1[var0]))

Init ==
/\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
/\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
/\ Fluent157_1 = [ x0 \in Value |-> FALSE]
/\ Fluent156_1 = [ x0 \in Value |-> FALSE]
/\ Fluent155_1 = [ x0 \in Value |-> FALSE]

do_bus_read_valid(c,a,v) ==
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ UNCHANGED<<Fluent157_1, Fluent156_1, Fluent155_1>>

complete_proc_read_invalid_shared(c,a,v) ==
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<exclusive>>
/\ UNCHANGED<<Fluent157_1, Fluent156_1, Fluent155_1>>

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<shared>>
/\ Fluent157_1' = [Fluent157_1 EXCEPT ![v] = TRUE]
/\ Fluent156_1' = [Fluent156_1 EXCEPT ![v] = Fluent157_1[v]]
/\ UNCHANGED<<Fluent155_1>>

do_bus_read_for_ownership_valid(c,a,v) ==
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ UNCHANGED<<Fluent157_1, Fluent156_1, Fluent155_1>>

proc_write_exclusive(c,a,v) ==
/\ exclusive[c][a]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<shared>>
/\ UNCHANGED<<Fluent157_1, Fluent156_1, Fluent155_1>>

issue_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ UNCHANGED <<exclusive,shared>>
/\ UNCHANGED<<Fluent157_1, Fluent156_1, Fluent155_1>>

do_bus_upgrade(c,a) ==
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<exclusive>>
/\ UNCHANGED<<Fluent157_1, Fluent156_1, Fluent155_1>>

complete_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<exclusive>>
/\ Fluent157_1' = [x0 \in Value |-> FALSE]
/\ UNCHANGED<<Fluent156_1, Fluent155_1>>

evict_exclusive_or_shared(c,a) ==
/\ (exclusive[c][a] \/ shared[c][a])
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ Fluent155_1' = [x0 \in Value |-> TRUE]
/\ UNCHANGED<<Fluent157_1, Fluent156_1>>

Next ==
\E c \in Core :
\E a \in Address :
\E v \in Value :
\/ do_bus_read_valid(c,a,v)
\/ complete_proc_read_invalid_shared(c,a,v)
\/ complete_proc_read_invalid_exclusive(c,a,v)
\/ do_bus_read_for_ownership_valid(c,a,v)
\/ proc_write_exclusive(c,a,v)
\/ issue_proc_write_shared(c,a,v)
\/ do_bus_upgrade(c,a)
\/ complete_proc_write_shared(c,a,v)
\/ evict_exclusive_or_shared(c,a)

Spec == (Init /\ [][Next]_vars)
=============================================================================
