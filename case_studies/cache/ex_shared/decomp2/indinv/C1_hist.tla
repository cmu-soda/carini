--------------------------- MODULE C1_hist ---------------------------


CONSTANTS Address, Core, Value

VARIABLES shared, second_not_reading_shared, once_cpris, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, exclusive, once_cprie_or_iwps, not_reading_shared_ex, once_dbrv_core

vars == <<shared, second_not_reading_shared, once_cpris, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, exclusive, once_cprie_or_iwps, not_reading_shared_ex, once_dbrv_core>>

CandSep ==
/\ \A var0 \in Core : (any_cprie[var0]) => ((once_dbrv_core[var0]) => (once_cprie_or_iwps[var0]))
/\ \A var0 \in Core : (second_not_reading_shared[var0]) => (not_reading_shared[var0])
/\ \A var0 \in Core : (proc_read_after_bus_read[var0]) => (~(any_dbrv))
/\ \A var0 \in Address : (cprie_ex[var0]) => ((once_dbrv_addr[var0]) => (once_ipws[var0]))
/\ \A var0 \in Core : (once_cpris[var0]) => (any_dbrv)
/\ \A var0 \in Core : (once_cprie[var0]) => (~(not_reading_shared_ex[var0]))

Init ==
/\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
/\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
/\ second_not_reading_shared = [ x0 \in Core |-> FALSE]
/\ once_cpris = [ x0 \in Core |-> FALSE]
/\ any_dbrv = FALSE
/\ not_reading_shared = [ x0 \in Core |-> FALSE]
/\ cprie_ex = [ x0 \in Address |-> FALSE]
/\ once_dbrv_addr = [ x0 \in Address |-> FALSE]
/\ once_ipws = [ x0 \in Address |-> FALSE]
/\ proc_read_after_bus_read = [ x0 \in Core |-> FALSE]
/\ once_cprie = [ x0 \in Core |-> FALSE]
/\ any_cprie = [ x0 \in Core |-> FALSE]
/\ once_cprie_or_iwps = [ x0 \in Core |-> FALSE]
/\ not_reading_shared_ex = [ x0 \in Core |-> FALSE]
/\ once_dbrv_core = [ x0 \in Core |-> FALSE]

do_bus_read_valid(c,a,v) ==
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ any_dbrv' = TRUE
/\ not_reading_shared' = [not_reading_shared EXCEPT ![c] = FALSE]
/\ once_dbrv_addr' = [once_dbrv_addr EXCEPT ![a] = TRUE]
/\ not_reading_shared_ex' = [[x0 \in Core |-> once_cprie[c]] EXCEPT ![c] = FALSE]
/\ once_dbrv_core' = [once_dbrv_core EXCEPT ![c] = TRUE]
/\ UNCHANGED<<second_not_reading_shared, once_cpris, cprie_ex, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, once_cprie_or_iwps>>
/\ CandSep'
\*/\ any_cprie[c] => once_cprie_or_iwps[c]
\*/\ ~second_not_reading_shared[c]
\*/\ \A C \in Core : ~proc_read_after_bus_read[C]
\*/\ cprie_ex[a] => once_ipws[a]
\*/\ \A C \in Core : (once_cprie[C] /\ C # c) => ~once_cprie[c]

complete_proc_read_invalid_shared(c,a,v) ==
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<exclusive>>
/\ once_cpris' = [once_cpris EXCEPT ![c] = TRUE]
/\ UNCHANGED<<second_not_reading_shared, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, once_cprie_or_iwps, not_reading_shared_ex, once_dbrv_core>>
/\ CandSep'

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<shared>>
/\ second_not_reading_shared' = [second_not_reading_shared EXCEPT ![c] = not_reading_shared[c]]
/\ not_reading_shared' = [not_reading_shared EXCEPT ![c] = TRUE]
/\ cprie_ex' = [[x0 \in Address |-> TRUE] EXCEPT ![a] = FALSE]
/\ proc_read_after_bus_read' = [proc_read_after_bus_read EXCEPT ![c] = any_dbrv]
/\ once_cprie' = [once_cprie EXCEPT ![c] = TRUE]
/\ any_cprie' = [x0 \in Core |-> TRUE]
/\ once_cprie_or_iwps' = [once_cprie_or_iwps EXCEPT ![c] = TRUE]
/\ UNCHANGED<<once_cpris, any_dbrv, once_dbrv_addr, once_ipws, not_reading_shared_ex, once_dbrv_core>>
/\ CandSep'
\*/\ \A C \in Core : (once_dbrv_core[C] /\ C # c) => once_cprie_or_iwps[C]
\*/\ ~any_dbrv
\*/\ \A A \in Address : (once_dbrv_addr[A] /\ A # A) => once_ipws[A]
\*/\ ~not_reading_shared_ex[c]

do_bus_read_for_ownership_valid(c,a,v) ==
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ UNCHANGED<<second_not_reading_shared, once_cpris, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, once_cprie_or_iwps, not_reading_shared_ex, once_dbrv_core>>
/\ CandSep'

proc_write_exclusive(c,a,v) ==
/\ exclusive[c][a]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<shared>>
/\ UNCHANGED<<second_not_reading_shared, once_cpris, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, once_cprie_or_iwps, not_reading_shared_ex, once_dbrv_core>>
/\ CandSep'

issue_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ UNCHANGED <<exclusive,shared>>
/\ once_ipws' = [once_ipws EXCEPT ![a] = TRUE]
/\ once_cprie_or_iwps' = [once_cprie_or_iwps EXCEPT ![c] = TRUE]
/\ UNCHANGED<<second_not_reading_shared, once_cpris, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, proc_read_after_bus_read, once_cprie, any_cprie, not_reading_shared_ex, once_dbrv_core>>
/\ CandSep'

complete_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<exclusive>>
/\ UNCHANGED<<second_not_reading_shared, once_cpris, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, once_cprie_or_iwps, not_reading_shared_ex, once_dbrv_core>>
/\ CandSep'

evict_exclusive_or_shared(c,a) ==
/\ (exclusive[c][a] \/ shared[c][a])
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ UNCHANGED<<second_not_reading_shared, once_cpris, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, once_cprie_or_iwps, not_reading_shared_ex, once_dbrv_core>>
/\ CandSep'

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
\/ complete_proc_write_shared(c,a,v)
\/ evict_exclusive_or_shared(c,a)

Spec == (Init /\ [][Next]_vars)

Safety == (\A C \in Core, A \in Address : ~((exclusive[C][A] /\ shared[C][A])))


TypeOK ==
/\ exclusive \in [Core -> [Address -> BOOLEAN]]
/\ shared \in [Core -> [Address -> BOOLEAN]]
/\ second_not_reading_shared \in [Core -> BOOLEAN]
/\ once_cpris \in [Core -> BOOLEAN]
/\ any_dbrv \in BOOLEAN
/\ not_reading_shared \in [Core -> BOOLEAN]
/\ cprie_ex \in [Address -> BOOLEAN]
/\ once_dbrv_addr \in [Address -> BOOLEAN]
/\ once_ipws \in [Address -> BOOLEAN]
/\ proc_read_after_bus_read \in [Core -> BOOLEAN]
/\ once_cprie \in [Core -> BOOLEAN]
/\ any_cprie \in [Core -> BOOLEAN]
/\ once_cprie_or_iwps \in [Core -> BOOLEAN]
/\ not_reading_shared_ex \in [Core -> BOOLEAN]
/\ once_dbrv_core \in [Core -> BOOLEAN]

Inv ==
/\ \A C \in Core : ~proc_read_after_bus_read[C]
/\ ~(\E core0 \in Core : ~any_cprie[core0] /\ once_cprie[core0])
/\ ~(\E address0 \in Address, core0 \in Core : ~any_dbrv /\ shared[core0][address0])
/\ ~(\E core0 \in Core, core1 \in Core : any_cprie[core0] /\ ~any_cprie[core1])
/\ ~(\E core1 \in Core : ~any_dbrv /\ ~not_reading_shared[core1] /\ once_cprie_or_iwps[core1])
/\ ~(\E address0 \in Address, address1 \in Address, core0 \in Core : address0 # address1 /\ any_cprie[core0] /\ ~cprie_ex[address0] /\ ~cprie_ex[address1])
/\ ~(\E core0 \in Core : not_reading_shared[core0] /\ ~once_cprie[core0])
/\ ~(\E core0 \in Core : any_dbrv /\ not_reading_shared[core0])
/\ ~(\E address1 \in Address : ~any_dbrv /\ once_ipws[address1])
/\ ~(\E address0 \in Address, core0 \in Core : any_cprie[core0] /\ any_dbrv /\ ~cprie_ex[address0] /\ ~once_dbrv_addr[address0])
/\ ~(\E core0 \in Core : ~any_dbrv /\ once_dbrv_core[core0])
/\ ~(\E address0 \in Address, core0 \in Core : exclusive[core0][address0] /\ ~not_reading_shared[core0])
\*/\ ~(\E address0 \in Address, core0 \in Core : cprie_ex[address0] /\ exclusive[core0][address0] /\ once_cprie_or_iwps[core0] /\ ~second_not_reading_shared[core0]) \* invalid

\*/\ \A C \in Core : ~proc_read_after_bus_read[C]
\*/\ ~(\E address0 \in Address, core0 \in Core : ~any_cprie[core0] /\ exclusive[core0][address0])
\*/\ ~(\E core0 \in Core : ~any_cprie[core0] /\ once_cprie[core0])
\*/\ ~(\E address0 \in Address, core0 \in Core : ~any_dbrv /\ shared[core0][address0])
\*/\ ~(\E core0 \in Core, core1 \in Core : any_cprie[core0] /\ ~any_cprie[core1])
\*/\ ~(\E address0 \in Address, address1 \in Address, core0 \in Core : address0 # address1 /\ any_cprie[core0] /\ ~cprie_ex[address0] /\ ~cprie_ex[address1])
\*/\ ~(\E core0 \in Core : not_reading_shared[core0] /\ ~once_cprie[core0])
\*/\ ~(\E address1 \in Address : ~any_dbrv /\ once_ipws[address1])
\*/*/\ ~(\E address0 \in Address, core0 \in Core : any_cprie[core0] /\ any_dbrv /\ ~once_dbrv_addr[address0]) \* invalid
\*/\ ~(\E core1 \in Core : ~any_dbrv /\ ~not_reading_shared[core1] /\ once_cprie_or_iwps[core1])
\*/\ ~(\E core0 \in Core : any_dbrv /\ not_reading_shared[core0])
\*/\ ~(\E address0 \in Address, core0 \in Core : any_dbrv /\ exclusive[core0][address0])

IISpec == (TypeOK /\ Inv /\ [][Next]_vars)

=============================================================================
