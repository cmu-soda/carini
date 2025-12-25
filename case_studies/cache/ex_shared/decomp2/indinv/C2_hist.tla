--------------------------- MODULE C2_hist ---------------------------

CONSTANTS Address, Core, Value

VARIABLES memory, second_not_reading_shared, complete_write_after_ownership, once_ipwi, once_ownership, once_cpwi_core, once_ipws, once_cpwi_addr, once_cpwi_value, issue_proc_write_val, once_bus_read_or_ownership, modified, once_cprie_or_iwps, issue_proc_write_core, in_invalid_read, any_dbrv, cache, issue_proc_write_addr, once_cpris_core, write_or_read_for_ownership, not_reading_shared, bus_read, cprie_ex, bus_in_use, once_dbrv_addr, proc_read_after_bus_read, proc_read, once_cprie, invalid, any_cprie, not_reading_shared_ex, once_cpris_val, in_read_write, once_dbrv_core

vars == <<memory, second_not_reading_shared, complete_write_after_ownership, once_ipwi, once_ownership, once_cpwi_core, once_ipws, once_cpwi_addr, once_cpwi_value, issue_proc_write_val, once_bus_read_or_ownership, modified, once_cprie_or_iwps, issue_proc_write_core, in_invalid_read, any_dbrv, cache, issue_proc_write_addr, once_cpris_core, write_or_read_for_ownership, not_reading_shared, bus_read, cprie_ex, bus_in_use, once_dbrv_addr, proc_read_after_bus_read, proc_read, once_cprie, invalid, any_cprie, not_reading_shared_ex, once_cpris_val, in_read_write, once_dbrv_core>>

CandSep ==
/\ \A var0 \in Core : (complete_write_after_ownership[var0]) => (write_or_read_for_ownership[var0])
/\ \A var0 \in Value : (once_cpris_val[var0]) => (once_bus_read_or_ownership[var0])
/\ \A var0 \in Address : (once_ownership[var0]) => (once_ipwi[var0])
/\ \A var0 \in Address : (in_read_write[var0]) => (in_invalid_read[var0])
/\ \A var0 \in Value : (once_cpwi_value[var0]) => (issue_proc_write_val[var0])
/\ \A var0 \in Address : (once_cpwi_addr[var0]) => (issue_proc_write_addr[var0])
/\ \A var0 \in Core : (once_cpwi_core[var0]) => (issue_proc_write_core[var0])

Init ==
/\ (memory \in [Address -> Value])
/\ (cache \in [Core -> [Address -> Value]])
/\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
/\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]
/\ proc_read = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_in_use = FALSE
/\ bus_read = [c \in Core |-> [a \in Address |-> FALSE]]
/\ issue_proc_write_addr = [ x0 \in Address |-> FALSE]
/\ complete_write_after_ownership = [ x0 \in Core |-> FALSE]
/\ write_or_read_for_ownership = [ x0 \in Core |-> FALSE]
/\ once_ipwi = [ x0 \in Address |-> FALSE]
/\ once_ownership = [ x0 \in Address |-> FALSE]
/\ once_cpwi_core = [ x0 \in Core |-> FALSE]
/\ once_cpwi_addr = [ x0 \in Address |-> FALSE]
/\ once_cpwi_value = [ x0 \in Value |-> FALSE]
/\ issue_proc_write_val = [ x0 \in Value |-> FALSE]
/\ once_bus_read_or_ownership = [ x0 \in Value |-> FALSE]
/\ issue_proc_write_core = [ x0 \in Core |-> FALSE]
/\ once_cpris_val = [ x0 \in Value |-> FALSE]
/\ in_invalid_read = [ x0 \in Address |-> FALSE]
/\ in_read_write = [ x0 \in Address |-> FALSE]
/\ second_not_reading_shared = [ x0 \in Core |-> FALSE]
/\ once_cpris_core = [ x0 \in Core |-> FALSE]
/\ any_dbrv = FALSE
/\ not_reading_shared = [ x0 \in Core |-> FALSE]
/\ cprie_ex = [ x0 \in Address |-> FALSE]
/\ once_dbrv_addr = [ x0 \in Address |-> FALSE]
/\ once_ipws = [ x0 \in Address |-> FALSE]
/\ proc_read_after_bus_read = [ x0 \in Core |-> FALSE]
/\ once_cprie = [ x0 \in Core |-> FALSE]
/\ any_cprie = FALSE
/\ once_cprie_or_iwps = [ x0 \in Core |-> FALSE]
/\ not_reading_shared_ex = [ x0 \in Core |-> FALSE]
/\ once_dbrv_core = [ x0 \in Core |-> FALSE]

issue_proc_read_invalid(c,a) ==
/\ invalid[c][a]
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_read' = [proc_read EXCEPT![c][a] = TRUE]
/\ bus_read' = [C \in Core |-> [A \in Address |-> (bus_read[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<memory,cache,modified,invalid>>
/\ UNCHANGED<<issue_proc_write_addr, complete_write_after_ownership, write_or_read_for_ownership, once_ipwi, once_ownership, once_cpwi_core, once_cpwi_addr, once_cpwi_value, issue_proc_write_val, once_bus_read_or_ownership, issue_proc_write_core, once_cpris_val, in_invalid_read, in_read_write>>
/\ CandSep'
/\ UNCHANGED<<second_not_reading_shared, once_cpris_core, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, once_cprie_or_iwps, not_reading_shared_ex, once_dbrv_core, any_dbrv>>
/\ CandSep'

do_bus_read_invalid(c,a) ==
/\ bus_read[c][a]
/\ invalid[c][a]
/\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<memory,cache,modified,invalid,proc_read,bus_in_use>>
/\ UNCHANGED<<issue_proc_write_addr, complete_write_after_ownership, write_or_read_for_ownership, once_ipwi, once_ownership, once_cpwi_core, once_cpwi_addr, once_cpwi_value, issue_proc_write_val, once_bus_read_or_ownership, issue_proc_write_core, once_cpris_val, in_invalid_read, in_read_write>>
/\ CandSep'
/\ UNCHANGED<<second_not_reading_shared, once_cpris_core, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, once_cprie_or_iwps, not_reading_shared_ex, once_dbrv_core, any_dbrv>>
/\ CandSep'

do_bus_read_valid(c,a,v) ==
/\ bus_read[c][a]
/\ ~(invalid[c][a])
/\ cache[c][a] = v
/\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ (modified[c][a] => memory' = [memory EXCEPT![a] = v])
/\ (~(modified[c][a]) => memory' = memory)
/\ UNCHANGED <<cache,invalid,proc_read,bus_in_use>>
/\ once_bus_read_or_ownership' = [once_bus_read_or_ownership EXCEPT ![v] = TRUE]
/\ in_invalid_read' = [in_invalid_read EXCEPT ![a] = TRUE]
/\ in_read_write' = [in_read_write EXCEPT ![a] = TRUE]
/\ UNCHANGED<<issue_proc_write_addr, complete_write_after_ownership, write_or_read_for_ownership, once_ipwi, once_ownership, once_cpwi_core, once_cpwi_addr, once_cpwi_value, issue_proc_write_val, issue_proc_write_core, once_cpris_val>>
/\ CandSep'
/\ any_dbrv' = TRUE
/\ not_reading_shared' = [not_reading_shared EXCEPT ![c] = FALSE]
/\ once_dbrv_addr' = [once_dbrv_addr EXCEPT ![a] = TRUE]
/\ not_reading_shared_ex' = [[x0 \in Core |-> once_cprie[c]] EXCEPT ![c] = FALSE]
/\ once_dbrv_core' = [once_dbrv_core EXCEPT ![c] = TRUE]
/\ UNCHANGED<<second_not_reading_shared, once_cpris_core, cprie_ex, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, once_cprie_or_iwps>>
/\ CandSep'

complete_proc_read_invalid_shared(c,a,v) ==
/\ invalid[c][a]
/\ proc_read[c][a]
/\ (\A C \in Core : (\A A \in Address : ~(bus_read[C][A])))
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ bus_in_use' = FALSE
/\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<memory,modified,bus_read>>
/\ once_cpris_val' = [once_cpris_val EXCEPT ![v] = TRUE]
/\ in_read_write' = [x0 \in Address |-> FALSE]
/\ UNCHANGED<<issue_proc_write_addr, complete_write_after_ownership, write_or_read_for_ownership, once_ipwi, once_ownership, once_cpwi_core, once_cpwi_addr, once_cpwi_value, issue_proc_write_val, once_bus_read_or_ownership, issue_proc_write_core, in_invalid_read>>
/\ CandSep'
/\ once_cpris_core' = [once_cpris_core EXCEPT ![c] = TRUE]
/\ UNCHANGED<<second_not_reading_shared, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, once_cprie_or_iwps, not_reading_shared_ex, once_dbrv_core>>
/\ CandSep'

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ invalid[c][a]
/\ proc_read[c][a]
/\ (\A C \in Core : (\A A \in Address : ~(bus_read[C][A])))
/\ memory[a] = v
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ bus_in_use' = FALSE
/\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<memory,modified,bus_read>>
/\ in_invalid_read' = [in_invalid_read EXCEPT ![a] = FALSE]
/\ UNCHANGED<<issue_proc_write_addr, complete_write_after_ownership, write_or_read_for_ownership, once_ipwi, once_ownership, once_cpwi_core, once_cpwi_addr, once_cpwi_value, issue_proc_write_val, once_bus_read_or_ownership, issue_proc_write_core, once_cpris_val, in_read_write>>
/\ CandSep'
/\ second_not_reading_shared' = [second_not_reading_shared EXCEPT ![c] = not_reading_shared[c]]
/\ not_reading_shared' = [not_reading_shared EXCEPT ![c] = TRUE]
/\ cprie_ex' = [[x0 \in Address |-> TRUE] EXCEPT ![a] = FALSE]
/\ proc_read_after_bus_read' = [proc_read_after_bus_read EXCEPT ![c] = any_dbrv]
/\ once_cprie' = [once_cprie EXCEPT ![c] = TRUE]
/\ any_cprie' = TRUE
/\ once_cprie_or_iwps' = [once_cprie_or_iwps EXCEPT ![c] = TRUE]
/\ UNCHANGED<<once_cpris_core, any_dbrv, once_dbrv_addr, once_ipws, not_reading_shared_ex, once_dbrv_core>>
/\ CandSep'

issue_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ UNCHANGED <<memory,cache,modified,invalid,proc_read,bus_read>>
/\ issue_proc_write_addr' = [issue_proc_write_addr EXCEPT ![a] = TRUE]
/\ write_or_read_for_ownership' = [write_or_read_for_ownership EXCEPT ![c] = TRUE]
/\ once_ipwi' = [once_ipwi EXCEPT ![a] = TRUE]
/\ issue_proc_write_val' = [issue_proc_write_val EXCEPT ![v] = TRUE]
/\ issue_proc_write_core' = [issue_proc_write_core EXCEPT ![c] = TRUE]
/\ UNCHANGED<<complete_write_after_ownership, once_ownership, once_cpwi_core, once_cpwi_addr, once_cpwi_value, once_bus_read_or_ownership, once_cpris_val, in_invalid_read, in_read_write>>
/\ CandSep'
/\ UNCHANGED<<second_not_reading_shared, once_cpris_core, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, once_cprie_or_iwps, not_reading_shared_ex, once_dbrv_core>>
/\ CandSep'

do_bus_read_for_ownership_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,invalid,proc_read,bus_in_use,bus_read>>
/\ write_or_read_for_ownership' = [write_or_read_for_ownership EXCEPT ![c] = TRUE]
/\ UNCHANGED<<issue_proc_write_addr, complete_write_after_ownership, once_ipwi, once_ownership, once_cpwi_core, once_cpwi_addr, once_cpwi_value, issue_proc_write_val, once_bus_read_or_ownership, issue_proc_write_core, once_cpris_val, in_invalid_read, in_read_write>>
/\ CandSep'
/\ UNCHANGED<<second_not_reading_shared, once_cpris_core, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, once_cprie_or_iwps, not_reading_shared_ex, once_dbrv_core>>
/\ CandSep'

do_bus_read_for_ownership_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ cache[c][a] = v
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ (modified[c][a] => memory' = [memory EXCEPT![a] = v])
/\ (~(modified[c][a]) => memory' = memory)
/\ UNCHANGED <<cache,proc_read,bus_in_use,bus_read>>
/\ write_or_read_for_ownership' = [write_or_read_for_ownership EXCEPT ![c] = TRUE]
/\ once_ownership' = [once_ownership EXCEPT ![a] = TRUE]
/\ once_bus_read_or_ownership' = [once_bus_read_or_ownership EXCEPT ![v] = TRUE]
/\ UNCHANGED<<issue_proc_write_addr, complete_write_after_ownership, once_ipwi, once_cpwi_core, once_cpwi_addr, once_cpwi_value, issue_proc_write_val, issue_proc_write_core, once_cpris_val, in_invalid_read, in_read_write>>
/\ CandSep'
/\ UNCHANGED<<second_not_reading_shared, once_cpris_core, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, once_cprie_or_iwps, not_reading_shared_ex, once_dbrv_core>>
/\ CandSep'

complete_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ bus_in_use' = FALSE
/\ UNCHANGED <<memory,proc_read,bus_read>>
/\ complete_write_after_ownership' = [x0 \in Core |-> write_or_read_for_ownership[c]]
/\ once_cpwi_core' = [once_cpwi_core EXCEPT ![c] = TRUE]
/\ once_cpwi_addr' = [once_cpwi_addr EXCEPT ![a] = TRUE]
/\ once_cpwi_value' = [once_cpwi_value EXCEPT ![v] = TRUE]
/\ in_read_write' = [x0 \in Address |-> FALSE]
/\ UNCHANGED<<issue_proc_write_addr, write_or_read_for_ownership, once_ipwi, once_ownership, issue_proc_write_val, once_bus_read_or_ownership, issue_proc_write_core, once_cpris_val, in_invalid_read>>
/\ CandSep'
/\ UNCHANGED<<second_not_reading_shared, once_cpris_core, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, once_cprie_or_iwps, not_reading_shared_ex, once_dbrv_core>>
/\ CandSep'

proc_write_exclusive(c,a,v) ==
/\ ~(bus_in_use)
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,invalid,proc_read,bus_in_use,bus_read>>
/\ UNCHANGED<<issue_proc_write_addr, complete_write_after_ownership, write_or_read_for_ownership, once_ipwi, once_ownership, once_cpwi_core, once_cpwi_addr, once_cpwi_value, issue_proc_write_val, once_bus_read_or_ownership, issue_proc_write_core, once_cpris_val, in_invalid_read, in_read_write>>
/\ CandSep'
/\ UNCHANGED<<second_not_reading_shared, once_cpris_core, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, once_cprie_or_iwps, not_reading_shared_ex, once_dbrv_core>>
/\ CandSep'

issue_proc_write_shared(c,a,v) ==
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ UNCHANGED <<memory,cache,modified,invalid,proc_read,bus_read>>
/\ issue_proc_write_addr' = [issue_proc_write_addr EXCEPT ![a] = TRUE]
/\ issue_proc_write_val' = [issue_proc_write_val EXCEPT ![v] = TRUE]
/\ issue_proc_write_core' = [issue_proc_write_core EXCEPT ![c] = TRUE]
/\ UNCHANGED<<complete_write_after_ownership, write_or_read_for_ownership, once_ipwi, once_ownership, once_cpwi_core, once_cpwi_addr, once_cpwi_value, once_bus_read_or_ownership, once_cpris_val, in_invalid_read, in_read_write>>
/\ CandSep'
/\ once_ipws' = [once_ipws EXCEPT ![a] = TRUE]
/\ once_cprie_or_iwps' = [once_cprie_or_iwps EXCEPT ![c] = TRUE]
/\ UNCHANGED<<second_not_reading_shared, once_cpris_core, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, proc_read_after_bus_read, once_cprie, any_cprie, not_reading_shared_ex, once_dbrv_core>>
/\ CandSep'

do_bus_upgrade(c,a) ==
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<memory,cache,modified,proc_read,bus_in_use,bus_read>>
/\ UNCHANGED<<issue_proc_write_addr, complete_write_after_ownership, write_or_read_for_ownership, once_ipwi, once_ownership, once_cpwi_core, once_cpwi_addr, once_cpwi_value, issue_proc_write_val, once_bus_read_or_ownership, issue_proc_write_core, once_cpris_val, in_invalid_read, in_read_write>>
/\ CandSep'
/\ UNCHANGED<<second_not_reading_shared, once_cpris_core, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, once_cprie_or_iwps, not_reading_shared_ex, once_dbrv_core>>
/\ CandSep'

complete_proc_write_shared(c,a,v) ==
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ bus_in_use' = FALSE
/\ UNCHANGED <<memory,invalid,proc_read,bus_read>>
/\ UNCHANGED<<issue_proc_write_addr, complete_write_after_ownership, write_or_read_for_ownership, once_ipwi, once_ownership, once_cpwi_core, once_cpwi_addr, once_cpwi_value, issue_proc_write_val, once_bus_read_or_ownership, issue_proc_write_core, once_cpris_val, in_invalid_read, in_read_write>>
/\ CandSep'
/\ UNCHANGED<<second_not_reading_shared, once_cpris_core, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, once_cprie_or_iwps, not_reading_shared_ex, once_dbrv_core>>
/\ CandSep'

evict_modified(c,a) ==
/\ ~(bus_in_use)
/\ modified[c][a]
/\ memory' = [memory EXCEPT![a] = cache[c][a]]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<cache,proc_read,bus_in_use,bus_read>>
/\ UNCHANGED<<issue_proc_write_addr, complete_write_after_ownership, write_or_read_for_ownership, once_ipwi, once_ownership, once_cpwi_core, once_cpwi_addr, once_cpwi_value, issue_proc_write_val, once_bus_read_or_ownership, issue_proc_write_core, once_cpris_val, in_invalid_read, in_read_write>>
/\ CandSep'
/\ UNCHANGED<<second_not_reading_shared, once_cpris_core, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, once_cprie_or_iwps, not_reading_shared_ex, once_dbrv_core>>
/\ CandSep'

evict_exclusive_or_shared(c,a) ==
/\ ~(bus_in_use)
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<memory,cache,modified,proc_read,bus_in_use,bus_read>>
/\ UNCHANGED<<issue_proc_write_addr, complete_write_after_ownership, write_or_read_for_ownership, once_ipwi, once_ownership, once_cpwi_core, once_cpwi_addr, once_cpwi_value, issue_proc_write_val, once_bus_read_or_ownership, issue_proc_write_core, once_cpris_val, in_invalid_read, in_read_write>>
/\ CandSep'
/\ UNCHANGED<<second_not_reading_shared, once_cpris_core, any_dbrv, not_reading_shared, cprie_ex, once_dbrv_addr, once_ipws, proc_read_after_bus_read, once_cprie, any_cprie, once_cprie_or_iwps, not_reading_shared_ex, once_dbrv_core>>
/\ CandSep'

Next ==
\E c \in Core :
\E a \in Address :
\E v \in Value :
\/ issue_proc_read_invalid(c,a)
\/ do_bus_read_invalid(c,a)
\/ do_bus_read_valid(c,a,v)
\/ complete_proc_read_invalid_shared(c,a,v)
\/ complete_proc_read_invalid_exclusive(c,a,v)
\/ issue_proc_write_invalid(c,a,v)
\/ do_bus_read_for_ownership_invalid(c,a)
\/ do_bus_read_for_ownership_valid(c,a,v)
\/ complete_proc_write_invalid(c,a,v)
\/ proc_write_exclusive(c,a,v)
\/ issue_proc_write_shared(c,a,v)
\/ do_bus_upgrade(c,a)
\/ complete_proc_write_shared(c,a,v)
\/ evict_modified(c,a)
\/ evict_exclusive_or_shared(c,a)

Spec == (Init /\ [][Next]_vars)

Safety ==
/\ \A var0 \in Core : (any_cprie) => ((once_dbrv_core[var0]) => (once_cprie_or_iwps[var0]))
/\ \A var0 \in Core : (second_not_reading_shared[var0]) => (not_reading_shared[var0])
/\ \A var0 \in Core : (proc_read_after_bus_read[var0]) => (~(any_dbrv))
/\ \A var0 \in Address : (cprie_ex[var0]) => ((once_dbrv_addr[var0]) => (once_ipws[var0]))
/\ \A var0 \in Core : (once_cpris_core[var0]) => (any_dbrv)
/\ \A var0 \in Core : (once_cprie[var0]) => (~(not_reading_shared_ex[var0]))
=============================================================================
