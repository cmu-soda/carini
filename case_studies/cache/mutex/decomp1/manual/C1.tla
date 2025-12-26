---- MODULE C1 ----
EXTENDS Randomization

CONSTANTS Address, Core, Value

VARIABLES modified, exclusive, shared, invalid,
    good, in_read, in_write, issue_core, issue_addr, read_snoop, ownership_snoop, upgrade_snoop, transfer

vars == <<modified, exclusive, shared, invalid,
    good, in_read, in_write, issue_core, issue_addr, read_snoop, ownership_snoop, upgrade_snoop, transfer>>

CandSep ==
    /\ good

Init ==
    /\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]

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
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, exclusive, shared, invalid>>
    /\ in_read' = TRUE
    /\ issue_core' = c
    /\ issue_addr' = a
    /\ read_snoop' = [C \in Core |-> [A \in Address |-> (read_snoop[C][A] \/ (C # c /\ A = a))]] \* all other cores snoop on the read
    /\ good' = ~in_read /\ ~in_write \* multiple issues cannot happen concurrently
    /\ UNCHANGED<<in_write, ownership_snoop, upgrade_snoop, transfer>>
    /\ CandSep'

do_bus_read_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, exclusive, shared, invalid>>
    /\ read_snoop' = [read_snoop EXCEPT![c][a] = FALSE]
    /\ good' = read_snoop[c][a]
    /\ UNCHANGED<<in_read, in_write, issue_core, issue_addr, ownership_snoop, upgrade_snoop, transfer>>
    /\ CandSep'

do_bus_read_valid(c, a, v) ==
    /\ ~invalid[c][a]
    /\ ~modified[c][a]
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<invalid>>
    /\ read_snoop' = [read_snoop EXCEPT![c][a] = FALSE]
    /\ good' = read_snoop[c][a]
    /\ transfer' = TRUE
    /\ UNCHANGED<<in_read, in_write, issue_core, issue_addr, ownership_snoop, upgrade_snoop>>
    /\ CandSep'

do_bus_read_modified(c, a, v) ==
    /\ ~invalid[c][a]
    /\ modified[c][a]
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<invalid>>
    /\ read_snoop' = [read_snoop EXCEPT![c][a] = FALSE]
    /\ good' = read_snoop[c][a]
    /\ transfer' = TRUE
    /\ UNCHANGED<<in_read, in_write, issue_core, issue_addr, ownership_snoop, upgrade_snoop>>
    /\ CandSep'

complete_proc_read_invalid_shared(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ shared' = [shared EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<modified, exclusive>>
    /\ in_read' = FALSE \* issue complete
    /\ good' = /\ \A C \in Core, A \in Address : ~read_snoop[C][A] \* all snoops must be complete
               /\ issue_core = c
               /\ issue_addr = a
               /\ transfer
               /\ in_read
    /\ transfer' = FALSE
    /\ UNCHANGED<<in_write, issue_core, issue_addr, read_snoop, ownership_snoop, upgrade_snoop>>
    /\ CandSep'

complete_proc_read_invalid_exclusive(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<modified, shared>>
    /\ in_read' = FALSE \* issue complete
    /\ good' = /\ \A C \in Core, A \in Address : ~read_snoop[C][A] \* all snoops must be complete
               /\ issue_core = c
               /\ issue_addr = a
               /\ ~transfer
               /\ in_read
    /\ UNCHANGED<<in_write, issue_core, issue_addr, read_snoop, ownership_snoop, upgrade_snoop, transfer>>
    /\ CandSep'

issue_proc_write_invalid(c, a, v) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, exclusive, shared, invalid>>
    /\ in_write' = TRUE
    /\ issue_core' = c
    /\ issue_addr' = a
    /\ ownership_snoop' = [C \in Core |-> [A \in Address |-> (ownership_snoop[C][A] \/ (C # c /\ A = a))]] \* all other cores snoop on the ownerhsip request
    /\ good' = ~in_read /\ ~in_write \* multiple issues cannot happen concurrently
    /\ UNCHANGED<<in_read, read_snoop, upgrade_snoop, transfer>>
    /\ CandSep'

do_bus_read_for_ownership_invalid(c, a) ==
    /\ invalid[c][a]
    /\ UNCHANGED<<modified, exclusive, shared, invalid>>
    /\ ownership_snoop' = [ownership_snoop EXCEPT![c][a] = FALSE]
    /\ good' = ownership_snoop[c][a]
    /\ UNCHANGED<<in_read, in_write, issue_core, issue_addr, read_snoop, upgrade_snoop, transfer>>
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
    /\ transfer' = TRUE
    /\ UNCHANGED<<in_read, in_write, issue_core, issue_addr, read_snoop, upgrade_snoop>>
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
    /\ transfer' = TRUE
    /\ UNCHANGED<<in_read, in_write, issue_core, issue_addr, read_snoop, upgrade_snoop>>
    /\ CandSep'

complete_proc_write_invalid(c, a, v) ==
    /\ invalid[c][a]
    /\ invalid' = [invalid EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<exclusive, shared>>
    /\ in_write' = FALSE \* issue complete
    /\ good' = /\ \A C \in Core, A \in Address : ~ownership_snoop[C][A] \* all snoops must be complete
               /\ issue_core = c
               /\ issue_addr = a
               /\ in_write
    /\ transfer' = FALSE
    /\ UNCHANGED<<in_read, issue_core, issue_addr, read_snoop, ownership_snoop, upgrade_snoop>>
    /\ CandSep'

proc_write_exclusive(c, a, v) ==
    /\ exclusive[c][a]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<shared, invalid>>
    /\ UNCHANGED<<in_read, in_write, issue_core, issue_addr, read_snoop, ownership_snoop, upgrade_snoop, good, transfer>>
    /\ CandSep'

issue_proc_write_shared(c, a, v) ==
    /\ shared[c][a]
    /\ UNCHANGED<<modified, exclusive, shared, invalid>>
    /\ in_write' = TRUE
    /\ issue_core' = c
    /\ issue_addr' = a
    /\ upgrade_snoop' = [C \in Core |-> [A \in Address |-> (upgrade_snoop[C][A] \/ (C # c /\ A = a))]] \* all other cores snoop on the upgrade request
    /\ good' = ~in_read /\ ~in_write \* multiple issues cannot happen concurrently
    /\ UNCHANGED<<in_read, read_snoop, ownership_snoop, transfer>>
    /\ CandSep'

\* better name: invalidate_after_bus_upgrade_signal
\* another loc has upgraded so (c,a) must invalidate
do_bus_upgrade(c, a) ==
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ UNCHANGED<<modified, exclusive>>
    /\ upgrade_snoop' = [upgrade_snoop EXCEPT![c][a] = FALSE]
    /\ good' = upgrade_snoop[c][a]
    /\ UNCHANGED<<in_read, in_write, issue_core, issue_addr, read_snoop, ownership_snoop, transfer>>
    /\ CandSep'

complete_proc_write_shared(c, a, v) ==
    /\ shared[c][a]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ modified' = [modified EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<exclusive, invalid>>
    /\ in_write' = FALSE \* issue complete
    /\ upgrade_snoop' = [upgrade_snoop EXCEPT![c][a] = FALSE]
    /\ good' = /\ \A C \in Core, A \in Address : ~upgrade_snoop[C][A]
               /\ issue_core = c
               /\ issue_addr = a
               /\ in_write
    /\ UNCHANGED<<in_read, issue_core, issue_addr, read_snoop, ownership_snoop, transfer>>
    /\ CandSep'

evict_modified(c, a) ==
    /\ modified[c][a]
    /\ modified' = [modified EXCEPT![c][a] = FALSE]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<exclusive, shared>>
    /\ good' = ~in_read /\ ~in_write
    /\ UNCHANGED<<in_read, in_write, issue_core, issue_addr, read_snoop, ownership_snoop, upgrade_snoop, transfer>>
    /\ CandSep'

evict_exclusive_or_shared(c, a) ==
    /\ exclusive[c][a] \/ shared[c][a]
    /\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
    /\ shared' = [shared EXCEPT![c][a] = FALSE]
    /\ invalid' = [invalid EXCEPT![c][a] = TRUE]
    /\ UNCHANGED<<modified>>
    /\ good' = ~in_read /\ ~in_write
    /\ UNCHANGED<<in_read, in_write, issue_core, issue_addr, read_snoop, ownership_snoop, upgrade_snoop, transfer>>
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

Inv ==
    /\ Safety
    /\ ~(~exclusive[issue_core][issue_addr] /\ ~invalid[issue_core][issue_addr] /\ ~modified[issue_core][issue_addr] /\ ~shared[issue_core][issue_addr])
    /\ ~(\E address1 \in Address, core1 \in Core : exclusive[issue_core][issue_addr] /\ read_snoop[core1][address1])
    /\ ~(\E address1 \in Address, core1 \in Core : ~in_read /\ ~invalid[core1][address1] /\ ~modified[core1][address1] /\ read_snoop[core1][address1])
    /\ ~(\E address1 \in Address, core1 \in Core : issue_addr # address1 /\ ~invalid[core1][address1] /\ ~modified[core1][address1] /\ read_snoop[core1][address1])
    /\ ~(\E core1 \in Core : issue_core # core1 /\ exclusive[core1][issue_addr] /\ ~in_read /\ ~in_write)
    /\ ~(\E core0 \in Core : core0 # issue_core /\ ~in_read /\ ~in_write /\ modified[core0][issue_addr])
    /\ ~(\E core1 \in Core : issue_core # core1 /\ in_write /\ ~invalid[issue_core][issue_addr] /\ ~invalid[core1][issue_addr] /\ ~upgrade_snoop[core1][issue_addr])
    /\ ~(\E core0 \in Core : core0 # issue_core /\ in_read /\ ~invalid[core0][issue_addr] /\ ~invalid[issue_core][issue_addr])
    /\ ~(\E core1 \in Core : in_read /\ invalid[issue_core][issue_addr] /\ ~invalid[core1][issue_addr] /\ ~read_snoop[core1][issue_addr] /\ ~shared[core1][issue_addr])
    /\ ~(\E core2 \in Core : ~in_write /\ ~invalid[core2][issue_addr] /\ shared[issue_core][issue_addr] /\ ~shared[core2][issue_addr])
    /\ ~(\E address1 \in Address, core1 \in Core, core2 \in Core : issue_addr # address1 /\ core1 # core2 /\ ~invalid[core1][address1] /\ modified[core2][address1] /\ read_snoop[core2][address1])
    /\ ~(\E core1 \in Core : in_write /\ invalid[issue_core][issue_addr] /\ ~invalid[core1][issue_addr] /\ ~ownership_snoop[core1][issue_addr] /\ ~upgrade_snoop[core1][issue_addr])
    /\ ~(\E address0 \in Address, core1 \in Core, core2 \in Core : address0 # issue_addr /\ modified[core2][address0] /\ shared[core1][address0])
    /\ ~(\E C \in Core, A \in Address : invalid[C][A] /\ modified[C][A])
    /\ ~(\E C \in Core, A \in Address : invalid[C][A] /\ exclusive[C][A])
    /\ ~(\E address1 \in Address, core2 \in Core : ~invalid[issue_core][issue_addr] /\ ownership_snoop[core2][address1] /\ read_snoop[issue_core][issue_addr])
    /\ ~(\E address1 \in Address, core1 \in Core : modified[core1][address1] /\ upgrade_snoop[core1][address1])
    /\ ~(\E core1 \in Core : in_read /\ invalid[issue_core][issue_addr] /\ ~invalid[core1][issue_addr] /\ ~read_snoop[core1][issue_addr] /\ ~transfer)
    /\ ~(\E core1 \in Core : exclusive[issue_core][issue_addr] /\ shared[core1][issue_addr])
    /\ ~(\E address1 \in Address, core1 \in Core : exclusive[core1][address1] /\ upgrade_snoop[core1][address1])
    /\ ~(\E core1 \in Core : modified[issue_core][issue_addr] /\ shared[core1][issue_addr])
    /\ ~(\E address1 \in Address, core1 \in Core, core2 \in Core : issue_addr # address1 /\ exclusive[core1][address1] /\ shared[core2][address1])
    /\ ~upgrade_snoop[issue_core][issue_addr]
    /\ ~(\E core1 \in Core : ~in_write /\ upgrade_snoop[core1][issue_addr])
    /\ ~(\E core1 \in Core : ~shared[issue_core][issue_addr] /\ upgrade_snoop[core1][issue_addr])
    /\ ~(\E address1 \in Address : ~in_read /\ ~invalid[issue_core][issue_addr] /\ ownership_snoop[issue_core][address1] /\ shared[issue_core][address1])
    /\ ~(\E address1 \in Address, core1 \in Core : in_read /\ in_write /\ invalid[issue_core][issue_addr] /\ ~invalid[core1][address1])
    /\ ~(\E address1 \in Address, core1 \in Core : in_read /\ in_write /\ invalid[issue_core][issue_addr] /\ ownership_snoop[core1][address1] /\ transfer)
    /\ ~(\E address0 \in Address, core1 \in Core, core2 \in Core : core1 # core2 /\ ~in_read /\ ~invalid[core2][address0] /\ modified[core1][address0] /\ read_snoop[core1][address0])
    /\ ~(\E address1 \in Address, address2 \in Address, core1 \in Core, core2 \in Core : ~in_read /\ ~invalid[issue_core][issue_addr] /\ modified[core2][address2] /\ ownership_snoop[core1][address1] /\ read_snoop[core2][address2])
    /\ ~(\E address1 \in Address, core1 \in Core : issue_addr # address1 /\ upgrade_snoop[core1][address1])
    /\  ~ownership_snoop[issue_core][issue_addr]
    /\ ~(\E address1 \in Address, core1 \in Core, core2 \in Core : ~exclusive[core1][address1] /\ in_read /\ ~invalid[core1][address1] /\ ~modified[core1][address1] /\ ownership_snoop[core2][address1] /\ ~transfer)
    /\ ~(\E address1 \in Address, core0 \in Core : ~in_write /\ ownership_snoop[core0][address1])
    /\ ~(\E address1 \in Address, core1 \in Core : ownership_snoop[core1][address1] /\ shared[issue_core][issue_addr])
    /\ ~(\E address1 \in Address, core1 \in Core : in_read /\ ~invalid[core1][address1] /\ ownership_snoop[core1][address1])
    /\ ~(\E core0 \in Core, core2 \in Core : core0 # issue_core /\ exclusive[issue_core][issue_addr] /\ ownership_snoop[core2][issue_addr])
    /\ ~(\E core2 \in Core : in_read /\ ownership_snoop[core2][issue_addr])

TypeOK ==
    /\ modified \in [Core -> [Address -> BOOLEAN]]
    /\ exclusive \in [Core -> [Address -> BOOLEAN]]
    /\ shared \in [Core -> [Address -> BOOLEAN]]
    /\ invalid \in [Core -> [Address -> BOOLEAN]]

    /\ good \in BOOLEAN
    /\ in_read \in BOOLEAN
    /\ in_write \in BOOLEAN
    /\ issue_core \in Core
    /\ issue_addr \in Address
    /\ read_snoop \in [Core -> [Address -> BOOLEAN]]
    /\ ownership_snoop \in [Core -> [Address -> BOOLEAN]]
    /\ upgrade_snoop \in [Core -> [Address -> BOOLEAN]]
    /\ transfer \in BOOLEAN

num == 9
TypeOKRand ==
    /\ modified \in RandomSubset(num, [Core -> [Address -> BOOLEAN]])
    /\ exclusive \in RandomSubset(num, [Core -> [Address -> BOOLEAN]])
    /\ shared \in RandomSubset(num, [Core -> [Address -> BOOLEAN]])
    /\ invalid \in RandomSubset(num, [Core -> [Address -> BOOLEAN]])

    /\ good \in BOOLEAN
    /\ in_read \in BOOLEAN
    /\ in_write \in BOOLEAN
    /\ issue_core \in Core
    /\ issue_addr \in Address
    /\ read_snoop \in RandomSubset(num, [Core -> [Address -> BOOLEAN]])
    /\ ownership_snoop \in RandomSubset(num, [Core -> [Address -> BOOLEAN]])
    /\ upgrade_snoop \in RandomSubset(num, [Core -> [Address -> BOOLEAN]])
    /\ transfer \in BOOLEAN

IISpec == TypeOKRand /\ Inv /\ [][Next]_vars

======
