--------------------------- MODULE C1_hist ---------------------------


CONSTANTS Address, Core, Value

VARIABLES memory, Fluent80_2, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, modified, Fluent64_14, cache, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, invalid, Fluent16_9, Fluent63_14, Fluent15_9

vars == <<memory, Fluent80_2, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, modified, Fluent64_14, cache, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, invalid, Fluent16_9, Fluent63_14, Fluent15_9>>

CandSep ==
/\ \A var0 \in Value : (Fluent105_10[var0]) => (~(Fluent106_10[var0]))
/\ \A var0 \in Address : (Fluent49_1[var0]) => (Fluent48_1[var0])
/\ \A var0 \in Value : \E var1 \in Core : (Fluent46_5[var1][var0]) => (Fluent47_5[var1])
/\ \A var0 \in Address : (Fluent94_18[var0]) => (Fluent95_18[var0])
/\ \A var0 \in Value : (Fluent81_2[var0]) => (Fluent80_2[var0])
/\ \A var0 \in Core : (Fluent77_16[var0]) => (Fluent76_16[var0])
/\ \A var0 \in Core : (Fluent5_17[var0]) => (Fluent6_17[var0])
/\ \A var0 \in Address : (Fluent68_14[var0]) => (Fluent69_14[var0])
/\ \A var0 \in Core : (Fluent18_0[var0]) => (Fluent19_0[var0])
/\ \A var0 \in Address : (Fluent16_9[var0]) => (Fluent15_9[var0])
/\ \A var0 \in Core : (Fluent38_0[var0]) => (Fluent39_0[var0])
/\ \A var0 \in Address : (Fluent93_4[var0]) => (Fluent92_4[var0])
/\ \A var0 \in Core : (Fluent26_0[var0]) => (~(Fluent25_0[var0]))
/\ \A var0 \in Address : (Fluent64_14[var0]) => (Fluent63_14[var0])
/\ \A var0 \in Core : (Fluent74_0[var0]) => (Fluent73_0[var0])

Init ==
/\ (memory \in [Address -> Value])
/\ (cache \in [Core -> [Address -> Value]])
/\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
/\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]
/\ Fluent80_2 = [ x0 \in Value |-> FALSE]
/\ Fluent105_10 = [ x0 \in Value |-> FALSE]
/\ Fluent77_16 = [ x0 \in Core |-> FALSE]
/\ Fluent81_2 = [ x0 \in Value |-> FALSE]
/\ Fluent5_17 = [ x0 \in Core |-> FALSE]
/\ Fluent48_1 = [ x0 \in Address |-> FALSE]
/\ Fluent95_18 = [ x0 \in Address |-> FALSE]
/\ Fluent26_0 = [ x0 \in Core |-> FALSE]
/\ Fluent49_1 = [ x0 \in Address |-> FALSE]
/\ Fluent68_14 = [ x0 \in Address |-> FALSE]
/\ Fluent25_0 = [ x0 \in Core |-> FALSE]
/\ Fluent46_5 = [ x0 \in Core |-> [ x1 \in Value |-> FALSE]]
/\ Fluent47_5 = [ x0 \in Core |-> FALSE]
/\ Fluent64_14 = [ x0 \in Address |-> FALSE]
/\ Fluent76_16 = [ x0 \in Core |-> FALSE]
/\ Fluent106_10 = [ x0 \in Value |-> FALSE]
/\ Fluent73_0 = [ x0 \in Core |-> FALSE]
/\ Fluent93_4 = [ x0 \in Address |-> FALSE]
/\ Fluent74_0 = [ x0 \in Core |-> FALSE]
/\ Fluent6_17 = [ x0 \in Core |-> FALSE]
/\ Fluent92_4 = [ x0 \in Address |-> FALSE]
/\ Fluent38_0 = [ x0 \in Core |-> FALSE]
/\ Fluent39_0 = [ x0 \in Core |-> FALSE]
/\ Fluent94_18 = [ x0 \in Address |-> FALSE]
/\ Fluent19_0 = [ x0 \in Core |-> FALSE]
/\ Fluent18_0 = [ x0 \in Core |-> FALSE]
/\ Fluent69_14 = [ x0 \in Address |-> FALSE]
/\ Fluent16_9 = [ x0 \in Address |-> FALSE]
/\ Fluent63_14 = [ x0 \in Address |-> FALSE]
/\ Fluent15_9 = [ x0 \in Address |-> FALSE]

issue_proc_read_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,invalid>>
/\ Fluent48_1' = [Fluent48_1 EXCEPT ![a] = TRUE]
/\ Fluent95_18' = [Fluent95_18 EXCEPT ![a] = TRUE]
/\ Fluent25_0' = [x0 \in Core |-> TRUE]
/\ Fluent46_5' = [x0 \in Core |-> [x1 \in Value |-> TRUE]]
/\ Fluent47_5' = [Fluent47_5 EXCEPT ![c] = TRUE]
/\ Fluent92_4' = [Fluent92_4 EXCEPT ![a] = TRUE]
/\ Fluent69_14' = [Fluent69_14 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent26_0, Fluent49_1, Fluent68_14, Fluent64_14, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, Fluent6_17, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent16_9, Fluent63_14, Fluent15_9>>
/\ CandSep'

do_bus_read_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,invalid>>
/\ Fluent105_10' = [x0 \in Value |-> FALSE]
/\ Fluent49_1' = [Fluent49_1 EXCEPT ![a] = TRUE]
/\ Fluent25_0' = [x0 \in Core |-> FALSE]
/\ Fluent47_5' = [Fluent47_5 EXCEPT ![c] = FALSE]
/\ Fluent19_0' = [Fluent19_0 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent80_2, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent68_14, Fluent46_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9>>
/\ CandSep'

do_bus_read_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ cache[c][a] = v
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ (modified[c][a] => memory' = [memory EXCEPT![a] = v])
/\ (~(modified[c][a]) => memory' = memory)
/\ UNCHANGED <<cache,invalid>>
/\ Fluent80_2' = [Fluent80_2 EXCEPT ![v] = TRUE]
/\ Fluent68_14' = [Fluent68_14 EXCEPT ![a] = TRUE]
/\ Fluent6_17' = [x0 \in Core |-> TRUE]
/\ Fluent39_0' = [x0 \in Core |-> TRUE]
/\ UNCHANGED<<Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, Fluent92_4, Fluent38_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9>>
/\ CandSep'

complete_proc_read_invalid_shared(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,modified>>
/\ Fluent81_2' = [Fluent81_2 EXCEPT ![v] = TRUE]
/\ Fluent5_17' = [Fluent5_17 EXCEPT ![c] = TRUE]
/\ Fluent25_0' = [x0 \in Core |-> FALSE]
/\ Fluent93_4' = [Fluent93_4 EXCEPT ![a] = TRUE]
/\ Fluent63_14' = [Fluent63_14 EXCEPT ![a] = TRUE]
/\ Fluent15_9' = [Fluent15_9 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent77_16, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent73_0, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9>>
/\ CandSep'

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ invalid[c][a]
/\ memory[a] = v
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,modified>>
/\ Fluent105_10' = [Fluent105_10 EXCEPT ![v] = TRUE]
/\ Fluent76_16' = [Fluent76_16 EXCEPT ![c] = TRUE]
/\ Fluent106_10' = [Fluent106_10 EXCEPT ![v] = Fluent105_10[v]]
/\ Fluent94_18' = [Fluent94_18 EXCEPT ![a] = TRUE]
/\ Fluent19_0' = [Fluent19_0 EXCEPT ![c] = TRUE]
/\ Fluent18_0' = [x0 \in Core |-> TRUE]
/\ Fluent69_14' = [Fluent69_14 EXCEPT ![a] = Fluent68_14[a]]
/\ UNCHANGED<<Fluent80_2, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent73_0, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent16_9, Fluent63_14, Fluent15_9>>
/\ CandSep'

issue_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,invalid>>
/\ Fluent26_0' = [Fluent26_0 EXCEPT ![c] = Fluent25_0[c]]
/\ Fluent73_0' = [Fluent73_0 EXCEPT ![c] = TRUE]
/\ Fluent39_0' = [Fluent39_0 EXCEPT ![c] = TRUE]
/\ Fluent15_9' = [Fluent15_9 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14>>
/\ CandSep'

do_bus_read_for_ownership_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,invalid>>
/\ Fluent73_0' = [Fluent73_0 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9>>
/\ CandSep'

do_bus_read_for_ownership_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ cache[c][a] = v
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ (modified[c][a] => memory' = [memory EXCEPT![a] = v])
/\ (~(modified[c][a]) => memory' = memory)
/\ UNCHANGED <<cache>>
/\ Fluent80_2' = [Fluent80_2 EXCEPT ![v] = TRUE]
/\ Fluent73_0' = [Fluent73_0 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9>>
/\ CandSep'

complete_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory>>
/\ Fluent74_0' = [x0 \in Core |-> Fluent73_0[c]]
/\ Fluent38_0' = [Fluent38_0 EXCEPT ![c] = TRUE]
/\ Fluent16_9' = [Fluent16_9 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent6_17, Fluent92_4, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent63_14, Fluent15_9>>
/\ CandSep'

proc_write_exclusive(c,a,v) ==
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,invalid>>
/\ Fluent77_16' = [Fluent77_16 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9>>
/\ CandSep'

do_bus_upgrade(c,a) ==
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<memory,cache,modified>>
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9>>
/\ CandSep'

complete_proc_write_shared(c,a,v) ==
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,invalid>>
/\ Fluent64_14' = [Fluent64_14 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9>>
/\ CandSep'

evict_modified(c,a) ==
/\ modified[c][a]
/\ memory' = [memory EXCEPT![a] = cache[c][a]]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<cache>>
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9>>
/\ CandSep'

evict_exclusive_or_shared(c,a) ==
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<memory,cache,modified>>
/\ UNCHANGED<<Fluent80_2, Fluent105_10, Fluent77_16, Fluent81_2, Fluent5_17, Fluent48_1, Fluent95_18, Fluent26_0, Fluent49_1, Fluent68_14, Fluent25_0, Fluent46_5, Fluent47_5, Fluent64_14, Fluent76_16, Fluent106_10, Fluent73_0, Fluent93_4, Fluent74_0, Fluent6_17, Fluent92_4, Fluent38_0, Fluent39_0, Fluent94_18, Fluent19_0, Fluent18_0, Fluent69_14, Fluent16_9, Fluent63_14, Fluent15_9>>
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
\/ do_bus_upgrade(c,a)
\/ complete_proc_write_shared(c,a,v)
\/ evict_modified(c,a)
\/ evict_exclusive_or_shared(c,a)

Spec == (Init /\ [][Next]_vars)

Safety == (\A C \in Core : (\A A \in Address : ((~(invalid[C][A]) /\ ~(modified[C][A])) => cache[C][A] = memory[A])))
=============================================================================
