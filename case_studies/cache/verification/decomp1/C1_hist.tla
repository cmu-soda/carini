--------------------------- MODULE C1_hist ---------------------------


CONSTANTS Address, Core, Value

VARIABLES Fluent115_1, Fluent114_1, Fluent80_0, Fluent132_9, memory, Fluent133_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent5_15, Fluent35_15, Fluent71_14, Fluent127_22, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, modified, Fluent29_4, Fluent138_6, Fluent139_6, Fluent64_18, cache, Fluent123_14, Fluent99_0, Fluent128_22, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent34_15, Fluent135_13, Fluent67_15, invalid, Fluent65_18

vars == <<Fluent115_1, Fluent114_1, Fluent80_0, Fluent132_9, memory, Fluent133_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent5_15, Fluent35_15, Fluent71_14, Fluent127_22, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, modified, Fluent29_4, Fluent138_6, Fluent139_6, Fluent64_18, cache, Fluent123_14, Fluent99_0, Fluent128_22, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent34_15, Fluent135_13, Fluent67_15, invalid, Fluent65_18>>

CandSep ==
/\ \A var0 \in Core : \A var1 \in Address : (Fluent138_6[var1]) => (Fluent139_6[var1][var0])
/\ \A var0 \in Core : (Fluent99_0[var0]) => (Fluent100_0[var0])
/\ \A var0 \in Value : (Fluent89_5[var0]) => (Fluent90_5[var0])
/\ \A var0 \in Address : (Fluent114_1[var0]) => (Fluent115_1[var0])
/\ \A var0 \in Address : (Fluent127_22[var0]) => (~(Fluent128_22[var0]))
/\ \A var0 \in Core : (Fluent21_6[var0]) => (Fluent20_6[var0])
/\ \A var0 \in Address : (Fluent96_3[var0]) => (Fluent95_3[var0])
/\ \A var0 \in Core : (Fluent34_15[var0]) => (Fluent35_15[var0])
/\ \A var0 \in Address : (Fluent132_9[var0]) => (Fluent133_9[var0])
/\ \A var0 \in Address : (Fluent118_1[var0]) => (Fluent117_1[var0])
/\ \A var0 \in Address : (Fluent83_3[var0]) => (~(Fluent82_3[var0]))
/\ \A var0 \in Core : (Fluent5_15[var0]) => (Fluent6_15[var0])
/\ \A var0 \in Address : (Fluent71_14[var0]) => (Fluent70_14[var0])
/\ \A var0 \in Core : (Fluent23_0[var0]) => (Fluent24_0[var0])
/\ \A var0 \in Address : (Fluent65_18[var0]) => (Fluent64_18[var0])
/\ \A var0 \in Address : (Fluent136_13[var0]) => (~(Fluent135_13[var0]))
/\ \A var0 \in Core : (Fluent67_15[var0]) => (Fluent68_15[var0])
/\ \A var0 \in Core : (Fluent79_0[var0]) => (Fluent80_0[var0])
/\ \A var0 \in Value : \E var1 \in Core : (Fluent48_2[var1][var0]) => (Fluent47_2[var1])
/\ \A var0 \in Address : (Fluent29_4[var0]) => (Fluent30_4[var0])
/\ \A var0 \in Address : (Fluent123_14[var0]) => (Fluent122_14[var0])

Init ==
/\ (memory \in [Address -> Value])
/\ (cache \in [Core -> [Address -> Value]])
/\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
/\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]
/\ Fluent115_1 = [ x0 \in Address |-> FALSE]
/\ Fluent114_1 = [ x0 \in Address |-> FALSE]
/\ Fluent80_0 = [ x0 \in Core |-> FALSE]
/\ Fluent132_9 = [ x0 \in Address |-> FALSE]
/\ Fluent133_9 = [ x0 \in Address |-> FALSE]
/\ Fluent122_14 = [ x0 \in Address |-> FALSE]
/\ Fluent118_1 = [ x0 \in Address |-> FALSE]
/\ Fluent117_1 = [ x0 \in Address |-> FALSE]
/\ Fluent5_15 = [ x0 \in Core |-> FALSE]
/\ Fluent35_15 = [ x0 \in Core |-> FALSE]
/\ Fluent71_14 = [ x0 \in Address |-> FALSE]
/\ Fluent127_22 = [ x0 \in Address |-> FALSE]
/\ Fluent82_3 = [ x0 \in Address |-> FALSE]
/\ Fluent24_0 = [ x0 \in Core |-> FALSE]
/\ Fluent83_3 = [ x0 \in Address |-> FALSE]
/\ Fluent23_0 = [ x0 \in Core |-> FALSE]
/\ Fluent20_6 = [ x0 \in Core |-> FALSE]
/\ Fluent136_13 = [ x0 \in Address |-> FALSE]
/\ Fluent68_15 = [ x0 \in Core |-> FALSE]
/\ Fluent47_2 = [ x0 \in Core |-> FALSE]
/\ Fluent48_2 = [ x0 \in Core |-> [ x1 \in Value |-> FALSE]]
/\ Fluent70_14 = [ x0 \in Address |-> FALSE]
/\ Fluent21_6 = [ x0 \in Core |-> FALSE]
/\ Fluent89_5 = [ x0 \in Value |-> FALSE]
/\ Fluent29_4 = [ x0 \in Address |-> FALSE]
/\ Fluent138_6 = [ x0 \in Address |-> FALSE]
/\ Fluent139_6 = [ x0 \in Address |-> [ x1 \in Core |-> FALSE]]
/\ Fluent64_18 = [ x0 \in Address |-> FALSE]
/\ Fluent123_14 = [ x0 \in Address |-> FALSE]
/\ Fluent99_0 = [ x0 \in Core |-> FALSE]
/\ Fluent128_22 = [ x0 \in Address |-> FALSE]
/\ Fluent96_3 = [ x0 \in Address |-> FALSE]
/\ Fluent95_3 = [ x0 \in Address |-> FALSE]
/\ Fluent79_0 = [ x0 \in Core |-> FALSE]
/\ Fluent100_0 = [ x0 \in Core |-> FALSE]
/\ Fluent90_5 = [ x0 \in Value |-> FALSE]
/\ Fluent30_4 = [ x0 \in Address |-> FALSE]
/\ Fluent6_15 = [ x0 \in Core |-> FALSE]
/\ Fluent34_15 = [ x0 \in Core |-> FALSE]
/\ Fluent135_13 = [ x0 \in Address |-> FALSE]
/\ Fluent67_15 = [ x0 \in Core |-> FALSE]
/\ Fluent65_18 = [ x0 \in Address |-> FALSE]

issue_proc_read_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,invalid>>
/\ Fluent115_1' = [Fluent115_1 EXCEPT ![a] = TRUE]
/\ Fluent122_14' = [Fluent122_14 EXCEPT ![a] = TRUE]
/\ Fluent35_15' = [Fluent35_15 EXCEPT ![c] = FALSE]
/\ Fluent82_3' = [Fluent82_3 EXCEPT ![a] = Fluent83_3[a]]
/\ Fluent83_3' = [Fluent83_3 EXCEPT ![a] = TRUE]
/\ Fluent136_13' = [Fluent136_13 EXCEPT ![a] = FALSE]
/\ Fluent47_2' = [Fluent47_2 EXCEPT ![c] = TRUE]
/\ Fluent48_2' = [x0 \in Core |-> [x1 \in Value |-> TRUE]]
/\ Fluent29_4' = [Fluent29_4 EXCEPT ![a] = TRUE]
/\ Fluent139_6' = [Fluent139_6 EXCEPT ![a][c] = TRUE]
/\ Fluent64_18' = [Fluent64_18 EXCEPT ![a] = TRUE]
/\ Fluent128_22' = [Fluent128_22 EXCEPT ![a] = TRUE]
/\ Fluent95_3' = [Fluent95_3 EXCEPT ![a] = TRUE]
/\ Fluent30_4' = [Fluent30_4 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent114_1, Fluent80_0, Fluent132_9, Fluent133_9, Fluent118_1, Fluent117_1, Fluent5_15, Fluent71_14, Fluent127_22, Fluent24_0, Fluent23_0, Fluent20_6, Fluent68_15, Fluent70_14, Fluent21_6, Fluent89_5, Fluent138_6, Fluent123_14, Fluent99_0, Fluent96_3, Fluent79_0, Fluent100_0, Fluent90_5, Fluent6_15, Fluent34_15, Fluent135_13, Fluent67_15, Fluent65_18>>
/\ CandSep'

do_bus_read_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,invalid>>
/\ Fluent118_1' = [Fluent118_1 EXCEPT ![a] = FALSE]
/\ Fluent127_22' = [Fluent127_22 EXCEPT ![a] = FALSE]
/\ Fluent24_0' = [Fluent24_0 EXCEPT ![c] = TRUE]
/\ Fluent47_2' = [Fluent47_2 EXCEPT ![c] = FALSE]
/\ Fluent29_4' = [Fluent29_4 EXCEPT ![a] = FALSE]
/\ Fluent139_6' = [Fluent139_6 EXCEPT ![a][c] = TRUE]
/\ Fluent128_22' = [Fluent128_22 EXCEPT ![a] = FALSE]
/\ Fluent65_18' = [Fluent65_18 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent115_1, Fluent114_1, Fluent80_0, Fluent132_9, Fluent133_9, Fluent122_14, Fluent117_1, Fluent5_15, Fluent35_15, Fluent71_14, Fluent82_3, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent138_6, Fluent64_18, Fluent123_14, Fluent99_0, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent34_15, Fluent135_13, Fluent67_15>>
/\ CandSep'

do_bus_read_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ cache[c][a] = v
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ (modified[c][a] => memory' = [memory EXCEPT![a] = v])
/\ (~(modified[c][a]) => memory' = memory)
/\ UNCHANGED <<cache,invalid>>
/\ Fluent114_1' = [Fluent114_1 EXCEPT ![a] = TRUE]
/\ Fluent127_22' = [Fluent127_22 EXCEPT ![a] = Fluent128_22[a]]
/\ Fluent20_6' = [Fluent20_6 EXCEPT ![c] = TRUE]
/\ Fluent29_4' = [Fluent29_4 EXCEPT ![a] = FALSE]
/\ Fluent123_14' = [Fluent123_14 EXCEPT ![a] = TRUE]
/\ Fluent128_22' = [Fluent128_22 EXCEPT ![a] = FALSE]
/\ Fluent90_5' = [Fluent90_5 EXCEPT ![v] = TRUE]
/\ Fluent6_15' = [x0 \in Core |-> TRUE]
/\ UNCHANGED<<Fluent115_1, Fluent80_0, Fluent132_9, Fluent133_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent5_15, Fluent35_15, Fluent71_14, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent138_6, Fluent139_6, Fluent64_18, Fluent99_0, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent30_4, Fluent34_15, Fluent135_13, Fluent67_15, Fluent65_18>>
/\ CandSep'

complete_proc_read_invalid_shared(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,modified>>
/\ Fluent114_1' = [Fluent114_1 EXCEPT ![a] = FALSE]
/\ Fluent5_15' = [Fluent5_15 EXCEPT ![c] = TRUE]
/\ Fluent83_3' = [Fluent83_3 EXCEPT ![a] = FALSE]
/\ Fluent20_6' = [Fluent20_6 EXCEPT ![c] = TRUE]
/\ Fluent70_14' = [Fluent70_14 EXCEPT ![a] = TRUE]
/\ Fluent89_5' = [Fluent89_5 EXCEPT ![v] = TRUE]
/\ Fluent123_14' = [Fluent123_14 EXCEPT ![a] = FALSE]
/\ Fluent128_22' = [Fluent128_22 EXCEPT ![a] = TRUE]
/\ Fluent96_3' = [Fluent96_3 EXCEPT ![a] = TRUE]
/\ Fluent65_18' = [Fluent65_18 EXCEPT ![a] = FALSE]
/\ UNCHANGED<<Fluent115_1, Fluent80_0, Fluent132_9, Fluent133_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent35_15, Fluent71_14, Fluent127_22, Fluent82_3, Fluent24_0, Fluent23_0, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent21_6, Fluent29_4, Fluent138_6, Fluent139_6, Fluent64_18, Fluent99_0, Fluent95_3, Fluent79_0, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent34_15, Fluent135_13, Fluent67_15>>
/\ CandSep'

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ invalid[c][a]
/\ memory[a] = v
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,modified>>
/\ Fluent115_1' = [Fluent115_1 EXCEPT ![a] = FALSE]
/\ Fluent117_1' = [Fluent117_1 EXCEPT ![a] = FALSE]
/\ Fluent83_3' = [Fluent83_3 EXCEPT ![a] = FALSE]
/\ Fluent23_0' = [[x0 \in Core |-> TRUE] EXCEPT ![c] = FALSE]
/\ Fluent136_13' = [Fluent136_13 EXCEPT ![a] = TRUE]
/\ Fluent68_15' = [Fluent68_15 EXCEPT ![c] = TRUE]
/\ Fluent138_6' = [Fluent138_6 EXCEPT ![a] = TRUE]
/\ Fluent135_13' = [Fluent135_13 EXCEPT ![a] = Fluent136_13[a]]
/\ Fluent65_18' = [Fluent65_18 EXCEPT ![a] = FALSE]
/\ UNCHANGED<<Fluent114_1, Fluent80_0, Fluent132_9, Fluent133_9, Fluent122_14, Fluent118_1, Fluent5_15, Fluent35_15, Fluent71_14, Fluent127_22, Fluent82_3, Fluent24_0, Fluent20_6, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent29_4, Fluent139_6, Fluent64_18, Fluent123_14, Fluent99_0, Fluent128_22, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent34_15, Fluent67_15>>
/\ CandSep'

issue_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,invalid>>
/\ Fluent80_0' = [Fluent80_0 EXCEPT ![c] = TRUE]
/\ Fluent133_9' = [Fluent133_9 EXCEPT ![a] = TRUE]
/\ Fluent35_15' = [Fluent35_15 EXCEPT ![c] = TRUE]
/\ Fluent20_6' = [Fluent20_6 EXCEPT ![c] = TRUE]
/\ Fluent64_18' = [x0 \in Address |-> FALSE]
/\ Fluent99_0' = [Fluent99_0 EXCEPT ![c] = TRUE]
/\ Fluent100_0' = [[x0 \in Core |-> FALSE] EXCEPT ![c] = TRUE]
/\ Fluent30_4' = [x0 \in Address |-> FALSE]
/\ Fluent34_15' = [Fluent34_15 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent115_1, Fluent114_1, Fluent132_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent5_15, Fluent71_14, Fluent127_22, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent29_4, Fluent138_6, Fluent139_6, Fluent123_14, Fluent128_22, Fluent96_3, Fluent95_3, Fluent79_0, Fluent90_5, Fluent6_15, Fluent135_13, Fluent67_15, Fluent65_18>>
/\ CandSep'

do_bus_read_for_ownership_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,invalid>>
/\ Fluent80_0' = [Fluent80_0 EXCEPT ![c] = TRUE]
/\ Fluent132_9' = [Fluent132_9 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent115_1, Fluent114_1, Fluent133_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent5_15, Fluent35_15, Fluent71_14, Fluent127_22, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent29_4, Fluent138_6, Fluent139_6, Fluent64_18, Fluent123_14, Fluent99_0, Fluent128_22, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent34_15, Fluent135_13, Fluent67_15, Fluent65_18>>
/\ CandSep'

do_bus_read_for_ownership_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ cache[c][a] = v
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ (modified[c][a] => memory' = [memory EXCEPT![a] = v])
/\ (~(modified[c][a]) => memory' = memory)
/\ UNCHANGED <<cache>>
/\ Fluent80_0' = [Fluent80_0 EXCEPT ![c] = TRUE]
/\ Fluent90_5' = [Fluent90_5 EXCEPT ![v] = TRUE]
/\ UNCHANGED<<Fluent115_1, Fluent114_1, Fluent132_9, Fluent133_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent5_15, Fluent35_15, Fluent71_14, Fluent127_22, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent29_4, Fluent138_6, Fluent139_6, Fluent64_18, Fluent123_14, Fluent99_0, Fluent128_22, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent30_4, Fluent6_15, Fluent34_15, Fluent135_13, Fluent67_15, Fluent65_18>>
/\ CandSep'

complete_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory>>
/\ Fluent21_6' = [Fluent21_6 EXCEPT ![c] = TRUE]
/\ Fluent99_0' = [Fluent99_0 EXCEPT ![c] = FALSE]
/\ Fluent79_0' = [x0 \in Core |-> Fluent80_0[c]]
/\ Fluent34_15' = [Fluent34_15 EXCEPT ![c] = FALSE]
/\ UNCHANGED<<Fluent115_1, Fluent114_1, Fluent80_0, Fluent132_9, Fluent133_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent5_15, Fluent35_15, Fluent71_14, Fluent127_22, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent89_5, Fluent29_4, Fluent138_6, Fluent139_6, Fluent64_18, Fluent123_14, Fluent128_22, Fluent96_3, Fluent95_3, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent135_13, Fluent67_15, Fluent65_18>>
/\ CandSep'

proc_write_exclusive(c,a,v) ==
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,invalid>>
/\ Fluent122_14' = [Fluent122_14 EXCEPT ![a] = FALSE]
/\ Fluent118_1' = [Fluent118_1 EXCEPT ![a] = TRUE]
/\ Fluent117_1' = [Fluent117_1 EXCEPT ![a] = TRUE]
/\ Fluent67_15' = [Fluent67_15 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent115_1, Fluent114_1, Fluent80_0, Fluent132_9, Fluent133_9, Fluent5_15, Fluent35_15, Fluent71_14, Fluent127_22, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent29_4, Fluent138_6, Fluent139_6, Fluent64_18, Fluent123_14, Fluent99_0, Fluent128_22, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent34_15, Fluent135_13, Fluent65_18>>
/\ CandSep'

do_bus_upgrade(c,a) ==
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<memory,cache,modified>>
/\ UNCHANGED<<Fluent115_1, Fluent114_1, Fluent80_0, Fluent132_9, Fluent133_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent5_15, Fluent35_15, Fluent71_14, Fluent127_22, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent29_4, Fluent138_6, Fluent139_6, Fluent64_18, Fluent123_14, Fluent99_0, Fluent128_22, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent34_15, Fluent135_13, Fluent67_15, Fluent65_18>>
/\ CandSep'

complete_proc_write_shared(c,a,v) ==
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,invalid>>
/\ Fluent71_14' = [Fluent71_14 EXCEPT ![a] = TRUE]
/\ Fluent99_0' = [Fluent99_0 EXCEPT ![c] = FALSE]
/\ Fluent34_15' = [Fluent34_15 EXCEPT ![c] = FALSE]
/\ UNCHANGED<<Fluent115_1, Fluent114_1, Fluent80_0, Fluent132_9, Fluent133_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent5_15, Fluent35_15, Fluent127_22, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent29_4, Fluent138_6, Fluent139_6, Fluent64_18, Fluent123_14, Fluent128_22, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent135_13, Fluent67_15, Fluent65_18>>
/\ CandSep'

evict_modified(c,a) ==
/\ modified[c][a]
/\ memory' = [memory EXCEPT![a] = cache[c][a]]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<cache>>
/\ UNCHANGED<<Fluent115_1, Fluent114_1, Fluent80_0, Fluent132_9, Fluent133_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent5_15, Fluent35_15, Fluent71_14, Fluent127_22, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent29_4, Fluent138_6, Fluent139_6, Fluent64_18, Fluent123_14, Fluent99_0, Fluent128_22, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent34_15, Fluent135_13, Fluent67_15, Fluent65_18>>
/\ CandSep'

evict_exclusive_or_shared(c,a) ==
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<memory,cache,modified>>
/\ UNCHANGED<<Fluent115_1, Fluent114_1, Fluent80_0, Fluent132_9, Fluent133_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent5_15, Fluent35_15, Fluent71_14, Fluent127_22, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent29_4, Fluent138_6, Fluent139_6, Fluent64_18, Fluent123_14, Fluent99_0, Fluent128_22, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent34_15, Fluent135_13, Fluent67_15, Fluent65_18>>
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
