--------------------------- MODULE T1_hist ---------------------------


CONSTANTS Address, Core, Value

VARIABLES Fluent115_1, Fluent80_0, Fluent132_9, Fluent122_14, Fluent117_1, bus_transfer, Fluent35_15, Fluent127_22, Fluent82_3, Fluent23_0, Fluent136_13, Fluent68_15, Fluent48_2, Fluent70_14, proc_write, Fluent21_6, bus_read_for_ownership, exclusive, Fluent29_4, Fluent138_6, Fluent64_18, Fluent123_14, Fluent128_22, Fluent96_3, Fluent79_0, Fluent90_5, Fluent67_15, proc_read, shared, Fluent114_1, Fluent133_9, Fluent118_1, Fluent5_15, Fluent71_14, Fluent24_0, Fluent83_3, Fluent20_6, Fluent47_2, Fluent89_5, Fluent139_6, Fluent99_0, Fluent95_3, bus_read, Fluent100_0, Fluent30_4, Fluent6_15, bus_in_use, Fluent34_15, Fluent135_13, bus_upgrade, Fluent65_18

vars == <<Fluent115_1, Fluent80_0, Fluent132_9, Fluent122_14, Fluent117_1, bus_transfer, Fluent35_15, Fluent127_22, Fluent82_3, Fluent23_0, Fluent136_13, Fluent68_15, Fluent48_2, Fluent70_14, proc_write, Fluent21_6, bus_read_for_ownership, exclusive, Fluent29_4, Fluent138_6, Fluent64_18, Fluent123_14, Fluent128_22, Fluent96_3, Fluent79_0, Fluent90_5, Fluent67_15, proc_read, shared, Fluent114_1, Fluent133_9, Fluent118_1, Fluent5_15, Fluent71_14, Fluent24_0, Fluent83_3, Fluent20_6, Fluent47_2, Fluent89_5, Fluent139_6, Fluent99_0, Fluent95_3, bus_read, Fluent100_0, Fluent30_4, Fluent6_15, bus_in_use, Fluent34_15, Fluent135_13, bus_upgrade, Fluent65_18>>

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
/\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
/\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
/\ proc_read = [c \in Core |-> [a \in Address |-> FALSE]]
/\ proc_write = [c \in Core |-> [a \in Address |-> [v \in Value |-> FALSE]]]
/\ bus_in_use = FALSE
/\ bus_read = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_read_for_ownership = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_upgrade = [c \in Core |-> [a \in Address |-> FALSE]]
/\ bus_transfer = [v \in Value |-> FALSE]
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
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_read' = [proc_read EXCEPT![c][a] = TRUE]
/\ bus_read' = [C \in Core |-> [A \in Address |-> (bus_read[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<exclusive,shared,proc_write,bus_read_for_ownership,bus_upgrade,bus_transfer>>
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

do_bus_read_invalid(c,a) ==
/\ bus_read[c][a]
/\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<exclusive,shared,proc_read,proc_write,bus_in_use,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ Fluent118_1' = [Fluent118_1 EXCEPT ![a] = FALSE]
/\ Fluent127_22' = [Fluent127_22 EXCEPT ![a] = FALSE]
/\ Fluent24_0' = [Fluent24_0 EXCEPT ![c] = TRUE]
/\ Fluent47_2' = [Fluent47_2 EXCEPT ![c] = FALSE]
/\ Fluent29_4' = [Fluent29_4 EXCEPT ![a] = FALSE]
/\ Fluent139_6' = [Fluent139_6 EXCEPT ![a][c] = TRUE]
/\ Fluent128_22' = [Fluent128_22 EXCEPT ![a] = FALSE]
/\ Fluent65_18' = [Fluent65_18 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent115_1, Fluent114_1, Fluent80_0, Fluent132_9, Fluent133_9, Fluent122_14, Fluent117_1, Fluent5_15, Fluent35_15, Fluent71_14, Fluent82_3, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent138_6, Fluent64_18, Fluent123_14, Fluent99_0, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent34_15, Fluent135_13, Fluent67_15>>

do_bus_read_valid(c,a,v) ==
/\ bus_read[c][a]
/\ bus_read' = [bus_read EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read_for_ownership,bus_upgrade>>
/\ Fluent114_1' = [Fluent114_1 EXCEPT ![a] = TRUE]
/\ Fluent127_22' = [Fluent127_22 EXCEPT ![a] = Fluent128_22[a]]
/\ Fluent20_6' = [Fluent20_6 EXCEPT ![c] = TRUE]
/\ Fluent29_4' = [Fluent29_4 EXCEPT ![a] = FALSE]
/\ Fluent123_14' = [Fluent123_14 EXCEPT ![a] = TRUE]
/\ Fluent128_22' = [Fluent128_22 EXCEPT ![a] = FALSE]
/\ Fluent90_5' = [Fluent90_5 EXCEPT ![v] = TRUE]
/\ Fluent6_15' = [x0 \in Core |-> TRUE]
/\ UNCHANGED<<Fluent115_1, Fluent80_0, Fluent132_9, Fluent133_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent5_15, Fluent35_15, Fluent71_14, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent138_6, Fluent139_6, Fluent64_18, Fluent99_0, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent30_4, Fluent34_15, Fluent135_13, Fluent67_15, Fluent65_18>>

complete_proc_read_invalid_shared(c,a,v) ==
/\ proc_read[c][a]
/\ bus_transfer[v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_read[C][A])))
/\ bus_transfer' = [V \in Value |-> FALSE]
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ bus_in_use' = FALSE
/\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<exclusive,proc_write,bus_read,bus_read_for_ownership,bus_upgrade>>
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

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ proc_read[c][a]
/\ (\A V \in Value : ~(bus_transfer[V]))
/\ (\A C \in Core : (\A A \in Address : ~(bus_read[C][A])))
/\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
/\ bus_in_use' = FALSE
/\ proc_read' = [proc_read EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<shared,proc_write,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
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

issue_proc_write_invalid(c,a,v) ==
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
/\ bus_read_for_ownership' = [C \in Core |-> [A \in Address |-> (bus_read_for_ownership[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<exclusive,shared,proc_read,bus_read,bus_upgrade,bus_transfer>>
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

do_bus_read_for_ownership_invalid(c,a) ==
/\ bus_read_for_ownership[c][a]
/\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<exclusive,shared,proc_read,proc_write,bus_in_use,bus_read,bus_upgrade,bus_transfer>>
/\ Fluent80_0' = [Fluent80_0 EXCEPT ![c] = TRUE]
/\ Fluent132_9' = [Fluent132_9 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent115_1, Fluent114_1, Fluent133_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent5_15, Fluent35_15, Fluent71_14, Fluent127_22, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent29_4, Fluent138_6, Fluent139_6, Fluent64_18, Fluent123_14, Fluent99_0, Fluent128_22, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent34_15, Fluent135_13, Fluent67_15, Fluent65_18>>

do_bus_read_for_ownership_valid(c,a,v) ==
/\ bus_read_for_ownership[c][a]
/\ bus_read_for_ownership' = [bus_read_for_ownership EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ bus_transfer' = [bus_transfer EXCEPT![v] = TRUE]
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read,bus_upgrade>>
/\ Fluent80_0' = [Fluent80_0 EXCEPT ![c] = TRUE]
/\ Fluent90_5' = [Fluent90_5 EXCEPT ![v] = TRUE]
/\ UNCHANGED<<Fluent115_1, Fluent114_1, Fluent132_9, Fluent133_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent5_15, Fluent35_15, Fluent71_14, Fluent127_22, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent29_4, Fluent138_6, Fluent139_6, Fluent64_18, Fluent123_14, Fluent99_0, Fluent128_22, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent30_4, Fluent6_15, Fluent34_15, Fluent135_13, Fluent67_15, Fluent65_18>>

complete_proc_write_invalid(c,a,v) ==
/\ proc_write[c][a][v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_read_for_ownership[C][A])))
/\ bus_transfer' = [V \in Value |-> FALSE]
/\ bus_in_use' = FALSE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
/\ UNCHANGED <<exclusive,shared,proc_read,bus_read,bus_read_for_ownership,bus_upgrade>>
/\ Fluent21_6' = [Fluent21_6 EXCEPT ![c] = TRUE]
/\ Fluent99_0' = [Fluent99_0 EXCEPT ![c] = FALSE]
/\ Fluent79_0' = [x0 \in Core |-> Fluent80_0[c]]
/\ Fluent34_15' = [Fluent34_15 EXCEPT ![c] = FALSE]
/\ UNCHANGED<<Fluent115_1, Fluent114_1, Fluent80_0, Fluent132_9, Fluent133_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent5_15, Fluent35_15, Fluent71_14, Fluent127_22, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent89_5, Fluent29_4, Fluent138_6, Fluent139_6, Fluent64_18, Fluent123_14, Fluent128_22, Fluent96_3, Fluent95_3, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent135_13, Fluent67_15, Fluent65_18>>

proc_write_exclusive(c,a,v) ==
/\ exclusive[c][a]
/\ ~(bus_in_use)
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<shared,proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ Fluent122_14' = [Fluent122_14 EXCEPT ![a] = FALSE]
/\ Fluent118_1' = [Fluent118_1 EXCEPT ![a] = TRUE]
/\ Fluent117_1' = [Fluent117_1 EXCEPT ![a] = TRUE]
/\ Fluent67_15' = [Fluent67_15 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent115_1, Fluent114_1, Fluent80_0, Fluent132_9, Fluent133_9, Fluent5_15, Fluent35_15, Fluent71_14, Fluent127_22, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent29_4, Fluent138_6, Fluent139_6, Fluent64_18, Fluent123_14, Fluent99_0, Fluent128_22, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent34_15, Fluent135_13, Fluent65_18>>

issue_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ ~(bus_in_use)
/\ bus_in_use' = TRUE
/\ proc_write' = [proc_write EXCEPT![c][a][v] = TRUE]
/\ bus_upgrade' = [C \in Core |-> [A \in Address |-> (bus_upgrade[C][A] \/ (C /= c /\ A = a))]]
/\ UNCHANGED <<exclusive,shared,proc_read,bus_read,bus_read_for_ownership,bus_transfer>>
/\ UNCHANGED<<Fluent115_1, Fluent114_1, Fluent80_0, Fluent132_9, Fluent133_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent5_15, Fluent35_15, Fluent71_14, Fluent127_22, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent29_4, Fluent138_6, Fluent139_6, Fluent64_18, Fluent123_14, Fluent99_0, Fluent128_22, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent34_15, Fluent135_13, Fluent67_15, Fluent65_18>>

do_bus_upgrade(c,a) ==
/\ bus_upgrade[c][a]
/\ bus_upgrade' = [bus_upgrade EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<exclusive,proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_transfer>>
/\ UNCHANGED<<Fluent115_1, Fluent114_1, Fluent80_0, Fluent132_9, Fluent133_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent5_15, Fluent35_15, Fluent71_14, Fluent127_22, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent29_4, Fluent138_6, Fluent139_6, Fluent64_18, Fluent123_14, Fluent99_0, Fluent128_22, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent34_15, Fluent135_13, Fluent67_15, Fluent65_18>>

complete_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ proc_write[c][a][v]
/\ (\A C \in Core : (\A A \in Address : ~(bus_upgrade[C][A])))
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ proc_write' = [proc_write EXCEPT![c][a][v] = FALSE]
/\ bus_in_use' = FALSE
/\ UNCHANGED <<exclusive,proc_read,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ Fluent71_14' = [Fluent71_14 EXCEPT ![a] = TRUE]
/\ Fluent99_0' = [Fluent99_0 EXCEPT ![c] = FALSE]
/\ Fluent34_15' = [Fluent34_15 EXCEPT ![c] = FALSE]
/\ UNCHANGED<<Fluent115_1, Fluent114_1, Fluent80_0, Fluent132_9, Fluent133_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent5_15, Fluent35_15, Fluent127_22, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent29_4, Fluent138_6, Fluent139_6, Fluent64_18, Fluent123_14, Fluent128_22, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent135_13, Fluent67_15, Fluent65_18>>

evict_modified(c,a) ==
/\ ~(bus_in_use)
/\ UNCHANGED <<exclusive,shared,proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent115_1, Fluent114_1, Fluent80_0, Fluent132_9, Fluent133_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent5_15, Fluent35_15, Fluent71_14, Fluent127_22, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent29_4, Fluent138_6, Fluent139_6, Fluent64_18, Fluent123_14, Fluent99_0, Fluent128_22, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent34_15, Fluent135_13, Fluent67_15, Fluent65_18>>

evict_exclusive_or_shared(c,a) ==
/\ ~(bus_in_use)
/\ (exclusive[c][a] \/ shared[c][a])
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<proc_read,proc_write,bus_in_use,bus_read,bus_read_for_ownership,bus_upgrade,bus_transfer>>
/\ UNCHANGED<<Fluent115_1, Fluent114_1, Fluent80_0, Fluent132_9, Fluent133_9, Fluent122_14, Fluent118_1, Fluent117_1, Fluent5_15, Fluent35_15, Fluent71_14, Fluent127_22, Fluent82_3, Fluent24_0, Fluent83_3, Fluent23_0, Fluent20_6, Fluent136_13, Fluent68_15, Fluent47_2, Fluent48_2, Fluent70_14, Fluent21_6, Fluent89_5, Fluent29_4, Fluent138_6, Fluent139_6, Fluent64_18, Fluent123_14, Fluent99_0, Fluent128_22, Fluent96_3, Fluent95_3, Fluent79_0, Fluent100_0, Fluent90_5, Fluent30_4, Fluent6_15, Fluent34_15, Fluent135_13, Fluent67_15, Fluent65_18>>

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
=============================================================================
