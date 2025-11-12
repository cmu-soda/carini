--------------------------- MODULE C1_hist ---------------------------


CONSTANTS Address, Core, Value

VARIABLES Fluent153_8, Fluent132_3, Fluent122_13, Fluent117_1, Fluent250_11, Fluent219_5, Fluent299_9, Fluent174_0, Fluent297_8, Fluent269_25, Fluent141_18, Fluent70_12, Fluent179_20, Fluent274_6, Fluent25_6, exclusive, modified, Fluent249_11, Fluent272_3, Fluent170_14, Fluent251_3, Fluent137_23, cache, Fluent78_10, Fluent92_0, Fluent81_25, Fluent258_24, Fluent185_7, Fluent197_21, Fluent75_24, Fluent101_6, Fluent165_11, Fluent205_4, Fluent280_18, Fluent203_9, Fluent33_2, Fluent58_3, Fluent140_18, Fluent243_2, Fluent220_5, Fluent268_25, Fluent295_19, invalid, Fluent262_0, Fluent6_8, Fluent124_9, Fluent176_24, Fluent171_14, shared, Fluent196_21, Fluent82_25, memory, Fluent257_24, Fluent79_10, Fluent128_15, Fluent152_8, Fluent116_1, Fluent72_22, Fluent166_11, Fluent279_18, Fluent175_0, Fluent131_3, Fluent43_14, Fluent298_8, Fluent134_15, Fluent26_6, Fluent300_9, Fluent294_19, Fluent275_6, Fluent271_3, Fluent285_14, Fluent252_3, Fluent177_24, Fluent91_0, Fluent102_6, Fluent186_7, Fluent121_13, Fluent73_22, Fluent108_17, Fluent202_9, Fluent180_20, Fluent57_3, Fluent136_23, Fluent34_2, Fluent135_15, Fluent69_12, Fluent204_4, Fluent261_0, Fluent5_8, Fluent125_9, Fluent286_14, Fluent242_2

vars == <<Fluent153_8, Fluent132_3, Fluent122_13, Fluent117_1, Fluent250_11, Fluent219_5, Fluent299_9, Fluent174_0, Fluent297_8, Fluent269_25, Fluent141_18, Fluent70_12, Fluent179_20, Fluent274_6, Fluent25_6, exclusive, modified, Fluent249_11, Fluent272_3, Fluent170_14, Fluent251_3, Fluent137_23, cache, Fluent78_10, Fluent92_0, Fluent81_25, Fluent258_24, Fluent185_7, Fluent197_21, Fluent75_24, Fluent101_6, Fluent165_11, Fluent205_4, Fluent280_18, Fluent203_9, Fluent33_2, Fluent58_3, Fluent140_18, Fluent243_2, Fluent220_5, Fluent268_25, Fluent295_19, invalid, Fluent262_0, Fluent6_8, Fluent124_9, Fluent176_24, Fluent171_14, shared, Fluent196_21, Fluent82_25, memory, Fluent257_24, Fluent79_10, Fluent128_15, Fluent152_8, Fluent116_1, Fluent72_22, Fluent166_11, Fluent279_18, Fluent175_0, Fluent131_3, Fluent43_14, Fluent298_8, Fluent134_15, Fluent26_6, Fluent300_9, Fluent294_19, Fluent275_6, Fluent271_3, Fluent285_14, Fluent252_3, Fluent177_24, Fluent91_0, Fluent102_6, Fluent186_7, Fluent121_13, Fluent73_22, Fluent108_17, Fluent202_9, Fluent180_20, Fluent57_3, Fluent136_23, Fluent34_2, Fluent135_15, Fluent69_12, Fluent204_4, Fluent261_0, Fluent5_8, Fluent125_9, Fluent286_14, Fluent242_2>>

CandSep ==
/\ \A var0 \in Core : (Fluent176_24[var0]) => (Fluent177_24[var0])
/\ \A var0 \in Core : \A var1 \in Value : \A var2 \in Address : (Fluent91_0[var0][var2][var1]) => (Fluent92_0[var0][var2])
/\ \A var0 \in Value : (Fluent153_8[var0]) => (Fluent152_8[var0])
/\ \A var0 \in Address : (Fluent297_8[var0]) => (Fluent298_8[var0])
/\ \A var0 \in Value : \A var1 \in Address : (Fluent250_11[var1][var0]) => (Fluent249_11[var1][var0])
/\ \A var0 \in Value : \A var1 \in Core : (Fluent220_5[var1][var0]) => (Fluent219_5[var1][var0])
/\ \A var0 \in Address : (Fluent299_9[var0]) => (Fluent300_9[var0])
/\ \A var0 \in Value : (Fluent242_2[var0]) => (~(Fluent243_2[var0]))
/\ \A var0 \in Address : (Fluent140_18[var0]) => (Fluent141_18[var0])
/\ \A var0 \in Value : (Fluent185_7[var0]) => (Fluent186_7[var0])
/\ \A var0 \in Address : \A var1 \in Core : (Fluent179_20[var0]) => (Fluent180_20[var1])
/\ \A var0 \in Core : (Fluent134_15[var0]) => (Fluent135_15[var0])
/\ \A var0 \in Core : (Fluent261_0[var0]) => (Fluent262_0[var0])
/\ \A var0 \in Address : \A var1 \in Core : (Fluent58_3[var0]) => (Fluent57_3[var0][var1])
/\ \A var0 \in Value : \A var1 \in Address : (Fluent166_11[var0][var1]) => (Fluent165_11[var0][var1])
/\ \A var0 \in Address : (Fluent69_12[var0]) => (Fluent70_12[var0])
/\ \A var0 \in Address : (Fluent122_13[var0]) => (~(Fluent121_13[var0]))
/\ \A var0 \in Core : (Fluent82_25[var0]) => (Fluent81_25[var0])
/\ \A var0 \in Core : (Fluent279_18[var0]) => (Fluent280_18[var0])
/\ \A var0 \in Core : (Fluent78_10[var0]) => (Fluent79_10[var0])
/\ \A var0 \in Core : \A var1 \in Address : (Fluent137_23[var1][var0]) => (Fluent136_23[var1][var0])
/\ \A var0 \in Core : (Fluent269_25[var0]) => (Fluent268_25[var0])
/\ \A var0 \in Address : (Fluent197_21[var0]) => (Fluent196_21[var0])
/\ \A var0 \in Address : (Fluent286_14[var0]) => (~(Fluent285_14[var0]))
/\ \A var0 \in Address : (Fluent171_14[var0]) => (Fluent170_14[var0])
/\ \A var0 \in Address : (Fluent271_3[var0]) => (Fluent272_3[var0])
/\ \A var0 \in Value : (Fluent294_19[var0]) => (~(Fluent295_19[var0]))
/\ \A var0 \in Core : \A var1 \in Core : \E var2 \in Value : (Fluent108_17[var2]) => (~(var1 = var0))
/\ \A var0 \in Value : (Fluent5_8[var0]) => (Fluent6_8[var0])
/\ \A var0 \in Address : (Fluent203_9[var0]) => (~(Fluent202_9[var0]))
/\ \A var0 \in Core : (Fluent275_6[var0]) => (Fluent274_6[var0])
/\ \A var0 \in Core : (Fluent72_22[var0]) => (Fluent73_22[var0])
/\ \A var0 \in Address : \A var1 \in Address : \E var2 \in Core : (Fluent43_14[var2]) => (~(var0 = var1))
/\ \A var0 \in Address : (Fluent251_3[var0]) => (Fluent252_3[var0])
/\ \A var0 \in Address : (Fluent125_9[var0]) => (Fluent124_9[var0])
/\ \A var0 \in Core : \A var1 \in Core : \E var2 \in Address : (Fluent75_24[var2]) => (var0 = var1)
/\ \A var0 \in Address : (Fluent204_4[var0]) => (Fluent205_4[var0])
/\ \A var0 \in Value : (Fluent33_2[var0]) => (Fluent34_2[var0])
/\ \A var0 \in Core : (Fluent25_6[var0]) => (Fluent26_6[var0])
/\ \A var0 \in Address : (Fluent132_3[var0]) => (Fluent131_3[var0])
/\ \A var0 \in Core : (Fluent175_0[var0]) => (Fluent174_0[var0])
/\ \A var0 \in Core : (Fluent101_6[var0]) => (Fluent102_6[var0])
/\ \A var0 \in Address : \A var1 \in Address : \E var2 \in Core : (Fluent128_15[var2]) => (var1 = var0)
/\ \A var0 \in Core : (Fluent258_24[var0]) => (~(Fluent257_24[var0]))
/\ \A var0 \in Address : (Fluent117_1[var0]) => (~(Fluent116_1[var0]))

Init ==
/\ (memory \in [Address -> Value])
/\ (cache \in [Core -> [Address -> Value]])
/\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
/\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
/\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
/\ invalid = [c \in Core |-> [a \in Address |-> TRUE]]
/\ Fluent153_8 = [ x0 \in Value |-> FALSE]
/\ Fluent132_3 = [ x0 \in Address |-> FALSE]
/\ Fluent122_13 = [ x0 \in Address |-> FALSE]
/\ Fluent117_1 = [ x0 \in Address |-> FALSE]
/\ Fluent250_11 = [ x0 \in Address |-> [ x1 \in Value |-> FALSE]]
/\ Fluent219_5 = [ x0 \in Core |-> [ x1 \in Value |-> FALSE]]
/\ Fluent299_9 = [ x0 \in Address |-> FALSE]
/\ Fluent174_0 = [ x0 \in Core |-> FALSE]
/\ Fluent297_8 = [ x0 \in Address |-> FALSE]
/\ Fluent269_25 = [ x0 \in Core |-> FALSE]
/\ Fluent141_18 = [ x0 \in Address |-> FALSE]
/\ Fluent70_12 = [ x0 \in Address |-> FALSE]
/\ Fluent179_20 = [ x0 \in Address |-> FALSE]
/\ Fluent274_6 = [ x0 \in Core |-> FALSE]
/\ Fluent25_6 = [ x0 \in Core |-> FALSE]
/\ Fluent249_11 = [ x0 \in Address |-> [ x1 \in Value |-> FALSE]]
/\ Fluent272_3 = [ x0 \in Address |-> FALSE]
/\ Fluent170_14 = [ x0 \in Address |-> FALSE]
/\ Fluent251_3 = [ x0 \in Address |-> FALSE]
/\ Fluent137_23 = [ x0 \in Address |-> [ x1 \in Core |-> FALSE]]
/\ Fluent78_10 = [ x0 \in Core |-> FALSE]
/\ Fluent92_0 = [ x0 \in Core |-> [ x1 \in Address |-> FALSE]]
/\ Fluent81_25 = [ x0 \in Core |-> FALSE]
/\ Fluent258_24 = [ x0 \in Core |-> FALSE]
/\ Fluent185_7 = [ x0 \in Value |-> FALSE]
/\ Fluent197_21 = [ x0 \in Address |-> FALSE]
/\ Fluent75_24 = [ x0 \in Address |-> FALSE]
/\ Fluent101_6 = [ x0 \in Core |-> FALSE]
/\ Fluent165_11 = [ x0 \in Value |-> [ x1 \in Address |-> FALSE]]
/\ Fluent205_4 = [ x0 \in Address |-> FALSE]
/\ Fluent280_18 = [ x0 \in Core |-> FALSE]
/\ Fluent203_9 = [ x0 \in Address |-> FALSE]
/\ Fluent33_2 = [ x0 \in Value |-> FALSE]
/\ Fluent58_3 = [ x0 \in Address |-> FALSE]
/\ Fluent140_18 = [ x0 \in Address |-> FALSE]
/\ Fluent243_2 = [ x0 \in Value |-> FALSE]
/\ Fluent220_5 = [ x0 \in Core |-> [ x1 \in Value |-> FALSE]]
/\ Fluent268_25 = [ x0 \in Core |-> FALSE]
/\ Fluent295_19 = [ x0 \in Value |-> FALSE]
/\ Fluent262_0 = [ x0 \in Core |-> FALSE]
/\ Fluent6_8 = [ x0 \in Value |-> FALSE]
/\ Fluent124_9 = [ x0 \in Address |-> FALSE]
/\ Fluent176_24 = [ x0 \in Core |-> FALSE]
/\ Fluent171_14 = [ x0 \in Address |-> FALSE]
/\ Fluent196_21 = [ x0 \in Address |-> FALSE]
/\ Fluent82_25 = [ x0 \in Core |-> FALSE]
/\ Fluent257_24 = [ x0 \in Core |-> FALSE]
/\ Fluent79_10 = [ x0 \in Core |-> FALSE]
/\ Fluent128_15 = [ x0 \in Core |-> FALSE]
/\ Fluent152_8 = [ x0 \in Value |-> FALSE]
/\ Fluent116_1 = [ x0 \in Address |-> FALSE]
/\ Fluent72_22 = [ x0 \in Core |-> FALSE]
/\ Fluent166_11 = [ x0 \in Value |-> [ x1 \in Address |-> FALSE]]
/\ Fluent279_18 = [ x0 \in Core |-> FALSE]
/\ Fluent175_0 = [ x0 \in Core |-> FALSE]
/\ Fluent131_3 = [ x0 \in Address |-> FALSE]
/\ Fluent43_14 = [ x0 \in Core |-> FALSE]
/\ Fluent298_8 = [ x0 \in Address |-> FALSE]
/\ Fluent134_15 = [ x0 \in Core |-> FALSE]
/\ Fluent26_6 = [ x0 \in Core |-> FALSE]
/\ Fluent300_9 = [ x0 \in Address |-> FALSE]
/\ Fluent294_19 = [ x0 \in Value |-> FALSE]
/\ Fluent275_6 = [ x0 \in Core |-> FALSE]
/\ Fluent271_3 = [ x0 \in Address |-> FALSE]
/\ Fluent285_14 = [ x0 \in Address |-> FALSE]
/\ Fluent252_3 = [ x0 \in Address |-> FALSE]
/\ Fluent177_24 = [ x0 \in Core |-> FALSE]
/\ Fluent91_0 = [ x0 \in Core |-> [ x1 \in Address |-> [ x2 \in Value |-> FALSE]]]
/\ Fluent102_6 = [ x0 \in Core |-> FALSE]
/\ Fluent186_7 = [ x0 \in Value |-> FALSE]
/\ Fluent121_13 = [ x0 \in Address |-> FALSE]
/\ Fluent73_22 = [ x0 \in Core |-> FALSE]
/\ Fluent108_17 = [ x0 \in Value |-> FALSE]
/\ Fluent202_9 = [ x0 \in Address |-> FALSE]
/\ Fluent180_20 = [ x0 \in Core |-> FALSE]
/\ Fluent57_3 = [ x0 \in Address |-> [ x1 \in Core |-> FALSE]]
/\ Fluent136_23 = [ x0 \in Address |-> [ x1 \in Core |-> FALSE]]
/\ Fluent34_2 = [ x0 \in Value |-> FALSE]
/\ Fluent135_15 = [ x0 \in Core |-> FALSE]
/\ Fluent69_12 = [ x0 \in Address |-> FALSE]
/\ Fluent204_4 = [ x0 \in Address |-> FALSE]
/\ Fluent261_0 = [ x0 \in Core |-> FALSE]
/\ Fluent5_8 = [ x0 \in Value |-> FALSE]
/\ Fluent125_9 = [ x0 \in Address |-> FALSE]
/\ Fluent286_14 = [ x0 \in Address |-> FALSE]
/\ Fluent242_2 = [ x0 \in Value |-> FALSE]

issue_proc_read_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,exclusive,shared,invalid>>
/\ Fluent269_25' = [Fluent269_25 EXCEPT ![c] = FALSE]
/\ Fluent70_12' = [[x0 \in Address |-> FALSE] EXCEPT ![a] = TRUE]
/\ Fluent274_6' = [Fluent274_6 EXCEPT ![c] = TRUE]
/\ Fluent25_6' = [Fluent25_6 EXCEPT ![c] = TRUE]
/\ Fluent251_3' = [Fluent251_3 EXCEPT ![a] = FALSE]
/\ Fluent78_10' = [Fluent78_10 EXCEPT ![c] = TRUE]
/\ Fluent92_0' = [Fluent92_0 EXCEPT ![c][a] = TRUE]
/\ Fluent75_24' = [[x0 \in Address |-> FALSE] EXCEPT ![a] = TRUE]
/\ Fluent101_6' = [Fluent101_6 EXCEPT ![c] = FALSE]
/\ Fluent203_9' = [Fluent203_9 EXCEPT ![a] = FALSE]
/\ Fluent176_24' = [Fluent176_24 EXCEPT ![c] = FALSE]
/\ Fluent79_10' = [[x0 \in Core |-> FALSE] EXCEPT ![c] = TRUE]
/\ Fluent175_0' = [Fluent175_0 EXCEPT ![c] = FALSE]
/\ Fluent43_14' = [[x0 \in Core |-> TRUE] EXCEPT ![c] = FALSE]
/\ Fluent298_8' = [Fluent298_8 EXCEPT ![a] = TRUE]
/\ Fluent134_15' = [Fluent134_15 EXCEPT ![c] = FALSE]
/\ Fluent26_6' = [Fluent26_6 EXCEPT ![c] = TRUE]
/\ Fluent271_3' = [Fluent271_3 EXCEPT ![a] = FALSE]
/\ Fluent177_24' = [Fluent177_24 EXCEPT ![c] = FALSE]
/\ Fluent102_6' = [Fluent102_6 EXCEPT ![c] = TRUE]
/\ Fluent73_22' = [Fluent73_22 EXCEPT ![c] = TRUE]
/\ Fluent202_9' = [Fluent202_9 EXCEPT ![a] = FALSE]
/\ Fluent136_23' = [Fluent136_23 EXCEPT ![a][c] = TRUE]
/\ Fluent34_2' = [x0 \in Value |-> FALSE]
/\ Fluent69_12' = [Fluent69_12 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent153_8, Fluent132_3, Fluent122_13, Fluent117_1, Fluent250_11, Fluent219_5, Fluent299_9, Fluent174_0, Fluent297_8, Fluent141_18, Fluent179_20, Fluent249_11, Fluent272_3, Fluent170_14, Fluent137_23, Fluent81_25, Fluent258_24, Fluent185_7, Fluent197_21, Fluent165_11, Fluent205_4, Fluent280_18, Fluent33_2, Fluent58_3, Fluent140_18, Fluent243_2, Fluent220_5, Fluent268_25, Fluent295_19, Fluent262_0, Fluent6_8, Fluent124_9, Fluent171_14, Fluent196_21, Fluent82_25, Fluent257_24, Fluent128_15, Fluent152_8, Fluent116_1, Fluent72_22, Fluent166_11, Fluent279_18, Fluent131_3, Fluent300_9, Fluent294_19, Fluent275_6, Fluent285_14, Fluent252_3, Fluent91_0, Fluent186_7, Fluent121_13, Fluent108_17, Fluent180_20, Fluent57_3, Fluent135_15, Fluent204_4, Fluent261_0, Fluent5_8, Fluent125_9, Fluent286_14, Fluent242_2>>
/\ CandSep'

do_bus_read_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,exclusive,shared,invalid>>
/\ Fluent299_9' = [[x0 \in Address |-> TRUE] EXCEPT ![a] = FALSE]
/\ Fluent81_25' = [Fluent81_25 EXCEPT ![c] = TRUE]
/\ Fluent203_9' = [Fluent203_9 EXCEPT ![a] = TRUE]
/\ Fluent196_21' = [Fluent196_21 EXCEPT ![a] = TRUE]
/\ Fluent131_3' = [Fluent131_3 EXCEPT ![a] = TRUE]
/\ Fluent43_14' = [Fluent43_14 EXCEPT ![c] = TRUE]
/\ Fluent300_9' = [x0 \in Address |-> TRUE]
/\ Fluent252_3' = [Fluent252_3 EXCEPT ![a] = FALSE]
/\ Fluent177_24' = [x0 \in Core |-> TRUE]
/\ UNCHANGED<<Fluent153_8, Fluent132_3, Fluent122_13, Fluent117_1, Fluent250_11, Fluent219_5, Fluent174_0, Fluent297_8, Fluent269_25, Fluent141_18, Fluent70_12, Fluent179_20, Fluent274_6, Fluent25_6, Fluent249_11, Fluent272_3, Fluent170_14, Fluent251_3, Fluent137_23, Fluent78_10, Fluent92_0, Fluent258_24, Fluent185_7, Fluent197_21, Fluent75_24, Fluent101_6, Fluent165_11, Fluent205_4, Fluent280_18, Fluent33_2, Fluent58_3, Fluent140_18, Fluent243_2, Fluent220_5, Fluent268_25, Fluent295_19, Fluent262_0, Fluent6_8, Fluent124_9, Fluent176_24, Fluent171_14, Fluent82_25, Fluent257_24, Fluent79_10, Fluent128_15, Fluent152_8, Fluent116_1, Fluent72_22, Fluent166_11, Fluent279_18, Fluent175_0, Fluent298_8, Fluent134_15, Fluent26_6, Fluent294_19, Fluent275_6, Fluent271_3, Fluent285_14, Fluent91_0, Fluent102_6, Fluent186_7, Fluent121_13, Fluent73_22, Fluent108_17, Fluent202_9, Fluent180_20, Fluent57_3, Fluent136_23, Fluent34_2, Fluent135_15, Fluent69_12, Fluent204_4, Fluent261_0, Fluent5_8, Fluent125_9, Fluent286_14, Fluent242_2>>
/\ CandSep'

do_bus_read_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ cache[c][a] = v
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ (modified[c][a] => memory' = [memory EXCEPT![a] = v])
/\ (~(modified[c][a]) => memory' = memory)
/\ UNCHANGED <<cache,invalid>>
/\ Fluent141_18' = [Fluent141_18 EXCEPT ![a] = TRUE]
/\ Fluent272_3' = [Fluent272_3 EXCEPT ![a] = TRUE]
/\ Fluent170_14' = [Fluent170_14 EXCEPT ![a] = TRUE]
/\ Fluent75_24' = [Fluent75_24 EXCEPT ![a] = TRUE]
/\ Fluent140_18' = [Fluent140_18 EXCEPT ![a] = TRUE]
/\ Fluent6_8' = [Fluent6_8 EXCEPT ![v] = TRUE]
/\ Fluent152_8' = [Fluent152_8 EXCEPT ![v] = TRUE]
/\ Fluent72_22' = [[x0 \in Core |-> TRUE] EXCEPT ![c] = FALSE]
/\ Fluent131_3' = [Fluent131_3 EXCEPT ![a] = TRUE]
/\ Fluent271_3' = [Fluent271_3 EXCEPT ![a] = TRUE]
/\ Fluent202_9' = [Fluent202_9 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent153_8, Fluent132_3, Fluent122_13, Fluent117_1, Fluent250_11, Fluent219_5, Fluent299_9, Fluent174_0, Fluent297_8, Fluent269_25, Fluent70_12, Fluent179_20, Fluent274_6, Fluent25_6, Fluent249_11, Fluent251_3, Fluent137_23, Fluent78_10, Fluent92_0, Fluent81_25, Fluent258_24, Fluent185_7, Fluent197_21, Fluent101_6, Fluent165_11, Fluent205_4, Fluent280_18, Fluent203_9, Fluent33_2, Fluent58_3, Fluent243_2, Fluent220_5, Fluent268_25, Fluent295_19, Fluent262_0, Fluent124_9, Fluent176_24, Fluent171_14, Fluent196_21, Fluent82_25, Fluent257_24, Fluent79_10, Fluent128_15, Fluent116_1, Fluent166_11, Fluent279_18, Fluent175_0, Fluent43_14, Fluent298_8, Fluent134_15, Fluent26_6, Fluent300_9, Fluent294_19, Fluent275_6, Fluent285_14, Fluent252_3, Fluent177_24, Fluent91_0, Fluent102_6, Fluent186_7, Fluent121_13, Fluent73_22, Fluent108_17, Fluent180_20, Fluent57_3, Fluent136_23, Fluent34_2, Fluent135_15, Fluent69_12, Fluent204_4, Fluent261_0, Fluent5_8, Fluent125_9, Fluent286_14, Fluent242_2>>
/\ CandSep'

complete_proc_read_invalid_shared(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,modified,exclusive>>
/\ Fluent153_8' = [Fluent153_8 EXCEPT ![v] = TRUE]
/\ Fluent132_3' = [Fluent132_3 EXCEPT ![a] = TRUE]
/\ Fluent25_6' = [Fluent25_6 EXCEPT ![c] = FALSE]
/\ Fluent137_23' = [Fluent137_23 EXCEPT ![a][c] = TRUE]
/\ Fluent78_10' = [Fluent78_10 EXCEPT ![c] = FALSE]
/\ Fluent140_18' = [Fluent140_18 EXCEPT ![a] = FALSE]
/\ Fluent268_25' = [Fluent268_25 EXCEPT ![c] = FALSE]
/\ Fluent171_14' = [Fluent171_14 EXCEPT ![a] = TRUE]
/\ Fluent275_6' = [Fluent275_6 EXCEPT ![c] = TRUE]
/\ Fluent102_6' = [Fluent102_6 EXCEPT ![c] = FALSE]
/\ Fluent69_12' = [Fluent69_12 EXCEPT ![a] = FALSE]
/\ Fluent5_8' = [Fluent5_8 EXCEPT ![v] = TRUE]
/\ UNCHANGED<<Fluent122_13, Fluent117_1, Fluent250_11, Fluent219_5, Fluent299_9, Fluent174_0, Fluent297_8, Fluent269_25, Fluent141_18, Fluent70_12, Fluent179_20, Fluent274_6, Fluent249_11, Fluent272_3, Fluent170_14, Fluent251_3, Fluent92_0, Fluent81_25, Fluent258_24, Fluent185_7, Fluent197_21, Fluent75_24, Fluent101_6, Fluent165_11, Fluent205_4, Fluent280_18, Fluent203_9, Fluent33_2, Fluent58_3, Fluent243_2, Fluent220_5, Fluent295_19, Fluent262_0, Fluent6_8, Fluent124_9, Fluent176_24, Fluent196_21, Fluent82_25, Fluent257_24, Fluent79_10, Fluent128_15, Fluent152_8, Fluent116_1, Fluent72_22, Fluent166_11, Fluent279_18, Fluent175_0, Fluent131_3, Fluent43_14, Fluent298_8, Fluent134_15, Fluent26_6, Fluent300_9, Fluent294_19, Fluent271_3, Fluent285_14, Fluent252_3, Fluent177_24, Fluent91_0, Fluent186_7, Fluent121_13, Fluent73_22, Fluent108_17, Fluent202_9, Fluent180_20, Fluent57_3, Fluent136_23, Fluent34_2, Fluent135_15, Fluent204_4, Fluent261_0, Fluent125_9, Fluent286_14, Fluent242_2>>
/\ CandSep'

complete_proc_read_invalid_exclusive(c,a,v) ==
/\ invalid[c][a]
/\ memory[a] = v
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,modified,shared>>
/\ Fluent174_0' = [Fluent174_0 EXCEPT ![c] = FALSE]
/\ Fluent297_8' = [Fluent297_8 EXCEPT ![a] = TRUE]
/\ Fluent25_6' = [Fluent25_6 EXCEPT ![c] = FALSE]
/\ Fluent272_3' = [Fluent272_3 EXCEPT ![a] = FALSE]
/\ Fluent251_3' = [Fluent251_3 EXCEPT ![a] = TRUE]
/\ Fluent78_10' = [Fluent78_10 EXCEPT ![c] = FALSE]
/\ Fluent197_21' = [Fluent197_21 EXCEPT ![a] = TRUE]
/\ Fluent101_6' = [Fluent101_6 EXCEPT ![c] = TRUE]
/\ Fluent176_24' = [Fluent176_24 EXCEPT ![c] = TRUE]
/\ Fluent82_25' = [[x0 \in Core |-> TRUE] EXCEPT ![c] = FALSE]
/\ Fluent300_9' = [Fluent300_9 EXCEPT ![a] = FALSE]
/\ Fluent252_3' = [Fluent252_3 EXCEPT ![a] = TRUE]
/\ Fluent91_0' = [Fluent91_0 EXCEPT ![c][a][v] = TRUE]
/\ Fluent135_15' = [Fluent135_15 EXCEPT ![c] = FALSE]
/\ Fluent69_12' = [Fluent69_12 EXCEPT ![a] = FALSE]
/\ UNCHANGED<<Fluent153_8, Fluent132_3, Fluent122_13, Fluent117_1, Fluent250_11, Fluent219_5, Fluent299_9, Fluent269_25, Fluent141_18, Fluent70_12, Fluent179_20, Fluent274_6, Fluent249_11, Fluent170_14, Fluent137_23, Fluent92_0, Fluent81_25, Fluent258_24, Fluent185_7, Fluent75_24, Fluent165_11, Fluent205_4, Fluent280_18, Fluent203_9, Fluent33_2, Fluent58_3, Fluent140_18, Fluent243_2, Fluent220_5, Fluent268_25, Fluent295_19, Fluent262_0, Fluent6_8, Fluent124_9, Fluent171_14, Fluent196_21, Fluent257_24, Fluent79_10, Fluent128_15, Fluent152_8, Fluent116_1, Fluent72_22, Fluent166_11, Fluent279_18, Fluent175_0, Fluent131_3, Fluent43_14, Fluent298_8, Fluent134_15, Fluent26_6, Fluent294_19, Fluent275_6, Fluent271_3, Fluent285_14, Fluent177_24, Fluent102_6, Fluent186_7, Fluent121_13, Fluent73_22, Fluent108_17, Fluent202_9, Fluent180_20, Fluent57_3, Fluent136_23, Fluent34_2, Fluent204_4, Fluent261_0, Fluent5_8, Fluent125_9, Fluent286_14, Fluent242_2>>
/\ CandSep'

issue_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,exclusive,shared,invalid>>
/\ Fluent122_13' = [Fluent122_13 EXCEPT ![a] = TRUE]
/\ Fluent117_1' = [Fluent117_1 EXCEPT ![a] = FALSE]
/\ Fluent219_5' = [Fluent219_5 EXCEPT ![c][v] = TRUE]
/\ Fluent249_11' = [Fluent249_11 EXCEPT ![a][v] = TRUE]
/\ Fluent197_21' = [Fluent197_21 EXCEPT ![a] = FALSE]
/\ Fluent165_11' = [Fluent165_11 EXCEPT ![v][a] = TRUE]
/\ Fluent205_4' = [Fluent205_4 EXCEPT ![a] = TRUE]
/\ Fluent280_18' = [Fluent280_18 EXCEPT ![c] = TRUE]
/\ Fluent33_2' = [Fluent33_2 EXCEPT ![v] = TRUE]
/\ Fluent243_2' = [x0 \in Value |-> FALSE]
/\ Fluent295_19' = [Fluent295_19 EXCEPT ![v] = FALSE]
/\ Fluent262_0' = [Fluent262_0 EXCEPT ![c] = TRUE]
/\ Fluent196_21' = [Fluent196_21 EXCEPT ![a] = FALSE]
/\ Fluent128_15' = [[x0 \in Core |-> FALSE] EXCEPT ![c] = TRUE]
/\ Fluent116_1' = [Fluent116_1 EXCEPT ![a] = TRUE]
/\ Fluent26_6' = [x0 \in Core |-> FALSE]
/\ Fluent121_13' = [Fluent121_13 EXCEPT ![a] = FALSE]
/\ Fluent108_17' = [Fluent108_17 EXCEPT ![v] = TRUE]
/\ Fluent57_3' = [Fluent57_3 EXCEPT ![a][c] = TRUE]
/\ Fluent34_2' = [Fluent34_2 EXCEPT ![v] = TRUE]
/\ UNCHANGED<<Fluent153_8, Fluent132_3, Fluent250_11, Fluent299_9, Fluent174_0, Fluent297_8, Fluent269_25, Fluent141_18, Fluent70_12, Fluent179_20, Fluent274_6, Fluent25_6, Fluent272_3, Fluent170_14, Fluent251_3, Fluent137_23, Fluent78_10, Fluent92_0, Fluent81_25, Fluent258_24, Fluent185_7, Fluent75_24, Fluent101_6, Fluent203_9, Fluent58_3, Fluent140_18, Fluent220_5, Fluent268_25, Fluent6_8, Fluent124_9, Fluent176_24, Fluent171_14, Fluent82_25, Fluent257_24, Fluent79_10, Fluent152_8, Fluent72_22, Fluent166_11, Fluent279_18, Fluent175_0, Fluent131_3, Fluent43_14, Fluent298_8, Fluent134_15, Fluent300_9, Fluent294_19, Fluent275_6, Fluent271_3, Fluent285_14, Fluent252_3, Fluent177_24, Fluent91_0, Fluent102_6, Fluent186_7, Fluent73_22, Fluent202_9, Fluent180_20, Fluent136_23, Fluent135_15, Fluent69_12, Fluent204_4, Fluent261_0, Fluent5_8, Fluent125_9, Fluent286_14, Fluent242_2>>
/\ CandSep'

do_bus_read_for_ownership_invalid(c,a) ==
/\ invalid[c][a]
/\ UNCHANGED <<memory,cache,modified,exclusive,shared,invalid>>
/\ Fluent58_3' = [Fluent58_3 EXCEPT ![a] = TRUE]
/\ Fluent116_1' = [Fluent116_1 EXCEPT ![a] = FALSE]
/\ Fluent279_18' = [[x0 \in Core |-> TRUE] EXCEPT ![c] = FALSE]
/\ Fluent57_3' = [Fluent57_3 EXCEPT ![a][c] = TRUE]
/\ UNCHANGED<<Fluent153_8, Fluent132_3, Fluent122_13, Fluent117_1, Fluent250_11, Fluent219_5, Fluent299_9, Fluent174_0, Fluent297_8, Fluent269_25, Fluent141_18, Fluent70_12, Fluent179_20, Fluent274_6, Fluent25_6, Fluent249_11, Fluent272_3, Fluent170_14, Fluent251_3, Fluent137_23, Fluent78_10, Fluent92_0, Fluent81_25, Fluent258_24, Fluent185_7, Fluent197_21, Fluent75_24, Fluent101_6, Fluent165_11, Fluent205_4, Fluent280_18, Fluent203_9, Fluent33_2, Fluent140_18, Fluent243_2, Fluent220_5, Fluent268_25, Fluent295_19, Fluent262_0, Fluent6_8, Fluent124_9, Fluent176_24, Fluent171_14, Fluent196_21, Fluent82_25, Fluent257_24, Fluent79_10, Fluent128_15, Fluent152_8, Fluent72_22, Fluent166_11, Fluent175_0, Fluent131_3, Fluent43_14, Fluent298_8, Fluent134_15, Fluent26_6, Fluent300_9, Fluent294_19, Fluent275_6, Fluent271_3, Fluent285_14, Fluent252_3, Fluent177_24, Fluent91_0, Fluent102_6, Fluent186_7, Fluent121_13, Fluent73_22, Fluent108_17, Fluent202_9, Fluent180_20, Fluent136_23, Fluent34_2, Fluent135_15, Fluent69_12, Fluent204_4, Fluent261_0, Fluent5_8, Fluent125_9, Fluent286_14, Fluent242_2>>
/\ CandSep'

do_bus_read_for_ownership_valid(c,a,v) ==
/\ ~(invalid[c][a])
/\ cache[c][a] = v
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ (modified[c][a] => memory' = [memory EXCEPT![a] = v])
/\ (~(modified[c][a]) => memory' = memory)
/\ UNCHANGED <<cache>>
/\ Fluent170_14' = [x0 \in Address |-> TRUE]
/\ Fluent6_8' = [Fluent6_8 EXCEPT ![v] = TRUE]
/\ Fluent116_1' = [Fluent116_1 EXCEPT ![a] = FALSE]
/\ Fluent204_4' = [Fluent204_4 EXCEPT ![a] = TRUE]
/\ Fluent242_2' = [Fluent242_2 EXCEPT ![v] = TRUE]
/\ UNCHANGED<<Fluent153_8, Fluent132_3, Fluent122_13, Fluent117_1, Fluent250_11, Fluent219_5, Fluent299_9, Fluent174_0, Fluent297_8, Fluent269_25, Fluent141_18, Fluent70_12, Fluent179_20, Fluent274_6, Fluent25_6, Fluent249_11, Fluent272_3, Fluent251_3, Fluent137_23, Fluent78_10, Fluent92_0, Fluent81_25, Fluent258_24, Fluent185_7, Fluent197_21, Fluent75_24, Fluent101_6, Fluent165_11, Fluent205_4, Fluent280_18, Fluent203_9, Fluent33_2, Fluent58_3, Fluent140_18, Fluent243_2, Fluent220_5, Fluent268_25, Fluent295_19, Fluent262_0, Fluent124_9, Fluent176_24, Fluent171_14, Fluent196_21, Fluent82_25, Fluent257_24, Fluent79_10, Fluent128_15, Fluent152_8, Fluent72_22, Fluent166_11, Fluent279_18, Fluent175_0, Fluent131_3, Fluent43_14, Fluent298_8, Fluent134_15, Fluent26_6, Fluent300_9, Fluent294_19, Fluent275_6, Fluent271_3, Fluent285_14, Fluent252_3, Fluent177_24, Fluent91_0, Fluent102_6, Fluent186_7, Fluent121_13, Fluent73_22, Fluent108_17, Fluent202_9, Fluent180_20, Fluent57_3, Fluent136_23, Fluent34_2, Fluent135_15, Fluent69_12, Fluent261_0, Fluent5_8, Fluent125_9, Fluent286_14>>
/\ CandSep'

complete_proc_write_invalid(c,a,v) ==
/\ invalid[c][a]
/\ invalid' = [invalid EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,exclusive,shared>>
/\ Fluent122_13' = [Fluent122_13 EXCEPT ![a] = FALSE]
/\ Fluent117_1' = [Fluent117_1 EXCEPT ![a] = TRUE]
/\ Fluent250_11' = [Fluent250_11 EXCEPT ![a][v] = TRUE]
/\ Fluent185_7' = [Fluent185_7 EXCEPT ![v] = FALSE]
/\ Fluent280_18' = [Fluent280_18 EXCEPT ![c] = FALSE]
/\ Fluent33_2' = [Fluent33_2 EXCEPT ![v] = FALSE]
/\ Fluent243_2' = [Fluent243_2 EXCEPT ![v] = TRUE]
/\ Fluent220_5' = [Fluent220_5 EXCEPT ![c][v] = TRUE]
/\ Fluent295_19' = [Fluent295_19 EXCEPT ![v] = TRUE]
/\ Fluent257_24' = [Fluent257_24 EXCEPT ![c] = FALSE]
/\ Fluent128_15' = [Fluent128_15 EXCEPT ![c] = TRUE]
/\ Fluent279_18' = [Fluent279_18 EXCEPT ![c] = FALSE]
/\ Fluent294_19' = [Fluent294_19 EXCEPT ![v] = FALSE]
/\ Fluent121_13' = [x0 \in Address |-> TRUE]
/\ Fluent108_17' = [Fluent108_17 EXCEPT ![v] = FALSE]
/\ Fluent242_2' = [Fluent242_2 EXCEPT ![v] = FALSE]
/\ UNCHANGED<<Fluent153_8, Fluent132_3, Fluent219_5, Fluent299_9, Fluent174_0, Fluent297_8, Fluent269_25, Fluent141_18, Fluent70_12, Fluent179_20, Fluent274_6, Fluent25_6, Fluent249_11, Fluent272_3, Fluent170_14, Fluent251_3, Fluent137_23, Fluent78_10, Fluent92_0, Fluent81_25, Fluent258_24, Fluent197_21, Fluent75_24, Fluent101_6, Fluent165_11, Fluent205_4, Fluent203_9, Fluent58_3, Fluent140_18, Fluent268_25, Fluent262_0, Fluent6_8, Fluent124_9, Fluent176_24, Fluent171_14, Fluent196_21, Fluent82_25, Fluent79_10, Fluent152_8, Fluent116_1, Fluent72_22, Fluent166_11, Fluent175_0, Fluent131_3, Fluent43_14, Fluent298_8, Fluent134_15, Fluent26_6, Fluent300_9, Fluent275_6, Fluent271_3, Fluent285_14, Fluent252_3, Fluent177_24, Fluent91_0, Fluent102_6, Fluent186_7, Fluent73_22, Fluent202_9, Fluent180_20, Fluent57_3, Fluent136_23, Fluent34_2, Fluent135_15, Fluent69_12, Fluent204_4, Fluent261_0, Fluent5_8, Fluent125_9, Fluent286_14>>
/\ CandSep'

proc_write_exclusive(c,a,v) ==
/\ exclusive[c][a]
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,invalid,shared>>
/\ Fluent174_0' = [Fluent174_0 EXCEPT ![c] = TRUE]
/\ Fluent297_8' = [Fluent297_8 EXCEPT ![a] = FALSE]
/\ Fluent175_0' = [Fluent175_0 EXCEPT ![c] = TRUE]
/\ Fluent298_8' = [Fluent298_8 EXCEPT ![a] = FALSE]
/\ UNCHANGED<<Fluent153_8, Fluent132_3, Fluent122_13, Fluent117_1, Fluent250_11, Fluent219_5, Fluent299_9, Fluent269_25, Fluent141_18, Fluent70_12, Fluent179_20, Fluent274_6, Fluent25_6, Fluent249_11, Fluent272_3, Fluent170_14, Fluent251_3, Fluent137_23, Fluent78_10, Fluent92_0, Fluent81_25, Fluent258_24, Fluent185_7, Fluent197_21, Fluent75_24, Fluent101_6, Fluent165_11, Fluent205_4, Fluent280_18, Fluent203_9, Fluent33_2, Fluent58_3, Fluent140_18, Fluent243_2, Fluent220_5, Fluent268_25, Fluent295_19, Fluent262_0, Fluent6_8, Fluent124_9, Fluent176_24, Fluent171_14, Fluent196_21, Fluent82_25, Fluent257_24, Fluent79_10, Fluent128_15, Fluent152_8, Fluent116_1, Fluent72_22, Fluent166_11, Fluent279_18, Fluent131_3, Fluent43_14, Fluent134_15, Fluent26_6, Fluent300_9, Fluent294_19, Fluent275_6, Fluent271_3, Fluent285_14, Fluent252_3, Fluent177_24, Fluent91_0, Fluent102_6, Fluent186_7, Fluent121_13, Fluent73_22, Fluent108_17, Fluent202_9, Fluent180_20, Fluent57_3, Fluent136_23, Fluent34_2, Fluent135_15, Fluent69_12, Fluent204_4, Fluent261_0, Fluent5_8, Fluent125_9, Fluent286_14, Fluent242_2>>
/\ CandSep'

issue_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ UNCHANGED <<memory,cache,modified,exclusive,shared,invalid>>
/\ Fluent219_5' = [Fluent219_5 EXCEPT ![c][v] = TRUE]
/\ Fluent269_25' = [x0 \in Core |-> TRUE]
/\ Fluent141_18' = [Fluent141_18 EXCEPT ![a] = FALSE]
/\ Fluent249_11' = [Fluent249_11 EXCEPT ![a][v] = TRUE]
/\ Fluent258_24' = [[x0 \in Core |-> TRUE] EXCEPT ![c] = FALSE]
/\ Fluent185_7' = [Fluent185_7 EXCEPT ![v] = TRUE]
/\ Fluent165_11' = [Fluent165_11 EXCEPT ![v][a] = TRUE]
/\ Fluent268_25' = [x0 \in Core |-> TRUE]
/\ Fluent295_19' = [Fluent295_19 EXCEPT ![v] = FALSE]
/\ Fluent262_0' = [Fluent262_0 EXCEPT ![c] = TRUE]
/\ Fluent124_9' = [Fluent124_9 EXCEPT ![a] = TRUE]
/\ Fluent257_24' = [Fluent257_24 EXCEPT ![c] = TRUE]
/\ Fluent128_15' = [x0 \in Core |-> FALSE]
/\ Fluent285_14' = [Fluent285_14 EXCEPT ![a] = TRUE]
/\ Fluent186_7' = [Fluent186_7 EXCEPT ![v] = TRUE]
/\ Fluent180_20' = [Fluent180_20 EXCEPT ![c] = TRUE]
/\ Fluent286_14' = [Fluent286_14 EXCEPT ![a] = FALSE]
/\ UNCHANGED<<Fluent153_8, Fluent132_3, Fluent122_13, Fluent117_1, Fluent250_11, Fluent299_9, Fluent174_0, Fluent297_8, Fluent70_12, Fluent179_20, Fluent274_6, Fluent25_6, Fluent272_3, Fluent170_14, Fluent251_3, Fluent137_23, Fluent78_10, Fluent92_0, Fluent81_25, Fluent197_21, Fluent75_24, Fluent101_6, Fluent205_4, Fluent280_18, Fluent203_9, Fluent33_2, Fluent58_3, Fluent140_18, Fluent243_2, Fluent220_5, Fluent6_8, Fluent176_24, Fluent171_14, Fluent196_21, Fluent82_25, Fluent79_10, Fluent152_8, Fluent116_1, Fluent72_22, Fluent166_11, Fluent279_18, Fluent175_0, Fluent131_3, Fluent43_14, Fluent298_8, Fluent134_15, Fluent26_6, Fluent300_9, Fluent294_19, Fluent275_6, Fluent271_3, Fluent252_3, Fluent177_24, Fluent91_0, Fluent102_6, Fluent121_13, Fluent73_22, Fluent108_17, Fluent202_9, Fluent57_3, Fluent136_23, Fluent34_2, Fluent135_15, Fluent69_12, Fluent204_4, Fluent261_0, Fluent5_8, Fluent125_9, Fluent242_2>>
/\ CandSep'

do_bus_upgrade(c,a) ==
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ UNCHANGED <<memory,cache,modified,exclusive>>
/\ Fluent179_20' = [Fluent179_20 EXCEPT ![a] = TRUE]
/\ Fluent285_14' = [Fluent285_14 EXCEPT ![a] = FALSE]
/\ Fluent180_20' = [Fluent180_20 EXCEPT ![c] = TRUE]
/\ Fluent125_9' = [Fluent125_9 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent153_8, Fluent132_3, Fluent122_13, Fluent117_1, Fluent250_11, Fluent219_5, Fluent299_9, Fluent174_0, Fluent297_8, Fluent269_25, Fluent141_18, Fluent70_12, Fluent274_6, Fluent25_6, Fluent249_11, Fluent272_3, Fluent170_14, Fluent251_3, Fluent137_23, Fluent78_10, Fluent92_0, Fluent81_25, Fluent258_24, Fluent185_7, Fluent197_21, Fluent75_24, Fluent101_6, Fluent165_11, Fluent205_4, Fluent280_18, Fluent203_9, Fluent33_2, Fluent58_3, Fluent140_18, Fluent243_2, Fluent220_5, Fluent268_25, Fluent295_19, Fluent262_0, Fluent6_8, Fluent124_9, Fluent176_24, Fluent171_14, Fluent196_21, Fluent82_25, Fluent257_24, Fluent79_10, Fluent128_15, Fluent152_8, Fluent116_1, Fluent72_22, Fluent166_11, Fluent279_18, Fluent175_0, Fluent131_3, Fluent43_14, Fluent298_8, Fluent134_15, Fluent26_6, Fluent300_9, Fluent294_19, Fluent275_6, Fluent271_3, Fluent252_3, Fluent177_24, Fluent91_0, Fluent102_6, Fluent186_7, Fluent121_13, Fluent73_22, Fluent108_17, Fluent202_9, Fluent57_3, Fluent136_23, Fluent34_2, Fluent135_15, Fluent69_12, Fluent204_4, Fluent261_0, Fluent5_8, Fluent286_14, Fluent242_2>>
/\ CandSep'

complete_proc_write_shared(c,a,v) ==
/\ shared[c][a]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ modified' = [modified EXCEPT![c][a] = TRUE]
/\ cache' = [cache EXCEPT![c][a] = v]
/\ UNCHANGED <<memory,invalid,exclusive>>
/\ Fluent122_13' = [Fluent122_13 EXCEPT ![a] = FALSE]
/\ Fluent185_7' = [Fluent185_7 EXCEPT ![v] = FALSE]
/\ Fluent33_2' = [Fluent33_2 EXCEPT ![v] = FALSE]
/\ Fluent257_24' = [Fluent257_24 EXCEPT ![c] = FALSE]
/\ Fluent152_8' = [x0 \in Value |-> TRUE]
/\ Fluent166_11' = [Fluent166_11 EXCEPT ![v][a] = TRUE]
/\ Fluent294_19' = [Fluent294_19 EXCEPT ![v] = TRUE]
/\ Fluent108_17' = [Fluent108_17 EXCEPT ![v] = FALSE]
/\ Fluent261_0' = [Fluent261_0 EXCEPT ![c] = TRUE]
/\ Fluent286_14' = [Fluent286_14 EXCEPT ![a] = TRUE]
/\ UNCHANGED<<Fluent153_8, Fluent132_3, Fluent117_1, Fluent250_11, Fluent219_5, Fluent299_9, Fluent174_0, Fluent297_8, Fluent269_25, Fluent141_18, Fluent70_12, Fluent179_20, Fluent274_6, Fluent25_6, Fluent249_11, Fluent272_3, Fluent170_14, Fluent251_3, Fluent137_23, Fluent78_10, Fluent92_0, Fluent81_25, Fluent258_24, Fluent197_21, Fluent75_24, Fluent101_6, Fluent165_11, Fluent205_4, Fluent280_18, Fluent203_9, Fluent58_3, Fluent140_18, Fluent243_2, Fluent220_5, Fluent268_25, Fluent295_19, Fluent262_0, Fluent6_8, Fluent124_9, Fluent176_24, Fluent171_14, Fluent196_21, Fluent82_25, Fluent79_10, Fluent128_15, Fluent116_1, Fluent72_22, Fluent279_18, Fluent175_0, Fluent131_3, Fluent43_14, Fluent298_8, Fluent134_15, Fluent26_6, Fluent300_9, Fluent275_6, Fluent271_3, Fluent285_14, Fluent252_3, Fluent177_24, Fluent91_0, Fluent102_6, Fluent186_7, Fluent121_13, Fluent73_22, Fluent202_9, Fluent180_20, Fluent57_3, Fluent136_23, Fluent34_2, Fluent135_15, Fluent69_12, Fluent204_4, Fluent5_8, Fluent125_9, Fluent242_2>>
/\ CandSep'

evict_modified(c,a) ==
/\ modified[c][a]
/\ memory' = [memory EXCEPT![a] = cache[c][a]]
/\ modified' = [modified EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<cache,exclusive,shared>>
/\ UNCHANGED<<Fluent153_8, Fluent132_3, Fluent122_13, Fluent117_1, Fluent250_11, Fluent219_5, Fluent299_9, Fluent174_0, Fluent297_8, Fluent269_25, Fluent141_18, Fluent70_12, Fluent179_20, Fluent274_6, Fluent25_6, Fluent249_11, Fluent272_3, Fluent170_14, Fluent251_3, Fluent137_23, Fluent78_10, Fluent92_0, Fluent81_25, Fluent258_24, Fluent185_7, Fluent197_21, Fluent75_24, Fluent101_6, Fluent165_11, Fluent205_4, Fluent280_18, Fluent203_9, Fluent33_2, Fluent58_3, Fluent140_18, Fluent243_2, Fluent220_5, Fluent268_25, Fluent295_19, Fluent262_0, Fluent6_8, Fluent124_9, Fluent176_24, Fluent171_14, Fluent196_21, Fluent82_25, Fluent257_24, Fluent79_10, Fluent128_15, Fluent152_8, Fluent116_1, Fluent72_22, Fluent166_11, Fluent279_18, Fluent175_0, Fluent131_3, Fluent43_14, Fluent298_8, Fluent134_15, Fluent26_6, Fluent300_9, Fluent294_19, Fluent275_6, Fluent271_3, Fluent285_14, Fluent252_3, Fluent177_24, Fluent91_0, Fluent102_6, Fluent186_7, Fluent121_13, Fluent73_22, Fluent108_17, Fluent202_9, Fluent180_20, Fluent57_3, Fluent136_23, Fluent34_2, Fluent135_15, Fluent69_12, Fluent204_4, Fluent261_0, Fluent5_8, Fluent125_9, Fluent286_14, Fluent242_2>>
/\ CandSep'

evict_exclusive_or_shared(c,a) ==
/\ (exclusive[c][a] \/ shared[c][a])
/\ exclusive' = [exclusive EXCEPT![c][a] = FALSE]
/\ shared' = [shared EXCEPT![c][a] = FALSE]
/\ invalid' = [invalid EXCEPT![c][a] = TRUE]
/\ UNCHANGED <<memory,cache,modified>>
/\ Fluent274_6' = [Fluent274_6 EXCEPT ![c] = FALSE]
/\ Fluent134_15' = [Fluent134_15 EXCEPT ![c] = TRUE]
/\ Fluent275_6' = [Fluent275_6 EXCEPT ![c] = FALSE]
/\ Fluent186_7' = [x0 \in Value |-> FALSE]
/\ Fluent135_15' = [Fluent135_15 EXCEPT ![c] = TRUE]
/\ UNCHANGED<<Fluent153_8, Fluent132_3, Fluent122_13, Fluent117_1, Fluent250_11, Fluent219_5, Fluent299_9, Fluent174_0, Fluent297_8, Fluent269_25, Fluent141_18, Fluent70_12, Fluent179_20, Fluent25_6, Fluent249_11, Fluent272_3, Fluent170_14, Fluent251_3, Fluent137_23, Fluent78_10, Fluent92_0, Fluent81_25, Fluent258_24, Fluent185_7, Fluent197_21, Fluent75_24, Fluent101_6, Fluent165_11, Fluent205_4, Fluent280_18, Fluent203_9, Fluent33_2, Fluent58_3, Fluent140_18, Fluent243_2, Fluent220_5, Fluent268_25, Fluent295_19, Fluent262_0, Fluent6_8, Fluent124_9, Fluent176_24, Fluent171_14, Fluent196_21, Fluent82_25, Fluent257_24, Fluent79_10, Fluent128_15, Fluent152_8, Fluent116_1, Fluent72_22, Fluent166_11, Fluent279_18, Fluent175_0, Fluent131_3, Fluent43_14, Fluent298_8, Fluent26_6, Fluent300_9, Fluent294_19, Fluent271_3, Fluent285_14, Fluent252_3, Fluent177_24, Fluent91_0, Fluent102_6, Fluent121_13, Fluent73_22, Fluent108_17, Fluent202_9, Fluent180_20, Fluent57_3, Fluent136_23, Fluent34_2, Fluent69_12, Fluent204_4, Fluent261_0, Fluent5_8, Fluent125_9, Fluent286_14, Fluent242_2>>
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

Safety == (\A C \in Core : (\A A \in Address : ((~(invalid[C][A]) /\ ~(modified[C][A])) => cache[C][A] = memory[A])))
=============================================================================
