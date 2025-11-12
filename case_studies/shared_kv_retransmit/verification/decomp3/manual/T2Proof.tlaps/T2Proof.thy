(* automatically generated -- do not edit manually *)
theory T2Proof imports Constant Zenon begin
ML_command {* writeln ("*** TLAPS PARSED\n"); *}
consts
  "isReal" :: c
  "isa_slas_a" :: "[c,c] => c"
  "isa_bksl_diva" :: "[c,c] => c"
  "isa_perc_a" :: "[c,c] => c"
  "isa_peri_peri_a" :: "[c,c] => c"
  "isInfinity" :: c
  "isa_lbrk_rbrk_a" :: "[c] => c"
  "isa_less_more_a" :: "[c] => c"

lemma ob'91:
fixes Key
fixes Node
fixes Value
fixes Seqnum
fixes unacked unacked'
fixes a_ackunde_msga a_ackunde_msga'
fixes a_rectr1a a_rectr1a'
fixes a_rectr2a a_rectr2a'
(* usable definition vars suppressed *)
(* usable definition Init suppressed *)
(* usable definition retransmit suppressed *)
(* usable definition send_ack suppressed *)
(* usable definition drop_ack_msg suppressed *)
(* usable definition recv_ack_msg suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition IISpec suppressed *)
assumes v'21: "(((((unacked) \<in> ([(Node) \<rightarrow> ([(Node) \<rightarrow> ([(Key) \<rightarrow> ([(Value) \<rightarrow> ([(Seqnum) \<rightarrow> (BOOLEAN)])])])])]))) & (((a_ackunde_msga) \<in> ([(Node) \<rightarrow> ([(Node) \<rightarrow> ([(Seqnum) \<rightarrow> (BOOLEAN)])])]))) & (((a_rectr1a) \<in> ([(Node) \<rightarrow> ([(Node) \<rightarrow> ([(Key) \<rightarrow> ([(Value) \<rightarrow> ([(Seqnum) \<rightarrow> (BOOLEAN)])])])])]))) & (((a_rectr2a) \<in> ([(Node) \<rightarrow> ([(Node) \<rightarrow> ([(Key) \<rightarrow> ([(Value) \<rightarrow> ([(Seqnum) \<rightarrow> (BOOLEAN)])])])])])))) & (\<forall> n \<in> (Node) : (\<forall> m \<in> (Node) : (\<forall> k \<in> (Key) : (\<forall> v \<in> (Value) : (\<forall> s \<in> (Seqnum) : ((~ (fapply ((fapply ((fapply ((fapply ((fapply ((a_rectr2a), (n))), (m))), (k))), (v))), (s)))))))))) & (\<forall> a_N1a \<in> (Node) : (\<forall> a_N2a \<in> (Node) : (\<forall> K \<in> (Key) : (\<forall> V \<in> (Value) : (\<forall> S \<in> (Seqnum) : (((fapply ((fapply ((fapply ((fapply ((fapply ((unacked), (a_N1a))), (a_N2a))), (K))), (V))), (S))) \<Rightarrow> ((~ (fapply ((fapply ((fapply ((fapply ((fapply ((a_rectr1a), (a_N1a))), (a_N2a))), (K))), (V))), (S)))))))))))))"
assumes v'22: "(Next)"
fixes n
assumes n_in : "(n \<in> (Node))"
fixes m
assumes m_in : "(m \<in> (Node))"
fixes k
assumes k_in : "(k \<in> (Key))"
fixes v
assumes v_in : "(v \<in> (Value))"
fixes s
assumes s_in : "(s \<in> (Seqnum))"
fixes a_N1a
assumes a_N1a_in : "(a_N1a \<in> (Node))"
fixes a_N2a
assumes a_N2a_in : "(a_N2a \<in> (Node))"
fixes K
assumes K_in : "(K \<in> (Key))"
fixes V
assumes V_in : "(V \<in> (Value))"
fixes S
assumes S_in : "(S \<in> (Seqnum))"
assumes v'59: "((((a_unackedhash_primea :: c)) = ([(unacked) EXCEPT ![(n)] = ([(fapply ((unacked), (n))) EXCEPT ![(m)] = ([(fapply ((fapply ((unacked), (n))), (m))) EXCEPT ![(k)] = ([(fapply ((fapply ((fapply ((unacked), (n))), (m))), (k))) EXCEPT ![(v)] = ([(fapply ((fapply ((fapply ((fapply ((unacked), (n))), (m))), (k))), (v))) EXCEPT ![(s)] = (TRUE)])])])])])))"
assumes v'60: "((((a_ackunde_msghash_primea :: c)) = (a_ackunde_msga)))"
assumes v'61: "((((a_rectr1hash_primea :: c)) = ([(a_rectr1a) EXCEPT ![(n)] = ([(fapply ((a_rectr1a), (n))) EXCEPT ![(m)] = ([(fapply ((fapply ((a_rectr1a), (n))), (m))) EXCEPT ![(k)] = ([(fapply ((fapply ((fapply ((a_rectr1a), (n))), (m))), (k))) EXCEPT ![(v)] = ([(fapply ((fapply ((fapply ((fapply ((a_rectr1a), (n))), (m))), (k))), (v))) EXCEPT ![(s)] = (FALSE)])])])])])))"
assumes v'62: "((((a_rectr2hash_primea :: c)) = ([(a_rectr2a) EXCEPT ![(n)] = ([(fapply ((a_rectr2a), (n))) EXCEPT ![(m)] = ([(fapply ((fapply ((a_rectr2a), (n))), (m))) EXCEPT ![(k)] = ([(fapply ((fapply ((fapply ((a_rectr2a), (n))), (m))), (k))) EXCEPT ![(v)] = ([(fapply ((fapply ((fapply ((fapply ((a_rectr2a), (n))), (m))), (k))), (v))) EXCEPT ![(s)] = (FALSE)])])])])])))"
assumes v'63: "(fapply ((fapply ((fapply ((fapply ((fapply (((a_unackedhash_primea :: c)), (a_N1a))), (a_N2a))), (K))), (V))), (S)))"
assumes v'64: "(((S) \<noteq> (s)))"
assumes v'65: "(((fapply ((fapply ((fapply ((fapply ((fapply (((a_unackedhash_primea :: c)), (a_N1a))), (a_N2a))), (K))), (V))), (S))) = (fapply ((fapply ((fapply ((fapply ((fapply ((unacked), (a_N1a))), (a_N2a))), (K))), (V))), (S)))))"
assumes v'66: "(((fapply ((fapply ((fapply ((fapply ((fapply (((a_rectr1hash_primea :: c)), (a_N1a))), (a_N2a))), (K))), (V))), (S))) = (fapply ((fapply ((fapply ((fapply ((fapply ((a_rectr1a), (a_N1a))), (a_N2a))), (K))), (V))), (S)))))"
shows "((~ (fapply ((fapply ((fapply ((fapply ((fapply (((a_rectr1hash_primea :: c)), (a_N1a))), (a_N2a))), (K))), (V))), (S)))))"(is "PROP ?ob'91")
proof -
ML_command {* writeln "*** TLAPS ENTER 91"; *}
show "PROP ?ob'91"

(* BEGIN ZENON INPUT
;; file=T2Proof.tlaps/tlapm_dd5919.znn; PATH='/Users/idardik/.opam/homework/bin:/Users/idardik/apalache/bin:/Users/idardik/go/bin:/usr/local/go/bin:~/bin:/Users/idardik/.elan/bin:/opt/homebrew/bin:/opt/homebrew/sbin:/Users/idardik/.gem/ruby/3.1.3/bin:/Users/idardik/.rubies/ruby-3.1.3/lib/ruby/gems/3.1.0/bin:/Users/idardik/.rubies/ruby-3.1.3/bin:/Users/idardik/apalache/bin:/Users/idardik/go/bin:/usr/local/go/bin:~/bin:/Users/idardik/.elan/bin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Library/TeX/texbin:/usr/local/laps:/Applications/CMake.app/Contents/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >T2Proof.tlaps/tlapm_dd5919.znn.out
;; obligation #91
$hyp "v'21" (/\ (/\ (TLA.in unacked
(TLA.FuncSet Node (TLA.FuncSet Node (TLA.FuncSet Key (TLA.FuncSet Value (TLA.FuncSet Seqnum (TLA.set T. F.)))))))
(TLA.in a_ackunde_msga
(TLA.FuncSet Node (TLA.FuncSet Node (TLA.FuncSet Seqnum (TLA.set T. F.)))))
(TLA.in a_rectr1a
(TLA.FuncSet Node (TLA.FuncSet Node (TLA.FuncSet Key (TLA.FuncSet Value (TLA.FuncSet Seqnum (TLA.set T. F.)))))))
(TLA.in a_rectr2a
(TLA.FuncSet Node (TLA.FuncSet Node (TLA.FuncSet Key (TLA.FuncSet Value (TLA.FuncSet Seqnum (TLA.set T. F.))))))))
(TLA.bAll Node ((n) (TLA.bAll Node ((m) (TLA.bAll Key ((k) (TLA.bAll Value ((v) (TLA.bAll Seqnum ((s) (-. (TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply a_rectr2a n) m) k) v) s))))))))))))
(TLA.bAll Node ((a_N1a) (TLA.bAll Node ((a_N2a) (TLA.bAll Key ((K) (TLA.bAll Value ((V) (TLA.bAll Seqnum ((S) (=> (TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply unacked a_N1a) a_N2a) K) V) S)
(-. (TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply a_rectr1a a_N1a) a_N2a) K) V) S))))))))))))))
$hyp "v'22" Next
$hyp "n_in" (TLA.in n Node)
$hyp "m_in" (TLA.in m Node)
$hyp "k_in" (TLA.in k Key)
$hyp "v_in" (TLA.in v Value)
$hyp "s_in" (TLA.in s Seqnum)
$hyp "a_N1a_in" (TLA.in a_N1a Node)
$hyp "a_N2a_in" (TLA.in a_N2a Node)
$hyp "K_in" (TLA.in K Key)
$hyp "V_in" (TLA.in V Value)
$hyp "S_in" (TLA.in S Seqnum)
$hyp "v'59" (= a_unackedhash_primea
(TLA.except unacked n (TLA.except (TLA.fapply unacked n) m (TLA.except (TLA.fapply (TLA.fapply unacked n) m) k (TLA.except (TLA.fapply (TLA.fapply (TLA.fapply unacked n) m) k) v (TLA.except (TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply unacked n) m) k) v) s T.))))))
$hyp "v'60" (= a_ackunde_msghash_primea
a_ackunde_msga)
$hyp "v'61" (= a_rectr1hash_primea
(TLA.except a_rectr1a n (TLA.except (TLA.fapply a_rectr1a n) m (TLA.except (TLA.fapply (TLA.fapply a_rectr1a n) m) k (TLA.except (TLA.fapply (TLA.fapply (TLA.fapply a_rectr1a n) m) k) v (TLA.except (TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply a_rectr1a n) m) k) v) s F.))))))
$hyp "v'62" (= a_rectr2hash_primea
(TLA.except a_rectr2a n (TLA.except (TLA.fapply a_rectr2a n) m (TLA.except (TLA.fapply (TLA.fapply a_rectr2a n) m) k (TLA.except (TLA.fapply (TLA.fapply (TLA.fapply a_rectr2a n) m) k) v (TLA.except (TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply a_rectr2a n) m) k) v) s F.))))))
$hyp "v'63" (TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply a_unackedhash_primea a_N1a) a_N2a) K) V) S)
$hyp "v'64" (-. (= S
s))
$hyp "v'65" (= (TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply a_unackedhash_primea a_N1a) a_N2a) K) V) S)
(TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply unacked a_N1a) a_N2a) K) V) S))
$hyp "v'66" (= (TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply a_rectr1hash_primea a_N1a) a_N2a) K) V) S)
(TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply a_rectr1a a_N1a) a_N2a) K) V) S))
$goal (-. (TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply (TLA.fapply a_rectr1hash_primea a_N1a) a_N2a) K) V) S))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((unacked \\in FuncSet(Node, FuncSet(Node, FuncSet(Key, FuncSet(Value, FuncSet(Seqnum, {TRUE, FALSE}))))))&((a_ackunde_msga \\in FuncSet(Node, FuncSet(Node, FuncSet(Seqnum, {TRUE, FALSE}))))&((a_rectr1a \\in FuncSet(Node, FuncSet(Node, FuncSet(Key, FuncSet(Value, FuncSet(Seqnum, {TRUE, FALSE}))))))&(a_rectr2a \\in FuncSet(Node, FuncSet(Node, FuncSet(Key, FuncSet(Value, FuncSet(Seqnum, {TRUE, FALSE})))))))))&(bAll(Node, (\<lambda>n. bAll(Node, (\<lambda>m. bAll(Key, (\<lambda>k. bAll(Value, (\<lambda>v. bAll(Seqnum, (\<lambda>s. (~(((((a_rectr2a[n])[m])[k])[v])[s]))))))))))))&bAll(Node, (\<lambda>a_N1a. bAll(Node, (\<lambda>a_N2a. bAll(Key, (\<lambda>K. bAll(Value, (\<lambda>V. bAll(Seqnum, (\<lambda>S. ((((((unacked[a_N1a])[a_N2a])[K])[V])[S])=>(~(((((a_rectr1a[a_N1a])[a_N2a])[K])[V])[S])))))))))))))))" (is "?z_hv&?z_hbu")
 using v'21 by blast
 have z_Ho:"(a_rectr1hash_primea=except(a_rectr1a, n, except((a_rectr1a[n]), m, except(((a_rectr1a[n])[m]), k, except((((a_rectr1a[n])[m])[k]), v, except(((((a_rectr1a[n])[m])[k])[v]), s, FALSE))))))" (is "_=?z_hds")
 using v'61 by blast
 have z_Hm:"(a_unackedhash_primea=except(unacked, n, except((unacked[n]), m, except(((unacked[n])[m]), k, except((((unacked[n])[m])[k]), v, except(((((unacked[n])[m])[k])[v]), s, TRUE))))))" (is "_=?z_hec")
 using v'59 by blast
 have z_Hq:"(((((a_unackedhash_primea[a_N1a])[a_N2a])[K])[V])[S])" (is "?z_hq")
 using v'63 by blast
 have z_Ht:"((((((a_rectr1hash_primea[a_N1a])[a_N2a])[K])[V])[S])=(((((a_rectr1a[a_N1a])[a_N2a])[K])[V])[S]))" (is "?z_hep=?z_hdm")
 using v'66 by blast
 have z_Hj:"(K \\in Key)" (is "?z_hj")
 using K_in by blast
 have z_Hl:"(S \\in Seqnum)" (is "?z_hl")
 using S_in by blast
 have z_Hk:"(V \\in Value)" (is "?z_hk")
 using V_in by blast
 have z_Hi:"(a_N2a \\in Node)" (is "?z_hi")
 using a_N2a_in by blast
 have z_Hh:"(a_N1a \\in Node)" (is "?z_hh")
 using a_N1a_in by blast
 have z_Hs:"(?z_hq=(((((unacked[a_N1a])[a_N2a])[K])[V])[S]))" (is "_=?z_hdb")
 using v'65 by blast
 assume z_Hu:"(~(~?z_hep))"
 have z_Hbu: "?z_hbu" (is "?z_hbv&?z_hcq")
 by (rule zenon_and_1 [OF z_Ha])
 have z_Hcq: "?z_hcq"
 by (rule zenon_and_1 [OF z_Hbu])
 have z_Hep: "?z_hep"
 by (rule zenon_notnot_0 [OF z_Hu])
 have z_Hev: "(((((?z_hds[a_N1a])[a_N2a])[K])[V])[S])" (is "?z_hev")
 by (rule subst [where P="(\<lambda>zenon_Vaec. (((((zenon_Vaec[a_N1a])[a_N2a])[K])[V])[S]))", OF z_Ho z_Hep])
 have z_Hfh: "(((((?z_hec[a_N1a])[a_N2a])[K])[V])[S])" (is "?z_hfh")
 by (rule subst [where P="(\<lambda>zenon_Vaec. (((((zenon_Vaec[a_N1a])[a_N2a])[K])[V])[S]))", OF z_Hm z_Hq])
 have z_Hfm: "(?z_hfh=?z_hdb)"
 by (rule subst [where P="(\<lambda>zenon_Veec. ((((((zenon_Veec[a_N1a])[a_N2a])[K])[V])[S])=?z_hdb))", OF z_Hm z_Hs])
 have z_Hfv: "(TRUE=?z_hdb)" (is "?z_hbi=_")
 by (rule zenon_trueistrue_0 [of "(\<lambda>zenon_Vh. (zenon_Vh=?z_hdb))" "?z_hfh", OF z_Hfm z_Hfh])
 have z_Hdb: "?z_hdb"
 by (rule zenon_eq_true_x_0 [of "?z_hdb", OF z_Hfv])
 have z_Hfz: "(?z_hev=?z_hdm)"
 by (rule subst [where P="(\<lambda>zenon_Vgec. ((((((zenon_Vgec[a_N1a])[a_N2a])[K])[V])[S])=?z_hdm))", OF z_Ho z_Ht])
 have z_Hgi: "(?z_hbi=?z_hdm)"
 by (rule zenon_trueistrue_0 [of "(\<lambda>zenon_Vg. (zenon_Vg=?z_hdm))" "?z_hev", OF z_Hfz z_Hev])
 have z_Hdm: "?z_hdm"
 by (rule zenon_eq_true_x_0 [of "?z_hdm", OF z_Hgi])
 have z_Hcs: "bAll(Node, (\<lambda>a_N2a. bAll(Key, (\<lambda>K. bAll(Value, (\<lambda>V. bAll(Seqnum, (\<lambda>S. ((((((unacked[a_N1a])[a_N2a])[K])[V])[S])=>(~(((((a_rectr1a[a_N1a])[a_N2a])[K])[V])[S])))))))))))" (is "?z_hcs")
 by (rule zenon_all_in_0 [of "Node" "(\<lambda>a_N1a. bAll(Node, (\<lambda>a_N2a. bAll(Key, (\<lambda>K. bAll(Value, (\<lambda>V. bAll(Seqnum, (\<lambda>S. ((((((unacked[a_N1a])[a_N2a])[K])[V])[S])=>(~(((((a_rectr1a[a_N1a])[a_N2a])[K])[V])[S]))))))))))))", OF z_Hcq z_Hh])
 have z_Hgm_z_Hcs: "(\\A x:((x \\in Node)=>bAll(Key, (\<lambda>K. bAll(Value, (\<lambda>V. bAll(Seqnum, (\<lambda>S. ((((((unacked[a_N1a])[x])[K])[V])[S])=>(~(((((a_rectr1a[a_N1a])[x])[K])[V])[S]))))))))))) == ?z_hcs" (is "?z_hgm == _")
 by (unfold bAll_def)
 have z_Hgm: "?z_hgm" (is "\\A x : ?z_hhg(x)")
 by (unfold z_Hgm_z_Hcs, fact z_Hcs)
 have z_Hhh: "?z_hhg(a_N2a)" (is "_=>?z_hcu")
 by (rule zenon_all_0 [of "?z_hhg" "a_N2a", OF z_Hgm])
 show FALSE
 proof (rule zenon_imply [OF z_Hhh])
  assume z_Hhi:"(~?z_hi)"
  show FALSE
  by (rule notE [OF z_Hhi z_Hi])
 next
  assume z_Hcu:"?z_hcu"
  have z_Hhj_z_Hcu: "(\\A x:((x \\in Key)=>bAll(Value, (\<lambda>V. bAll(Seqnum, (\<lambda>S. ((((((unacked[a_N1a])[a_N2a])[x])[V])[S])=>(~(((((a_rectr1a[a_N1a])[a_N2a])[x])[V])[S]))))))))) == ?z_hcu" (is "?z_hhj == _")
  by (unfold bAll_def)
  have z_Hhj: "?z_hhj" (is "\\A x : ?z_hhy(x)")
  by (unfold z_Hhj_z_Hcu, fact z_Hcu)
  have z_Hhz: "?z_hhy(K)" (is "_=>?z_hcw")
  by (rule zenon_all_0 [of "?z_hhy" "K", OF z_Hhj])
  show FALSE
  proof (rule zenon_imply [OF z_Hhz])
   assume z_Hia:"(~?z_hj)"
   show FALSE
   by (rule notE [OF z_Hia z_Hj])
  next
   assume z_Hcw:"?z_hcw"
   have z_Hib_z_Hcw: "(\\A x:((x \\in Value)=>bAll(Seqnum, (\<lambda>S. ((((((unacked[a_N1a])[a_N2a])[K])[x])[S])=>(~(((((a_rectr1a[a_N1a])[a_N2a])[K])[x])[S]))))))) == ?z_hcw" (is "?z_hib == _")
   by (unfold bAll_def)
   have z_Hib: "?z_hib" (is "\\A x : ?z_him(x)")
   by (unfold z_Hib_z_Hcw, fact z_Hcw)
   have z_Hin: "?z_him(V)" (is "_=>?z_hcy")
   by (rule zenon_all_0 [of "?z_him" "V", OF z_Hib])
   show FALSE
   proof (rule zenon_imply [OF z_Hin])
    assume z_Hio:"(~?z_hk)"
    show FALSE
    by (rule notE [OF z_Hio z_Hk])
   next
    assume z_Hcy:"?z_hcy"
    have z_Hip_z_Hcy: "(\\A x:((x \\in Seqnum)=>((((((unacked[a_N1a])[a_N2a])[K])[V])[x])=>(~(((((a_rectr1a[a_N1a])[a_N2a])[K])[V])[x]))))) == ?z_hcy" (is "?z_hip == _")
    by (unfold bAll_def)
    have z_Hip: "?z_hip" (is "\\A x : ?z_hiw(x)")
    by (unfold z_Hip_z_Hcy, fact z_Hcy)
    have z_Hix: "?z_hiw(S)" (is "_=>?z_hda")
    by (rule zenon_all_0 [of "?z_hiw" "S", OF z_Hip])
    show FALSE
    proof (rule zenon_imply [OF z_Hix])
     assume z_Hiy:"(~?z_hl)"
     show FALSE
     by (rule notE [OF z_Hiy z_Hl])
    next
     assume z_Hda:"?z_hda" (is "_=>?z_hdl")
     show FALSE
     proof (rule zenon_imply [OF z_Hda])
      assume z_Hiz:"(~?z_hdb)"
      show FALSE
      by (rule notE [OF z_Hiz z_Hdb])
     next
      assume z_Hdl:"?z_hdl"
      show FALSE
      by (rule notE [OF z_Hdl z_Hdm])
     qed
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 91"; *} qed
lemma ob'103:
fixes Key
fixes Node
fixes Value
fixes Seqnum
fixes unacked unacked'
fixes a_ackunde_msga a_ackunde_msga'
fixes a_rectr1a a_rectr1a'
fixes a_rectr2a a_rectr2a'
(* usable definition vars suppressed *)
(* usable definition Safety suppressed *)
(* usable definition Init suppressed *)
(* usable definition retransmit suppressed *)
(* usable definition send_ack suppressed *)
(* usable definition drop_ack_msg suppressed *)
(* usable definition recv_ack_msg suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Inv1 suppressed *)
(* usable definition IISpec suppressed *)
assumes v'23: "(((((unacked) \<in> ([(Node) \<rightarrow> ([(Node) \<rightarrow> ([(Key) \<rightarrow> ([(Value) \<rightarrow> ([(Seqnum) \<rightarrow> (BOOLEAN)])])])])]))) & (((a_ackunde_msga) \<in> ([(Node) \<rightarrow> ([(Node) \<rightarrow> ([(Seqnum) \<rightarrow> (BOOLEAN)])])]))) & (((a_rectr1a) \<in> ([(Node) \<rightarrow> ([(Node) \<rightarrow> ([(Key) \<rightarrow> ([(Value) \<rightarrow> ([(Seqnum) \<rightarrow> (BOOLEAN)])])])])]))) & (((a_rectr2a) \<in> ([(Node) \<rightarrow> ([(Node) \<rightarrow> ([(Key) \<rightarrow> ([(Value) \<rightarrow> ([(Seqnum) \<rightarrow> (BOOLEAN)])])])])])))) & (Safety) & (a_Inv1a))"
assumes v'24: "(Next)"
fixes n
assumes n_in : "(n \<in> (Node))"
fixes m
assumes m_in : "(m \<in> (Node))"
fixes k
assumes k_in : "(k \<in> (Key))"
fixes v
assumes v_in : "(v \<in> (Value))"
fixes s
assumes s_in : "(s \<in> (Seqnum))"
fixes a_N1a
assumes a_N1a_in : "(a_N1a \<in> (Node))"
fixes a_N2a
assumes a_N2a_in : "(a_N2a \<in> (Node))"
fixes K
assumes K_in : "(K \<in> (Key))"
fixes V
assumes V_in : "(V \<in> (Value))"
fixes S
assumes S_in : "(S \<in> (Seqnum))"
assumes v'62: "(((((a_unackedhash_primea :: c)) \<in> ([(Node) \<rightarrow> ([(Node) \<rightarrow> ([(Key) \<rightarrow> ([(Value) \<rightarrow> ([(Seqnum) \<rightarrow> (BOOLEAN)])])])])]))) & ((((a_ackunde_msghash_primea :: c)) \<in> ([(Node) \<rightarrow> ([(Node) \<rightarrow> ([(Seqnum) \<rightarrow> (BOOLEAN)])])]))) & ((((a_rectr1hash_primea :: c)) \<in> ([(Node) \<rightarrow> ([(Node) \<rightarrow> ([(Key) \<rightarrow> ([(Value) \<rightarrow> ([(Seqnum) \<rightarrow> (BOOLEAN)])])])])]))) & ((((a_rectr2hash_primea :: c)) \<in> ([(Node) \<rightarrow> ([(Node) \<rightarrow> ([(Key) \<rightarrow> ([(Value) \<rightarrow> ([(Seqnum) \<rightarrow> (BOOLEAN)])])])])]))))"
assumes v'63: "((((a_unackedhash_primea :: c)) = ([(unacked) EXCEPT ![(n)] = ([(fapply ((unacked), (n))) EXCEPT ![(m)] = ([(fapply ((fapply ((unacked), (n))), (m))) EXCEPT ![(k)] = ([(fapply ((fapply ((fapply ((unacked), (n))), (m))), (k))) EXCEPT ![(v)] = ([(fapply ((fapply ((fapply ((fapply ((unacked), (n))), (m))), (k))), (v))) EXCEPT ![(s)] = (TRUE)])])])])])))"
assumes v'64: "((((a_ackunde_msghash_primea :: c)) = (a_ackunde_msga)))"
assumes v'65: "((((a_rectr1hash_primea :: c)) = ([(a_rectr1a) EXCEPT ![(n)] = ([(fapply ((a_rectr1a), (n))) EXCEPT ![(m)] = ([(fapply ((fapply ((a_rectr1a), (n))), (m))) EXCEPT ![(k)] = ([(fapply ((fapply ((fapply ((a_rectr1a), (n))), (m))), (k))) EXCEPT ![(v)] = ([(fapply ((fapply ((fapply ((fapply ((a_rectr1a), (n))), (m))), (k))), (v))) EXCEPT ![(s)] = (FALSE)])])])])])))"
assumes v'66: "((((a_rectr2hash_primea :: c)) = ([(a_rectr2a) EXCEPT ![(n)] = ([(fapply ((a_rectr2a), (n))) EXCEPT ![(m)] = ([(fapply ((fapply ((a_rectr2a), (n))), (m))) EXCEPT ![(k)] = ([(fapply ((fapply ((fapply ((a_rectr2a), (n))), (m))), (k))) EXCEPT ![(v)] = ([(fapply ((fapply ((fapply ((fapply ((a_rectr2a), (n))), (m))), (k))), (v))) EXCEPT ![(s)] = (FALSE)])])])])])))"
assumes v'67: "(fapply ((fapply ((fapply ((fapply ((fapply (((a_unackedhash_primea :: c)), (a_N1a))), (a_N2a))), (K))), (V))), (S)))"
assumes v'68: "(((S) \<noteq> (s)))"
assumes v'69: "((\<And> a_N1a_1 :: c. a_N1a_1 \<in> (Node) \<Longrightarrow> (\<And> a_N2a_1 :: c. a_N2a_1 \<in> (Node) \<Longrightarrow> (\<And> K_1 :: c. K_1 \<in> (Key) \<Longrightarrow> (\<And> V_1 :: c. V_1 \<in> (Value) \<Longrightarrow> (\<And> S_1 :: c. S_1 \<in> (Seqnum) \<Longrightarrow> (\<And> a_n1a :: c. a_n1a \<in> (Node) \<Longrightarrow> (\<And> a_n2a :: c. a_n2a \<in> (Node) \<Longrightarrow> (\<And> k_1 :: c. k_1 \<in> (Key) \<Longrightarrow> (\<And> v_1 :: c. v_1 \<in> (Value) \<Longrightarrow> (\<And> s_1 :: c. s_1 \<in> (Seqnum) \<Longrightarrow> (((((a_rectr1hash_primea :: c)) = ([(a_rectr1a) EXCEPT ![(a_n1a)] = ([(fapply ((a_rectr1a), (a_n1a))) EXCEPT ![(a_n2a)] = ([(fapply ((fapply ((a_rectr1a), (a_n1a))), (a_n2a))) EXCEPT ![(k_1)] = ([(fapply ((fapply ((fapply ((a_rectr1a), (a_n1a))), (a_n2a))), (k_1))) EXCEPT ![(v_1)] = ([(fapply ((fapply ((fapply ((fapply ((a_rectr1a), (a_n1a))), (a_n2a))), (k_1))), (v_1))) EXCEPT ![(s_1)] = (FALSE)])])])])]))) \<Longrightarrow> ((((S_1) \<noteq> (s_1))) \<Longrightarrow> (((fapply ((fapply ((fapply ((fapply ((fapply (((a_rectr1hash_primea :: c)), (a_N1a_1))), (a_N2a_1))), (K_1))), (V_1))), (S_1))) = (fapply ((fapply ((fapply ((fapply ((fapply ((a_rectr1a), (a_N1a_1))), (a_N2a_1))), (K_1))), (V_1))), (S_1))))))))))))))))))"
shows "(((fapply ((fapply ((fapply ((fapply ((fapply (((a_rectr1hash_primea :: c)), (a_N1a))), (a_N2a))), (K))), (V))), (S))) = (fapply ((fapply ((fapply ((fapply ((fapply ((a_rectr1a), (a_N1a))), (a_N2a))), (K))), (V))), (S)))))"(is "PROP ?ob'103")
proof -
ML_command {* writeln "*** TLAPS ENTER 103"; *}
show "PROP ?ob'103"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 103"; *} qed
lemma ob'97:
fixes Key
fixes Node
fixes Value
fixes Seqnum
fixes unacked unacked'
fixes a_ackunde_msga a_ackunde_msga'
fixes a_rectr1a a_rectr1a'
fixes a_rectr2a a_rectr2a'
(* usable definition vars suppressed *)
(* usable definition Safety suppressed *)
(* usable definition Init suppressed *)
(* usable definition retransmit suppressed *)
(* usable definition send_ack suppressed *)
(* usable definition drop_ack_msg suppressed *)
(* usable definition recv_ack_msg suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Inv1 suppressed *)
(* usable definition IISpec suppressed *)
assumes v'23: "(((((unacked) \<in> ([(Node) \<rightarrow> ([(Node) \<rightarrow> ([(Key) \<rightarrow> ([(Value) \<rightarrow> ([(Seqnum) \<rightarrow> (BOOLEAN)])])])])]))) & (((a_ackunde_msga) \<in> ([(Node) \<rightarrow> ([(Node) \<rightarrow> ([(Seqnum) \<rightarrow> (BOOLEAN)])])]))) & (((a_rectr1a) \<in> ([(Node) \<rightarrow> ([(Node) \<rightarrow> ([(Key) \<rightarrow> ([(Value) \<rightarrow> ([(Seqnum) \<rightarrow> (BOOLEAN)])])])])]))) & (((a_rectr2a) \<in> ([(Node) \<rightarrow> ([(Node) \<rightarrow> ([(Key) \<rightarrow> ([(Value) \<rightarrow> ([(Seqnum) \<rightarrow> (BOOLEAN)])])])])])))) & (Safety) & (a_Inv1a))"
assumes v'24: "(Next)"
fixes n
assumes n_in : "(n \<in> (Node))"
fixes m
assumes m_in : "(m \<in> (Node))"
fixes k
assumes k_in : "(k \<in> (Key))"
fixes v
assumes v_in : "(v \<in> (Value))"
fixes s
assumes s_in : "(s \<in> (Seqnum))"
fixes a_N1a
assumes a_N1a_in : "(a_N1a \<in> (Node))"
fixes a_N2a
assumes a_N2a_in : "(a_N2a \<in> (Node))"
fixes K
assumes K_in : "(K \<in> (Key))"
fixes V
assumes V_in : "(V \<in> (Value))"
fixes S
assumes S_in : "(S \<in> (Seqnum))"
assumes v'61: "(((((a_unackedhash_primea :: c)) \<in> ([(Node) \<rightarrow> ([(Node) \<rightarrow> ([(Key) \<rightarrow> ([(Value) \<rightarrow> ([(Seqnum) \<rightarrow> (BOOLEAN)])])])])]))) & ((((a_ackunde_msghash_primea :: c)) \<in> ([(Node) \<rightarrow> ([(Node) \<rightarrow> ([(Seqnum) \<rightarrow> (BOOLEAN)])])]))) & ((((a_rectr1hash_primea :: c)) \<in> ([(Node) \<rightarrow> ([(Node) \<rightarrow> ([(Key) \<rightarrow> ([(Value) \<rightarrow> ([(Seqnum) \<rightarrow> (BOOLEAN)])])])])]))) & ((((a_rectr2hash_primea :: c)) \<in> ([(Node) \<rightarrow> ([(Node) \<rightarrow> ([(Key) \<rightarrow> ([(Value) \<rightarrow> ([(Seqnum) \<rightarrow> (BOOLEAN)])])])])]))))"
assumes v'62: "((((a_unackedhash_primea :: c)) = ([(unacked) EXCEPT ![(n)] = ([(fapply ((unacked), (n))) EXCEPT ![(m)] = ([(fapply ((fapply ((unacked), (n))), (m))) EXCEPT ![(k)] = ([(fapply ((fapply ((fapply ((unacked), (n))), (m))), (k))) EXCEPT ![(v)] = ([(fapply ((fapply ((fapply ((fapply ((unacked), (n))), (m))), (k))), (v))) EXCEPT ![(s)] = (TRUE)])])])])])))"
assumes v'63: "((((a_ackunde_msghash_primea :: c)) = (a_ackunde_msga)))"
assumes v'64: "((((a_rectr1hash_primea :: c)) = ([(a_rectr1a) EXCEPT ![(n)] = ([(fapply ((a_rectr1a), (n))) EXCEPT ![(m)] = ([(fapply ((fapply ((a_rectr1a), (n))), (m))) EXCEPT ![(k)] = ([(fapply ((fapply ((fapply ((a_rectr1a), (n))), (m))), (k))) EXCEPT ![(v)] = ([(fapply ((fapply ((fapply ((fapply ((a_rectr1a), (n))), (m))), (k))), (v))) EXCEPT ![(s)] = (FALSE)])])])])])))"
assumes v'65: "((((a_rectr2hash_primea :: c)) = ([(a_rectr2a) EXCEPT ![(n)] = ([(fapply ((a_rectr2a), (n))) EXCEPT ![(m)] = ([(fapply ((fapply ((a_rectr2a), (n))), (m))) EXCEPT ![(k)] = ([(fapply ((fapply ((fapply ((a_rectr2a), (n))), (m))), (k))) EXCEPT ![(v)] = ([(fapply ((fapply ((fapply ((fapply ((a_rectr2a), (n))), (m))), (k))), (v))) EXCEPT ![(s)] = (FALSE)])])])])])))"
assumes v'66: "(fapply ((fapply ((fapply ((fapply ((fapply (((a_unackedhash_primea :: c)), (a_N1a))), (a_N2a))), (K))), (V))), (S)))"
assumes v'67: "(((S) \<noteq> (s)))"
assumes v'68: "((\<And> a_N1a_1 :: c. a_N1a_1 \<in> (Node) \<Longrightarrow> (\<And> a_N2a_1 :: c. a_N2a_1 \<in> (Node) \<Longrightarrow> (\<And> K_1 :: c. K_1 \<in> (Key) \<Longrightarrow> (\<And> V_1 :: c. V_1 \<in> (Value) \<Longrightarrow> (\<And> S_1 :: c. S_1 \<in> (Seqnum) \<Longrightarrow> (\<And> a_n1a :: c. a_n1a \<in> (Node) \<Longrightarrow> (\<And> a_n2a :: c. a_n2a \<in> (Node) \<Longrightarrow> (\<And> k_1 :: c. k_1 \<in> (Key) \<Longrightarrow> (\<And> v_1 :: c. v_1 \<in> (Value) \<Longrightarrow> (\<And> s_1 :: c. s_1 \<in> (Seqnum) \<Longrightarrow> (((((a_unackedhash_primea :: c)) = ([(unacked) EXCEPT ![(a_n1a)] = ([(fapply ((unacked), (a_n1a))) EXCEPT ![(a_n2a)] = ([(fapply ((fapply ((unacked), (a_n1a))), (a_n2a))) EXCEPT ![(k_1)] = ([(fapply ((fapply ((fapply ((unacked), (a_n1a))), (a_n2a))), (k_1))) EXCEPT ![(v_1)] = ([(fapply ((fapply ((fapply ((fapply ((unacked), (a_n1a))), (a_n2a))), (k_1))), (v_1))) EXCEPT ![(s_1)] = (TRUE)])])])])]))) \<Longrightarrow> ((((S_1) \<noteq> (s_1))) \<Longrightarrow> (((fapply ((fapply ((fapply ((fapply ((fapply (((a_unackedhash_primea :: c)), (a_N1a_1))), (a_N2a_1))), (K_1))), (V_1))), (S_1))) = (fapply ((fapply ((fapply ((fapply ((fapply ((unacked), (a_N1a_1))), (a_N2a_1))), (K_1))), (V_1))), (S_1))))))))))))))))))"
shows "(((fapply ((fapply ((fapply ((fapply ((fapply (((a_unackedhash_primea :: c)), (a_N1a))), (a_N2a))), (K))), (V))), (S))) = (fapply ((fapply ((fapply ((fapply ((fapply ((unacked), (a_N1a))), (a_N2a))), (K))), (V))), (S)))))"(is "PROP ?ob'97")
proof -
ML_command {* writeln "*** TLAPS ENTER 97"; *}
show "PROP ?ob'97"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 97"; *} qed
end
