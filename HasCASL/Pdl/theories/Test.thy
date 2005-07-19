theory Test = Parsec + State:

(* shows how to prove implications without implicit use of impI in a proof
statement *)
lemma "A \<longrightarrow> A" proof -
  { assume "A"
    have "A" .
  }
  thus ?thesis by (rule impI)
qed



lemma "A \<longrightarrow> A"
proof -
  have "A \<Longrightarrow> A"
  proof -
    assume "A"
    show "A" .
  qed
  thus ?thesis by (rule impI) 
qed


lemma "(A \<longrightarrow> B) \<longrightarrow> (C \<or> A \<longrightarrow> B \<or> C)"
  by blast

(* Contraposition is intuitionistic in two cases: *)

lemma "\<lbrakk> ~Q; P \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> ~P"
  apply(rule notI)
  apply(rule notE)
  apply(assumption)
  apply(rules)
done

lemma "\<lbrakk> Q; P \<Longrightarrow> ~Q\<rbrakk> \<Longrightarrow> ~P"
  apply(rule notI)
  apply(rule notE)
  
  apply(rules)+
done

lemma "\<lbrakk> ~Q; ~P \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> P"
  oops


lemma "\<not>(P \<or> Q) \<Longrightarrow> \<not>P \<and> \<not>Q"
  apply(rule conjI)
  oops



constdefs
  xor :: "[bool, bool] \<Rightarrow> bool"        (infixr "\<oplus>" 20)
  "P \<oplus> Q \<equiv>  (P \<and> \<not> Q) \<or> (\<not> P \<and> Q)"



lemma "(P \<oplus> True) = (\<not> P)" 
  apply (unfold xor_def)
  by blast



lemma and_comm: "(A \<and> B) = (B \<and> A)" by blast
lemma and_assoc: "((A \<and> B) \<and> C) = (A \<and> (B \<and> C))" by blast
lemma and_LC:   "(A \<and> (B \<and> C)) = (B \<and> (A \<and> C))" by blast


lemma xor_comm: "(A \<oplus> B) = (B \<oplus> A)" by (unfold xor_def, blast)
lemma xor_assoc: "((A \<oplus> B) \<oplus> C) = (A \<oplus> (B \<oplus> C))" by (unfold xor_def, blast)
lemma xor_LC:    "(A \<oplus> (B \<oplus> C)) = (B \<oplus> (A \<oplus> C))" by (unfold xor_def, blast)

lemma and_True: "(A \<and> True) = A"  by blast
lemma and_False: "(A \<and> False) = False" by blast
lemma and_absorb: "(A \<and> A) = A" by blast
lemma xor_False: "(A \<oplus> False) = A" by (unfold xor_def, blast)
lemma xor_contr: "(A \<oplus> A) = False" by (unfold xor_def, blast)
lemma and_xor_rdistrib: "((A \<oplus> B) \<and> C) = ((A \<and> C) \<oplus> (B \<and> C))" by (unfold xor_def, blast)
lemma and_xor_ldistrib: "(C \<and> (A \<oplus> B)) = ((C \<and> A) \<oplus> (C \<and> B))" by (unfold xor_def, blast)

lemma imp_as_xor: "(A \<longrightarrow> B) = (A \<and> B \<oplus> A \<oplus> True)"
  by (unfold xor_def, blast)
lemma or_as_xor: "(A \<or> B) = (A \<oplus> B \<oplus> A \<and> B)"
  by (unfold xor_def, blast)
lemma not_as_xor: "(\<not> A) = (A \<oplus> True)" by (unfold xor_def, blast)
lemma iff_as_xor: "(A = B) = (A \<oplus> B \<oplus> True)"  by (unfold xor_def, blast)


lemma aux1: "(A \<and> (A \<and> B)) = (A \<and> B)" by blast
lemma aux2: "(True \<and> A) = A" by blast
lemma aux3: "(False \<and> A) = False" by blast
lemma aux4: "(False \<oplus> A) = A" by (unfold xor_def, blast)
lemma aux5: "(A \<oplus> (A \<oplus> B)) = B" by (unfold xor_def, blast)

lemmas prop_taut = and_comm and_assoc and_LC xor_comm xor_assoc xor_LC and_True
                   and_False and_absorb xor_False xor_contr 
                   and_xor_ldistrib and_xor_rdistrib
                   imp_as_xor or_as_xor not_as_xor iff_as_xor
                   aux1 aux2 aux3 aux4 aux5


lemma "(p \<and> q \<longrightarrow> r) = (p \<longrightarrow> q \<longrightarrow> r)"
  apply (simp only: prop_taut)
done

lemma "A --> B --> A"
  apply (simp only: prop_taut)
done

lemma "(C \<and> D \<or> E \<and> \<not>C) \<longrightarrow> A \<longrightarrow> (C \<and> D \<or> E \<and> \<not>C)"
  apply (simp only: prop_taut)
done

lemma "A \<and> B \<longrightarrow> A" 
  apply (simp only: prop_taut)
done

lemma "A \<or> B \<longrightarrow> B \<or> A \<or> C" by (simp only: prop_taut)


lemma "A \<or> B \<longrightarrow> (A \<longrightarrow> C) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> C" by (simp only: prop_taut)


lemma "p = p" by (simp only: prop_taut)

lemma "(p \<and> q) = (p \<and> (q \<or> \<not> p))" by (simp only: prop_taut)


lemma "((p \<longrightarrow> q) \<and> (\<not> p \<longrightarrow> r)) = ((p \<and> q) \<or> (\<not>p \<and> r))" 
by (simp only: prop_taut)


lemma "(p = q) = ((p \<and> q) \<or> (\<not>p \<and> \<not>q))" by (simp only: prop_taut)




subsection {* Table of rules *}

text {* 
\begin{tabular}{lp{0.7\textwidth}}
@{thm [source] mon_ctr} &  @{thm mon_ctr[no_vars]}\\\hline
\end{tabular}

\begin{tabular}{lp{0.7\textwidth}}
@{thm [source] dsef_cp} &  @{thm dsef_cp[no_vars]}\\\hline
@{thm [source] dsef_dis} &  @{thm dsef_dis[no_vars]}\\\hline
@{thm [source] dis_left} &  @{thm dis_left[no_vars]}\\\hline
@{thm [source] dis_left2} &  @{thm dis_left2[no_vars]}\\\hline
@{thm [source] cp_arb} &  @{thm cp_arb[no_vars]}\\\hline
@{thm [source] weak_cp_seq} &  @{thm weak_cp_seq[no_vars]}\\\hline
@{thm [source] cp_seq_ret} &  @{thm cp_seq_ret[no_vars]}\\\hline
@{thm [source] weak_dis_seq} &  @{thm weak_dis_seq[no_vars]}\\\hline
@{thm [source] commute_1_2} &  @{thm commute_1_2[no_vars]}\\\hline
@{thm [source] commute_2_3} &  @{thm commute_2_3[no_vars]}\\\hline
@{thm [source] commute_3_1} &  @{thm commute_3_1[no_vars]}\\\hline
@{thm [source] commute_1_3} &  @{thm commute_1_3[no_vars]}\\\hline
@{thm [source] dis_Rep_Dsef} &  @{thm dis_Rep_Dsef[no_vars]}\\\hline
@{thm [source] cp_Rep_Dsef} &  @{thm cp_Rep_Dsef[no_vars]}\\\hline
@{thm [source] Ret_ret} &  @{thm Ret_ret[no_vars]}\\\hline
@{thm [source] liftM_ap} &  @{thm liftM_ap[no_vars]}\\\hline
@{thm [source] liftM2_ap} &  @{thm liftM2_ap[no_vars]}\\\hline
@{thm [source] liftM3_ap} &  @{thm liftM3_ap[no_vars]}\\\hline
@{thm [source] dsef_ret_ap} &  @{thm dsef_ret_ap[no_vars]}\\\hline
@{thm [source] commute_dsef} &  @{thm commute_dsef[no_vars]}\\\hline
@{thm [source] commute_bool} &  @{thm commute_bool[no_vars]}\\\hline
@{thm [source] dsef_seq} &  @{thm dsef_seq[no_vars]}\\\hline
@{thm [source] weak_dsef_seq} &  @{thm weak_dsef_seq[no_vars]}\\\hline
@{thm [source] dsef_liftM2} &  @{thm dsef_liftM2[no_vars]}\\\hline
\end{tabular}

\begin{tabular}{lp{0.7\textwidth}}
@{thm [source] Valid_simp} &  @{thm Valid_simp[no_vars]}\\\hline
@{thm [source] lift_Ret_hom} &  @{thm lift_Ret_hom[no_vars]}\\\hline
@{thm [source] conjD_Ret_hom} &  @{thm conjD_Ret_hom[no_vars]}\\\hline
@{thm [source] disjD_Ret_hom} &  @{thm disjD_Ret_hom[no_vars]}\\\hline
@{thm [source] impD_Ret_hom} &  @{thm impD_Ret_hom[no_vars]}\\\hline
@{thm [source] NotD_Ret_hom} &  @{thm NotD_Ret_hom[no_vars]}\\\hline
@{thm [source] dsef_form} &  @{thm dsef_form[no_vars]}\\\hline
@{thm [source] Valid_not_eq_ret_False} &  @{thm Valid_not_eq_ret_False[no_vars]}\\\hline
@{thm [source] pdl_excluded_middle} &  @{thm pdl_excluded_middle[no_vars]}\\\hline
@{thm [source] pdl_mp} &  @{thm pdl_mp[no_vars]}\\\hline
@{thm [source] pdl_disjI1} &  @{thm pdl_disjI1[no_vars]}\\\hline
@{thm [source] pdl_disjI2} &  @{thm pdl_disjI2[no_vars]}\\\hline
@{thm [source] pdl_disjE} &  @{thm pdl_disjE[no_vars]}\\\hline
@{thm [source] pdl_conjI} &  @{thm pdl_conjI[no_vars]}\\\hline
@{thm [source] pdl_FalseE} &  @{thm pdl_FalseE[no_vars]}\\\hline
@{thm [source] pdl_notE} &  @{thm pdl_notE[no_vars]}\\\hline
@{thm [source] pdl_conjE} &  @{thm pdl_conjE[no_vars]}\\\hline
@{thm [source] pdl_notI} &  @{thm pdl_notI[no_vars]}\\\hline
@{thm [source] pdl_conjunct1} &  @{thm pdl_conjunct1[no_vars]}\\\hline
@{thm [source] pdl_conjunct2} &  @{thm pdl_conjunct2[no_vars]}\\\hline
@{thm [source] pdl_iffI} &  @{thm pdl_iffI[no_vars]}\\\hline
@{thm [source] pdl_iffE} &  @{thm pdl_iffE[no_vars]}\\\hline
@{thm [source] pdl_sym} &  @{thm pdl_sym[no_vars]}\\\hline
@{thm [source] pdl_iffD1} &  @{thm pdl_iffD1[no_vars]}\\\hline
@{thm [source] pdl_iffD2} &  @{thm pdl_iffD2[no_vars]}\\\hline
@{thm [source] pdl_conjI_lifted} &  @{thm pdl_conjI_lifted[no_vars]}\\\hline
@{thm [source] pdl_eq_iff} &  @{thm pdl_eq_iff[no_vars]}\\\hline
@{thm [source] pdl_iff_sym} &  @{thm pdl_iff_sym[no_vars]}\\\hline
@{thm [source] pdl_imp_wk} &  @{thm pdl_imp_wk[no_vars]}\\\hline
@{thm [source] pdl_False_imp} &  @{thm pdl_False_imp[no_vars]}\\\hline
@{thm [source] pdl_imp_trans} &  @{thm pdl_imp_trans[no_vars]}\\\hline
\end{tabular}

\begin{tabular}{lp{0.7\textwidth}}
@{thm [source] dmd_box_rel} &  @{thm dmd_box_rel[no_vars]}\\\hline
@{thm [source] box_dmd_rel} &  @{thm box_dmd_rel[no_vars]}\\\hline
@{thm [source] pdl_eqB_ext} &  @{thm pdl_eqB_ext[no_vars]}\\\hline
@{thm [source] box_imp_distrib} &  @{thm box_imp_distrib[no_vars]}\\\hline
@{thm [source] dmd_imp_distrib} &  @{thm dmd_imp_distrib[no_vars]}\\\hline
@{thm [source] pdl_box_reg} &  @{thm pdl_box_reg[no_vars]}\\\hline
@{thm [source] pdl_dmd_reg} &  @{thm pdl_dmd_reg[no_vars]}\\\hline
@{thm [source] pdl_wkB} &  @{thm pdl_wkB[no_vars]}\\\hline
@{thm [source] pdl_wkD} &  @{thm pdl_wkD[no_vars]}\\\hline
@{thm [source] pdl_plugB} &  @{thm pdl_plugB[no_vars]}\\\hline
@{thm [source] box_conj_distrib} &  @{thm box_conj_distrib[no_vars]}\\\hline
@{thm [source] pdl_seqB_split} &  @{thm pdl_seqB_split[no_vars]}\\\hline
@{thm [source] pdl_seqB_join} &  @{thm pdl_seqB_join[no_vars]}\\\hline
@{thm [source] pdl_seqD_split} &  @{thm pdl_seqD_split[no_vars]}\\\hline
@{thm [source] pdl_seqD_join} &  @{thm pdl_seqD_join[no_vars]}\\\hline
@{thm [source] pdl_wkB_lifted1} &  @{thm pdl_wkB_lifted1[no_vars]}\\\hline
@{thm [source] box_conj_distrib_lifted1} &  @{thm box_conj_distrib_lifted1[no_vars]}\\\hline
@{thm [source] pdl_seqB_lifted1} &  @{thm pdl_seqB_lifted1[no_vars]}\\\hline
@{thm [source] pdl_plugB_lifted1} &  @{thm pdl_plugB_lifted1[no_vars]}\\\hline
@{thm [source] imp_box_conj1} &  @{thm imp_box_conj1[no_vars]}\\\hline
@{thm [source] imp_box_conj2} &  @{thm imp_box_conj2[no_vars]}\\\hline
\end{tabular}

\begin{tabular}{lp{0.7\textwidth}}
@{thm [source] MonEq_Ret_hom} &  @{thm MonEq_Ret_hom[no_vars]}\\\hline
\end{tabular}

\begin{tabular}{lp{0.7\textwidth}}
@{thm [source] dsef_eot} &  @{thm dsef_eot[no_vars]}\\\hline
@{thm [source] Eot_GetInput} &  @{thm Eot_GetInput[no_vars]}\\\hline
@{thm [source] GetInput_item_fail} &  @{thm GetInput_item_fail[no_vars]}\\\hline
@{thm [source] digitp_nat} &  @{thm digitp_nat[no_vars]}\\\hline
@{thm [source] digitp_fail} &  @{thm digitp_fail[no_vars]}\\\hline
\end{tabular}

\begin{tabular}{lp{0.7\textwidth}}
@{thm [source] pdl_conj_imp_wk1} &  @{thm pdl_conj_imp_wk1[no_vars]}\\\hline
@{thm [source] pdl_conj_imp_wk2} &  @{thm pdl_conj_imp_wk2[no_vars]}\\\hline
@{thm [source] pdl_conj_imp_box_split} &  @{thm pdl_conj_imp_box_split[no_vars]}\\\hline
@{thm [source] dsef_form_eq} &  @{thm dsef_form_eq[no_vars]}\\\hline
@{thm [source] dsefB_D} &  @{thm dsefB_D[no_vars]}\\\hline
@{thm [source] even_div_eq} &  @{thm even_div_eq[no_vars]}\\\hline
@{thm [source] odd_div_eq} &  @{thm odd_div_eq[no_vars]}\\\hline
@{thm [source] pdl_dsefB_ret} &  @{thm pdl_dsefB_ret[no_vars]}\\\hline
@{thm [source] russian_mult} &  @{thm russian_mult[no_vars]}\\\hline
\end{tabular}
*}

end
