(* Title:  MonEq.thy
   Id:     2005-03-13
   Author: Dennis Walter
*)

header {* Monadic Equality *}
theory MonEq = MonLogic:

text {* \label{sec:moneq-thy} *}

constdefs
  "MonEq"  :: "['a D, 'a D] \<Rightarrow> bool D"    (infixl "=\<^sub>D" 60)
  "MonEq a b \<equiv> \<Up> (liftM2 (op =) (\<Down> a) (\<Down> b))"


lemma MonEq_Ret_hom: "((Ret a) =\<^sub>D (Ret b)) = (Ret (a=b))"
by (simp add: lift_Ret_hom MonEq_def)


text {* Transitivity of monadic equality. *}
lemma mon_eq_trans: "\<lbrakk>\<turnstile> a =\<^sub>D b; \<turnstile> b =\<^sub>D c\<rbrakk> \<Longrightarrow> \<turnstile> a =\<^sub>D c"
proof -
  assume ab: "\<turnstile> a =\<^sub>D b" and bc: "\<turnstile> b =\<^sub>D c"
  have "\<turnstile> (a =\<^sub>D b) \<longrightarrow>\<^sub>D (b =\<^sub>D c) \<longrightarrow>\<^sub>D (a =\<^sub>D c)"
    apply(simp add: MonEq_def impD_def liftM2_def)
    apply(simp add: Abs_Dsef_inverse dsef_Rep_Dsef Dsef_def dsef_seq mon_ctr del: bind_assoc)
    apply(simp add: cp_arb dsef_cp[OF dsef_Rep_Dsef]) 
    apply(simp add: commute_dsef[of "\<Down> c" "\<Down> a"]) 
    apply(simp add: commute_dsef[of "\<Down> b" "\<Down> a"]) 
    apply(simp add: cp_arb dsef_cp[OF dsef_Rep_Dsef] del: bind_assoc) 
    apply (simp add: dsef_dis[OF dsef_Rep_Dsef] dis_left2)
    apply(subst Ret_def[symmetric])
    by simp
  from this ab bc show ?thesis by (rule pdl_mp[THEN pdl_mp])
qed

text {* Reflexivity of monadic equality. *}
lemma mon_eq_refl:  "\<turnstile> a =\<^sub>D a"
  apply(simp add: MonEq_def liftM2_def)
  apply(simp add: cp_arb dsef_cp[OF dsef_Rep_Dsef])
  apply(simp add: dis_left2 dsef_dis[OF dsef_Rep_Dsef])
  apply(subst Ret_def[symmetric])
  by (simp)


text {* Auxiliary lemma, just to help the simplifier. *}
lemma sym_subst_seq2: "\<forall>x y. c x y = c y x \<Longrightarrow> 
  (\<Up> (do {x\<leftarrow>p; y\<leftarrow>q; c x y})) = (\<Up> (do {x\<leftarrow>p; y\<leftarrow>q; c y x}))"
  by simp


text {* Symmetry of monadic equality. 
  The simplifier gets into trouble here, for it must apply symmetry
  of real equality inside the scope of lambda terms. We circumvent
  this problem by extracting the essential proof obligation through 
  @{thm [source] sym_subst_seq2} and then working by hand.
*}

lemma mon_eq_sym:   "(a =\<^sub>D b) = (b =\<^sub>D a)"
  apply(simp add: MonEq_def liftM2_def)
  apply(simp add: commute_dsef[of "\<Down> a" "\<Down> b"])
  apply(rule sym_subst_seq2)
  apply(clarify)
  apply(rule arg_cong[where f = ret]) 
  by (rule eq_sym_conv)

end
