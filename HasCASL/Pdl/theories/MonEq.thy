(* Title:  MonEq.thy
   Id:     2005-03-13
   Author: Dennis Walter
*)

header {* Monadic equality *}
theory MonEq = MonLogic:



constdefs
  "MonEq"  :: "['a D, 'a D] \<Rightarrow> bool D"    (infixl "=\<^sub>D" 60)
  "MonEq a b \<equiv> \<Up> (liftM2 (op =) (\<Down> a) (\<Down> b))"


lemma MonEq_Ret_hom: "((Ret a) =\<^sub>D (Ret b)) = (Ret (a=b))"
by (simp add: lift_Ret_hom MonEq_def)


(* Not so interesting since it used nowhere *)
(*<*)


(* A copyable and discardable program commutes with all cp and dis programs iff
   it commutes with all bool-valued cp/dis programs. *)
axioms 
dsef_anytype: "\<lbrakk>(\<forall>q::bool T. cp q \<and> dis q \<longrightarrow> cp (do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)}));
                cp p; dis p\<rbrakk> \<Longrightarrow>
                \<forall>q::'a T. cp q \<and> dis q \<longrightarrow> cp (do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)})"
mon_eq_trans: "\<lbrakk>\<turnstile> a =\<^sub>D b; \<turnstile> b =\<^sub>D c\<rbrakk> \<Longrightarrow> \<turnstile> a =\<^sub>D c"
mon_eq_refl:  "\<turnstile> a =\<^sub>D a"
mon_eq_sym:   "(a =\<^sub>D b) = (b =\<^sub>D a)"


lemma sym_subst_seq2: "\<forall>x y. c x y = c y x \<Longrightarrow> do {x\<leftarrow>p; y\<leftarrow>q; c x y} = do {x\<leftarrow>p; y\<leftarrow>q; c y x}"
  by simp


(* An ugly and cumbersome proof if ever there was one 
   uses "coercion lemma" dsef_anytype *)
theorem mon_eq_sym1: "\<turnstile> a =\<^sub>D b \<Longrightarrow> \<turnstile> b =\<^sub>D a"
proof -
  assume asm: "\<turnstile> a =\<^sub>D b"
  have "do {x\<leftarrow>\<Down> b; y\<leftarrow>\<Down> a; ret(x=y)} = 
        do {x\<leftarrow>\<Down> a; y\<leftarrow>\<Down> b; ret(x=y)}"
  proof -
    have "dsef (\<Down> a)"
      by (rule dsef_Rep_Dsef)
    moreover have "dsef (\<Down> b)" 
      by (rule dsef_Rep_Dsef)
    ultimately have "do {x\<leftarrow>(\<Down> a); y\<leftarrow>(\<Down> b); ret(x,y)} 
                     = do {y\<leftarrow>(\<Down> b); x\<leftarrow>(\<Down> a); ret(x,y)}"
      apply(simp add: dsef_def)
      apply(clarify)
      apply(drule dsef_anytype, assumption+)
      apply(drule_tac x = "\<Down> b" in spec)
      apply(drule conjI, assumption, drule mp, assumption, erule conjE)
      apply(rule commute_1_2, assumption+)
      done
    thus ?thesis
    proof -
      let ?ra = "\<Down> a" and ?rb = "\<Down> b"
      assume a1: "do {x\<leftarrow>?ra; y\<leftarrow>?rb; ret (x, y)} 
                = do {y\<leftarrow>?rb; x\<leftarrow>?ra; ret (x, y)}"
      have "do {x\<leftarrow>?rb; y\<leftarrow>?ra; ret(x = y)} = 
            do {u\<leftarrow>do {x\<leftarrow>?rb; y\<leftarrow>?ra; ret(y,x)}; ret(snd u = fst u)}"
	by (simp add: mon_ctr)
      also from a1 have "\<dots> = do {u\<leftarrow>do {x\<leftarrow>?ra; y\<leftarrow>?rb; ret(x,y)}; ret((snd u) = (fst u))}"
	by simp
      also have "\<dots> = do {x\<leftarrow>?ra; y\<leftarrow>?rb; ret(y = x)}" by (simp add: mon_ctr)
      also have "\<dots> = do {x\<leftarrow>?ra; y\<leftarrow>?rb; ret(x = y)}"
      proof -
	have rs: " \<forall>x y. ret(y=x) = ret(x=y)" 
	proof (rule allI)+
	  fix x y
	  have "(x = y) = (y = x)" by blast
	  thus "ret(x=y) = ret(y=x)" by simp
	qed
	show ?thesis by (rule sym_subst_seq2, rule rs)
      qed
      finally show ?thesis . 
    qed
  qed
  hence "(liftM2 op = (\<Down> a) (\<Down> b))
         = (liftM2 op = (\<Down> b) (\<Down> a))" (is "?A = ?B") 
    by (simp add: liftM2_def)
  hence "\<Up> ?A = \<Up> ?B" by simp
  with asm show "\<turnstile> b =\<^sub>D a" by (simp add: MonEq_def)
qed


(*>*)

end
