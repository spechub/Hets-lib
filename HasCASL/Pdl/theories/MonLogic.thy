(*
   Theory MonLogic introduces monadic logical connectives \<and>\<^sub>D etc. for the subtype
   ('a D) of dsef monadic programs.
   Currently -because of time limitations- the rules for this logic are 
   given as axioms rather than as Lemmas; these axioms constitute an intuistionistic
   logic, thus following Schroeder/Mossakowski.
*)

header {* Introducing Propositional Connectives *}
theory MonLogic = MonProp:


subsection {* Propositional Connectives *}

text {* As usual in intuitionistic logics, we introduce conjunction,
  disjunction and implication independently of each other.
*}  
consts
 "Valid"       :: "bool D => bool"               ("(\<turnstile> _)" 15)
 "\<and>\<^sub>D"         :: "[bool D, bool D] => bool D"     (infixr 35)
 "\<or>\<^sub>D"         :: "[bool D, bool D] => bool D"     (infixr 30)
 "\<longrightarrow>\<^sub>D"        :: "[bool D, bool D] \<Rightarrow> bool D"    (infixr 25)

text {*
  According with the definition in \cite{SchroederMossakowski:PDL}, the connectives
  are simply lifted from HOL, and validity amounts to being
  equal to a program always returning @{term "True"}.
*}
defs
  Valid_def: "\<turnstile> P \<equiv> \<Down> P = do {x\<leftarrow>(\<Down> P); ret True}"
  conjD_def: "P \<and>\<^sub>D Q \<equiv> \<Up> (liftM2 (op \<and>) (\<Down> P) (\<Down> Q))"
  disjD_def: "P \<or>\<^sub>D Q \<equiv> \<Up> (liftM2 (op \<or>) (\<Down> P) (\<Down> Q))"
  impD_def:  "P \<longrightarrow>\<^sub>D Q \<equiv> \<Up> (liftM2 (op \<longrightarrow>) (\<Down> P) (\<Down> Q))"


constdefs
 iffD        :: "[bool D, bool D] \<Rightarrow> bool D"   (infixr "\<longleftrightarrow>\<^sub>D" 20)
 "P \<longleftrightarrow>\<^sub>D Q \<equiv> (P \<longrightarrow>\<^sub>D Q) \<and>\<^sub>D (Q \<longrightarrow>\<^sub>D P)"
 NotD        :: "bool D \<Rightarrow> bool D"              ("\<not>\<^sub>D _" [40] 40)
  "\<not>\<^sub>D P \<equiv> P \<longrightarrow>\<^sub>D Ret False"





text {*
  Because of discardability, the definition of @{term "Valid"}, which 
  was simply taken over from the definition of global validity of terms of type
  @{typ "bool T"}, can be simplified.
*}
lemma Valid_simp: "(\<turnstile> p) = (\<Down> p = ret True)"
proof
  assume vp: "\<turnstile> p"
  show "\<Down> p = ret True"
  proof -
    from vp have "\<Down> p = do {\<Down> p; ret True}"
      by (simp only: Valid_def seq_def)
    also have "\<dots> = ret True" by (rule dis_left, rule dis_Rep_Dsef)  
    finally show ?thesis .
  qed
next
  assume "\<Down> p = ret True"
  hence "\<Down> p = do {x\<leftarrow>\<Down> p; ret True}" by simp
  thus "\<turnstile> p" by (simp only: Valid_def)
qed


text {*
  There is a notion of homomorphism associated with lifted operations. The formulation
  does not really make clear what is intended, but the subsequent lemmas should
  illuminate the idea.
*}
theorem lift_Ret_hom:  "(\<Up> (liftM2 f (\<Down> (Ret a)) (\<Down> (Ret b)))) 
                            = Ret (f a b)"
proof -
  have "\<Up> (liftM2 f (\<Down> (Ret a)) (\<Down> (Ret b)))
        = \<Up> (do {x\<leftarrow>(\<Down> (Ret a)); y\<leftarrow>(\<Down> (Ret b)); ret (f x y)})"
    by (simp only: liftM2_def)
  also have "\<dots> = \<Up> (do {x\<leftarrow>(\<Down> (\<Up> (ret a))); 
                                y\<leftarrow>(\<Down> (\<Up> (ret b))); ret (f x y)})"
    by (simp add: Ret_def)
  also have "\<dots> = \<Up> (do {x\<leftarrow>ret a; y\<leftarrow>ret b; ret(f x y)})"
    by (simp add: Dsef_def Abs_Dsef_inverse)
  also have "\<dots> = \<Up> (ret (f a b))" by simp
  also have "\<dots> = Ret (f a b)" by (simp only: Ret_def)
  finally show ?thesis .
qed


lemma conjD_Ret_hom: "Ret (a\<and>b) = ((Ret a) \<and>\<^sub>D (Ret b))"
  by (simp add: lift_Ret_hom conjD_def)
lemma disjD_Ret_hom: "Ret (a\<or>b) = ((Ret a) \<or>\<^sub>D (Ret b))"
  by (simp add: lift_Ret_hom disjD_def)
lemma impD_Ret_hom: "Ret (a\<longrightarrow>b) = ((Ret a) \<longrightarrow>\<^sub>D (Ret b))"
  by (simp add: lift_Ret_hom impD_def)

lemma NotD_Ret_hom: "Ret (\<not> P) = (\<not>\<^sub>D (Ret P))"
  by(simp add: NotD_def impD_Ret_hom[symmetric])



text {*
  If a formula depending on variable @{term "x"} is valid for all @{term "x"}, then we
  may also `substitute' it by a @{term "dsef"} term.
*}

lemma dsef_form: " \<forall>x. \<turnstile> P x \<Longrightarrow> \<forall>b. \<turnstile> \<Up> (do {a\<leftarrow>\<Down> b; \<Down> (P a)})"
proof
  fix b
  assume a1: " \<forall>x. \<turnstile> P x"
  hence "\<Down> (\<Up> (do {a\<leftarrow>\<Down> (b::'a D); \<Down> (P a)})) = 
        \<Down> (\<Up> (do {a\<leftarrow>\<Down> (b::'a D); ret True}))"
    by (simp add: Valid_simp) 
  also have "\<dots> = do {a\<leftarrow>\<Down> b; ret True}"
  proof (rule Abs_Dsef_inverse)
    have "dsef (do {a\<leftarrow>\<Down> b; ret True})"
      by (simp add: dsef_ret dsef_Rep_Dsef dsef_seq)
    thus "do {a\<leftarrow>\<Down> b; ret True} \<in> Dsef" by (simp add: Dsef_def)
  qed
  also have "\<dots> = ret True" by (simp add: dis_left2 dsef_dis[OF dsef_Rep_Dsef])
  finally show "\<turnstile> \<Up> (do {a\<leftarrow>\<Down> (b::'a D); \<Down> (P a)})"
    by (simp add: Valid_simp)
qed


text {*
  Every true formula may be injected into @{typ "bool D"} by @{term "Ret"} to 
  yield a valid formula of dynamic logic. And the converse also holds!
*}

theorem Valid_Ret [simp]: "(\<turnstile> Ret P) = P"
proof 
  assume p: "P"
  have "\<Down> (Ret P) = do {x\<leftarrow>\<Down> (Ret P); ret True}"
  proof -
    have "dsef (\<Down> (Ret P))" by (rule dsef_Rep_Dsef)
    hence ds: "dis (\<Down> (Ret P))" by (simp only: dsef_def)
    have "\<Down> (Ret P) = ret P" by (rule Ret_ret)
    also from p have "\<dots> = ret True" by simp
    also from ds have "\<dots> = do {\<Down> (Ret P); ret True}" by (rule dis_left[symmetric])
    finally show ?thesis by (simp only: seq_def)
  qed
  thus "\<turnstile> Ret P" by (simp only: Valid_def)
next
  assume rp: "\<turnstile> Ret P"
  hence "\<Down> (Ret P) = ret True" by (rule iffD1[OF Valid_simp])
  hence "ret P = ret True"
    by (simp add: Ret_def Dsef_def Abs_Dsef_inverse)
  hence "P = True" by (rule ret_inject)
  thus "P" by rules
qed
  


text {* 
  A bit more tedious, but conversely to @{thm [source] Valid_simp} it is also true
  that every valid formula that is a negation equals @{term "ret False"}.
*}
lemma Valid_not_eq_ret_False: "(\<turnstile> \<not>\<^sub>D b) = (\<Down> b = ret False)"
proof
  assume "\<turnstile> \<not>\<^sub>D b"
  hence nt: "\<Down> (\<not>\<^sub>D b) = ret True" by (simp add: Valid_simp)
  show "\<Down> b = ret False"
  proof -
    have "dsef (do {x\<leftarrow>\<Down> b; ret (\<not> x)})"
      by (rule weak_dsef_seq, rule dsef_Rep_Dsef) 
    hence bnnb: "b = (\<not>\<^sub>D (\<not>\<^sub>D b))"
      by (simp add: NotD_def impD_def liftM2_def 
                    Ret_ret Abs_Dsef_inverse Dsef_def mon_ctr Rep_Dsef_inverse) 
    from nt have "\<Up> (\<Down> (\<not>\<^sub>D b)) = Ret True" by (simp add: Ret_def)
    hence "(\<not>\<^sub>D b) = Ret True" by (simp only: Rep_Dsef_inverse)
    hence "(\<not>\<^sub>D (\<not>\<^sub>D b)) = (\<not>\<^sub>D (Ret True))" by simp
    with bnnb have "b = Ret (\<not> True)" by (simp add: NotD_Ret_hom[symmetric])
    thus ?thesis by (simp add: Ret_ret)
  qed
next
  assume "\<Down> b = ret False"
  hence "\<Up> (\<Down> b) = \<Up> (ret False)" by simp
  hence bf: "b = Ret False" by (simp add: Rep_Dsef_inverse Ret_def)
  have "\<Down> (\<not>\<^sub>D b) = ret True"
  proof -
    from bf have "\<Down> (\<not>\<^sub>D b) = \<Down> (Ret False \<longrightarrow>\<^sub>D Ret False)"
      by (simp add: NotD_def)
    also have "\<dots> = \<Down> (Ret True)" 
    proof -
      have "(Ret False \<longrightarrow>\<^sub>D Ret False) = Ret (False \<longrightarrow> False)"
	by (rule impD_Ret_hom[symmetric])
      thus ?thesis by simp
    qed
    also have "\<dots> = ret True" by (rule Ret_ret)
    finally show ?thesis .
  qed
  thus "\<turnstile> \<not>\<^sub>D b" by (simp only: Valid_simp)
qed
    

text {*
  Lemmas @{thm [source] Valid_simp}, @{thm [source] Valid_not_eq_ret_False} 
  and @{thm [source] Valid_Ret} show that, since the classical type @{typ bool} 
  is taken as the carrier of truth values, the whole calculus is classical.
*} 


subsection {* Setting up the Simplifier for Propositional Reasoning *}


text {* 
  Since natural deduction rules don't get us far in the calculus of global
  validity judgments (in particular, we do not have an analogon for
  the implication introduction rule), we algebraize it and perform
  proofs by term manipulation.
 
  All these axioms are in fact provable; it is just the shortage of time that
  forces us to impose them directly.  
*}

constdefs
  xorD :: "[bool D, bool D] \<Rightarrow> bool D"      (infixr "\<oplus>\<^sub>D" 20)
  "xorD P Q  \<equiv>  (P \<and>\<^sub>D \<not>\<^sub>D Q) \<or>\<^sub>D (\<not>\<^sub>D P \<and>\<^sub>D Q)"

  
axioms
  apl_and_assoc:   "((P \<and>\<^sub>D Q) \<and>\<^sub>D R) = (P \<and>\<^sub>D (Q \<and>\<^sub>D R))"
  apl_xor_assoc:    "((P \<oplus>\<^sub>D Q) \<oplus>\<^sub>D R) = (P \<oplus>\<^sub>D (Q \<oplus>\<^sub>D R))"
  apl_and_comm:     "(P \<and>\<^sub>D Q) = (Q \<and>\<^sub>D P)"
  apl_xor_comm:     "(P \<oplus>\<^sub>D Q) = (Q \<oplus>\<^sub>D P)"
  apl_and_LC:       "(P \<and>\<^sub>D (Q \<and>\<^sub>D R)) = (Q \<and>\<^sub>D (P \<and>\<^sub>D R))"
  apl_xor_LC:       "(P \<oplus>\<^sub>D (Q \<oplus>\<^sub>D R)) = (Q \<oplus>\<^sub>D (P \<oplus>\<^sub>D R))"
  apl_and_True_r:   "(P \<and>\<^sub>D Ret True) = P"
  apl_and_True_l:   "(Ret True \<and>\<^sub>D P) = P"
  apl_and_absorb:   "(P \<and>\<^sub>D P) = P"
  apl_and_absorb2:  "(P \<and>\<^sub>D (P \<and>\<^sub>D Q)) = (P \<and>\<^sub>D Q)"
  apl_and_False_l:  "(Ret False \<and>\<^sub>D P) = Ret False"
  apl_and_False_r:  "(P \<and>\<^sub>D Ret False) = Ret False"
  apl_xor_False_r:  "(P \<oplus>\<^sub>D Ret False) = P"
  apl_xor_False_l:  "(Ret False \<oplus>\<^sub>D P) = P"
  apl_xor_contr:    "(P \<oplus>\<^sub>D P) = Ret False"
  apl_xor_contr2:   "(P \<oplus>\<^sub>D (P \<oplus>\<^sub>D Q)) = Q"
  apl_and_ldist:    "(P \<and>\<^sub>D (Q \<oplus>\<^sub>D R)) = ((P \<and>\<^sub>D Q) \<oplus>\<^sub>D (P \<and>\<^sub>D R))"
  apl_and_rdist:    "((P \<oplus>\<^sub>D Q) \<and>\<^sub>D R) = ((P \<and>\<^sub>D R) \<oplus>\<^sub>D (Q \<and>\<^sub>D R))"
  -- {* Expressing the connectives by conjunction and exclusive or *}
  apl_imp_xor:      "(P \<longrightarrow>\<^sub>D Q) = ((P \<and>\<^sub>D Q) \<oplus>\<^sub>D P \<oplus>\<^sub>D Ret True)"
  apl_or_xor:       "(P \<or>\<^sub>D Q) = (P \<oplus>\<^sub>D Q \<oplus>\<^sub>D (P \<and>\<^sub>D Q))"
  apl_not_xor:      "(\<not>\<^sub>D P) = (P \<oplus>\<^sub>D Ret True)"
  apl_iff_xor:      "(P \<longleftrightarrow>\<^sub>D Q) = (P \<oplus>\<^sub>D Q \<oplus>\<^sub>D Ret True)"


text {* @{text "pdl_taut"} is the collection of all these rules, so that
  they can be handed over to the simplifier conveniently.
  
  This set of rewrite rules is complete with respect to normalisation
  of propositional tautologies to their normal form 
  @{term "Ret True"}. Hence, we can prove monadic tautologies 
  in one fell swoop by applying 
  the tactic @{text "(simp only: pdl_taut Valid_Ret)"}.
*}

lemmas pdl_taut = (*<*) apl_and_assoc apl_xor_assoc apl_and_comm apl_xor_comm 
  apl_and_LC apl_xor_LC apl_and_True_r apl_and_True_l apl_and_absorb 
  apl_and_absorb2 apl_and_False_l apl_and_False_r apl_xor_False_r 
  apl_xor_False_l apl_xor_contr apl_xor_contr2 apl_and_ldist apl_and_rdist
  apl_imp_xor apl_or_xor apl_not_xor apl_iff_xor (*>*) -- {* \dots all axioms above *}


lemmas mon_prop_reason = Abs_Dsef_inverse dsef_liftM2 
  Dsef_def conjD_def disjD_def impD_def NotD_def 


text {* A proof showing in what manner the above axioms may be proved *}
lemma "(P \<and>\<^sub>D (\<not>\<^sub>D P)) = Ret False"
  apply(simp add: mon_prop_reason, simp only: liftM2_def)
  apply(unfold Ret_def)
  apply(rule cong[of Abs_Dsef Abs_Dsef], rule refl)
  apply(simp add: Abs_Dsef_inverse Dsef_def)
  apply(simp add: mon_ctr del: bind_assoc)
  apply(simp add: cp_arb dsef_cp[OF dsef_Rep_Dsef])
  apply(rule dis_left2)
  apply(rule dsef_dis[OF dsef_Rep_Dsef])
done


subsection {* Proof Rules *}

text {* 
  Proof rules, which can all be proven to be correct, since we have
  the semantics built into the logic (i.e. we can access it within HOL).
  Some proofs however simply employ the above tautology reasoner.
*}

theorem pdl_excluded_middle: "\<turnstile> P \<or>\<^sub>D (\<not>\<^sub>D P)"
  by (simp add: pdl_taut)


theorem pdl_mp: "\<lbrakk>\<turnstile> P \<longrightarrow>\<^sub>D Q; \<turnstile> P\<rbrakk> \<Longrightarrow> \<turnstile> Q"
  by(simp add: Valid_simp impD_def liftM2_def Rep_Dsef_inverse)

text {* Disjunction introduction *}
theorem pdl_disjI1: "\<turnstile> P \<Longrightarrow> \<turnstile> (P \<or>\<^sub>D Q)"
proof -
  assume "\<turnstile> P"
  hence pt: "\<Down> P = ret True" by (simp only: Valid_simp)
  have "\<Down> (P \<or>\<^sub>D Q) = ret True" 
  proof -
    have "\<Down> (\<Up> (liftM2 op \<or> (\<Down> P) (\<Down> Q))) = ret True"
    proof -
      have "\<Down> (\<Up> (do {x\<leftarrow>\<Down> Q; ret True})) = ret True"
      proof -
	have "\<Down> (\<Up> (do {x\<leftarrow>\<Down> Q; ret True})) = 
	  do {x\<leftarrow>\<Down> Q; ret True}"
	  by (simp add: Abs_Dsef_inverse Dsef_def weak_dsef_seq)
	also have "\<dots> = do {\<Down> Q; ret True}" by (simp only:seq_def)
	also have "\<dots> = ret True" by (simp add: dis_Rep_Dsef dis_left)
	finally show ?thesis .
      qed
      with pt show ?thesis by (simp add: liftM2_def)
    qed
    thus ?thesis by (simp only: disjD_def)
  qed
  thus "\<turnstile> (P \<or>\<^sub>D Q)" by (simp only: Valid_simp)
qed

text {* Entirely analogous for this dual rule. *}
theorem pdl_disjI2: "\<turnstile> Q \<Longrightarrow> \<turnstile> (P \<or>\<^sub>D Q)"
(*<*)
proof -
  assume "\<turnstile> Q"
  hence qt: "\<Down> Q = ret True" by (simp only: Valid_simp)
  have "\<Down> (P \<or>\<^sub>D Q) = ret True" 
  proof -
    have "\<Down> (\<Up> (liftM2 op \<or> (\<Down> P) (\<Down> Q))) = ret True"
    proof -
      have "\<Down> (\<Up> (do {x\<leftarrow>\<Down> P; ret True})) = ret True"
      proof -
	have "\<Down> (\<Up> (do {x\<leftarrow>\<Down> P; ret True})) = 
	  do {x\<leftarrow>\<Down> P; ret True}"
	  by (simp add: Abs_Dsef_inverse Dsef_def weak_dsef_seq)
	also have "\<dots> = do {\<Down> P; ret True}" by (simp only:seq_def)
	also have "\<dots> = ret True" by (simp add: dis_Rep_Dsef dis_left)
	finally show ?thesis .
      qed
      with qt show ?thesis by (simp add: liftM2_def)
    qed
    thus ?thesis by (simp only: disjD_def)
  qed
  thus "\<turnstile> (P \<or>\<^sub>D Q)" by (simp only: Valid_simp)
qed
(*>*)


text {* 
  The following proof proceeds by a standard pattern: First insert the 
  assumptions into some specifically tailored do-term and then 
  reduce this do-term to @{term "ret True"} with the simplifier.
*}
theorem pdl_disjE: "\<lbrakk> \<turnstile> P \<or>\<^sub>D Q; \<turnstile> P \<longrightarrow>\<^sub>D R; \<turnstile> Q \<longrightarrow>\<^sub>D R\<rbrakk> \<Longrightarrow> \<turnstile> R"
proof -
  assume a1: "\<turnstile> P \<or>\<^sub>D Q" "\<turnstile> P \<longrightarrow>\<^sub>D R" "\<turnstile> Q \<longrightarrow>\<^sub>D R"
  note copy = dsef_cp[OF dsef_Rep_Dsef]
  note dsc  = dsef_dis[OF dsef_Rep_Dsef]
  -- {* 1st part: blow up program @{term "\<Down> R"} to some giant term: *}
  have "\<Down> R = do {u\<leftarrow>ret True; v\<leftarrow>ret True; w\<leftarrow>ret True; r\<leftarrow>\<Down> R; ret(u\<longrightarrow>v\<longrightarrow>w\<longrightarrow>r)}"
    by simp
  also from a1 have "\<dots> = do {u\<leftarrow>(\<Down> (P \<or>\<^sub>D Q));
                             v\<leftarrow>(\<Down> (P \<longrightarrow>\<^sub>D R));
                             w\<leftarrow>(\<Down> (Q \<longrightarrow>\<^sub>D R));
                             r\<leftarrow>\<Down> R; ret (u\<longrightarrow>v\<longrightarrow>w\<longrightarrow>r)}"
    by (simp add: Valid_simp)
  -- {* 2nd part: reduce this giant program to @{term "ret True"} exploiting
        properties of dsef programs *}
  also have "\<dots> = ret True"
    apply(simp add: mon_prop_reason liftM2_def dsef_Rep_Dsef dsef_seq mon_ctr del: bind_assoc)
    apply(simp add: commute_dsef[of "\<Down> Q" "\<Down> P"])
    apply(simp add: commute_dsef[of "\<Down> R" "\<Down> Q"])
    apply(simp add: dsef_cp[OF dsef_Rep_Dsef] cp_arb del: bind_assoc)
    apply(simp add: dsef_dis[OF dsef_Rep_Dsef] dis_left2)
    done
  finally show ?thesis by (simp only: Valid_simp)
qed
    

theorem pdl_conjI: "\<lbrakk> \<turnstile> P; \<turnstile> Q \<rbrakk> \<Longrightarrow> \<turnstile> P \<and>\<^sub>D Q"
proof -
  assume a: "\<turnstile> P" "\<turnstile> Q"
  from a have "\<Down> P = ret True" by (simp add: Valid_simp)
  moreover
  from a have "\<Down> Q = ret True" by (simp add: Valid_simp)
  ultimately 
  have "\<Down> (P \<and>\<^sub>D Q) = ret True"
    by (simp add: mon_prop_reason liftM2_def) 
  thus ?thesis by (simp add: Valid_simp)
qed


subsubsection {* Derived rules of inference *}


theorem pdl_FalseE: "\<turnstile> Ret False \<Longrightarrow> \<turnstile> R"
proof -
  assume "\<turnstile> Ret False"
  hence "False" by (rule iffD1[OF Valid_Ret])
  thus "\<turnstile> R" by (rule FalseE)
qed


lemma pdl_notE: "\<lbrakk> \<turnstile> P; \<turnstile> \<not>\<^sub>D P \<rbrakk> \<Longrightarrow> \<turnstile> R"
proof (unfold NotD_def)
  assume p: "\<turnstile> P" and np: "\<turnstile> P \<longrightarrow>\<^sub>D Ret False"
  from np p have "\<turnstile> Ret False" by (rule pdl_mp)
  thus "\<turnstile> R" by (rule pdl_FalseE)
qed


lemma pdl_conjE: "\<lbrakk> \<turnstile> P \<and>\<^sub>D Q; \<lbrakk>\<turnstile> P; \<turnstile> Q\<rbrakk> \<Longrightarrow> \<turnstile> R\<rbrakk> \<Longrightarrow> \<turnstile> R"
proof -
  assume a1: "\<turnstile> P \<and>\<^sub>D Q"
  assume a2: "\<lbrakk>\<turnstile> P; \<turnstile> Q\<rbrakk> \<Longrightarrow> \<turnstile> R"
  have "\<turnstile> P" 
  proof (rule pdl_mp)
    show "\<turnstile> P \<and>\<^sub>D Q \<longrightarrow>\<^sub>D P" by (simp add: pdl_taut)
  qed
  moreover
  have "\<turnstile> Q" 
  proof (rule pdl_mp)
    show "\<turnstile> P \<and>\<^sub>D Q \<longrightarrow>\<^sub>D Q" by (simp add: pdl_taut)
  qed
  moreover note a1 a2
  ultimately 
  show "\<turnstile> R" by (rules)
qed


text {* Some further typical rules *}
lemma pdl_notI: "\<lbrakk> \<turnstile> P; \<turnstile> Ret False\<rbrakk> \<Longrightarrow> \<turnstile> \<not>\<^sub>D P"
by(rule pdl_FalseE)

lemma pdl_conjunct1: "\<turnstile> P \<and>\<^sub>D Q \<Longrightarrow> \<turnstile> P"
proof -
  assume "\<turnstile> P \<and>\<^sub>D Q"
  thus "\<turnstile> P"
  proof (rule pdl_conjE)
    assume "\<turnstile> P"
    thus ?thesis .
  qed
qed

lemma pdl_conjunct2: assumes pq: "\<turnstile> P \<and>\<^sub>D Q" shows "\<turnstile> Q"
proof -
  from pq show "\<turnstile> Q"
  proof (rule pdl_conjE)
    assume "\<turnstile> Q"
    thus ?thesis .
  qed
qed
    
lemma pdl_iffI: "\<lbrakk>\<turnstile> P \<longrightarrow>\<^sub>D Q; \<turnstile> Q \<longrightarrow>\<^sub>D P\<rbrakk> \<Longrightarrow> \<turnstile> P \<longleftrightarrow>\<^sub>D Q"
proof (unfold iffD_def)
  assume a: "\<turnstile> P \<longrightarrow>\<^sub>D Q" and b: "\<turnstile> Q \<longrightarrow>\<^sub>D P"
  show "\<turnstile> (P \<longrightarrow>\<^sub>D Q) \<and>\<^sub>D (Q \<longrightarrow>\<^sub>D P)"
    by (rule pdl_conjI)
qed

lemma pdl_iffE: "\<lbrakk>\<turnstile> P \<longleftrightarrow>\<^sub>D Q; \<lbrakk> \<turnstile> P \<longrightarrow>\<^sub>D Q; \<turnstile> Q \<longrightarrow>\<^sub>D P \<rbrakk> \<Longrightarrow> \<turnstile> R\<rbrakk> \<Longrightarrow> \<turnstile> R"
 apply(unfold iffD_def) 
 apply(erule pdl_conjE)
by blast

lemma pdl_sym: "(\<turnstile> P \<longleftrightarrow>\<^sub>D Q) \<Longrightarrow> (\<turnstile> Q \<longleftrightarrow>\<^sub>D P)"
  apply(erule pdl_iffE)
by(rule pdl_iffI)

lemma pdl_iffD1: "\<turnstile> P \<longleftrightarrow>\<^sub>D Q \<Longrightarrow> \<turnstile> P \<longrightarrow>\<^sub>D Q"
by(erule pdl_iffE)

lemma pdl_iffD2: "\<turnstile> P \<longleftrightarrow>\<^sub>D Q \<Longrightarrow> \<turnstile> Q \<longrightarrow>\<^sub>D P"
by (erule pdl_iffE)

lemma pdl_conjI_lifted: 
assumes "\<turnstile> P \<longrightarrow>\<^sub>D Q" and "\<turnstile> P \<longrightarrow>\<^sub>D R" shows "\<turnstile> P \<longrightarrow>\<^sub>D Q \<and>\<^sub>D R"
proof -
  have "\<turnstile> (P \<longrightarrow>\<^sub>D Q) \<longrightarrow>\<^sub>D (P \<longrightarrow>\<^sub>D R) \<longrightarrow>\<^sub>D (P \<longrightarrow>\<^sub>D Q \<and>\<^sub>D R)" 
    by (simp add:  pdl_taut)
  thus ?thesis by (rule pdl_mp[THEN pdl_mp])
qed

lemma pdl_eq_iff: "\<lbrakk> P = Q \<rbrakk> \<Longrightarrow> \<turnstile> P \<longleftrightarrow>\<^sub>D Q"
by (simp only: pdl_taut Valid_Ret)


lemma pdl_iff_sym: "\<turnstile> P \<longleftrightarrow>\<^sub>D Q \<Longrightarrow> \<turnstile> Q \<longleftrightarrow>\<^sub>D P"
by (simp only: pdl_taut Valid_Ret)

lemma pdl_imp_wk: "\<turnstile> P \<Longrightarrow> \<turnstile> Q \<longrightarrow>\<^sub>D P"
proof -
  assume "\<turnstile> P"
  have "\<turnstile> P \<longrightarrow>\<^sub>D Q \<longrightarrow>\<^sub>D P" by (simp add: pdl_taut)
  thus ?thesis by (rule pdl_mp)
qed


lemma pdl_False_imp: "\<turnstile> Ret False \<longrightarrow>\<^sub>D P"
  by (simp add: pdl_taut)


lemma pdl_imp_trans: "\<lbrakk>\<turnstile> A \<longrightarrow>\<^sub>D B; \<turnstile> B \<longrightarrow>\<^sub>D C\<rbrakk> \<Longrightarrow> \<turnstile> A \<longrightarrow>\<^sub>D C"
proof -
  assume a1: "\<turnstile> A \<longrightarrow>\<^sub>D B" and a2: "\<turnstile> B \<longrightarrow>\<^sub>D C"
  have "\<turnstile> (A \<longrightarrow>\<^sub>D B) \<longrightarrow>\<^sub>D (B \<longrightarrow>\<^sub>D C) \<longrightarrow>\<^sub>D A \<longrightarrow>\<^sub>D C" by (simp only: pdl_taut Valid_Ret)
  from this a1 a2 show ?thesis by (rule pdl_mp[THEN pdl_mp])
qed



text {*  Some applications of the enhanced simplifier, which is now
         capable of proving prop. tautologies immediately *}


lemma "\<turnstile> A \<longrightarrow>\<^sub>D B \<longrightarrow>\<^sub>D A"
by (simp only: pdl_taut Valid_Ret)


lemma "\<turnstile> (P \<and>\<^sub>D Q \<longrightarrow>\<^sub>D R) \<longleftrightarrow>\<^sub>D (P \<longrightarrow>\<^sub>D Q \<longrightarrow>\<^sub>D R)"
by (simp only: pdl_taut Valid_Ret)


lemma "\<turnstile> (P \<longrightarrow>\<^sub>D Q) \<or>\<^sub>D (Q \<longrightarrow>\<^sub>D P)"
  by (simp only: pdl_taut Valid_Ret)


lemma "\<turnstile> (P \<longrightarrow>\<^sub>D Q) \<and>\<^sub>D (\<not>\<^sub>D P \<longrightarrow>\<^sub>D R) \<longleftrightarrow>\<^sub>D (P \<and>\<^sub>D Q \<or>\<^sub>D \<not>\<^sub>D P \<and>\<^sub>D R)"
  by (simp only: pdl_taut Valid_Ret)

end
