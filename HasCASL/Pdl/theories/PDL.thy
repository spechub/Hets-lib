
header {* The Proof Calculus of Monadic Dynamic Logic *}

theory PDL = MonLogic:
text_raw {* \label{sec:pdl-thy} *}


subsection {* Types, Rules and Axioms *}

text {*
 Types, rules and axioms for the box and diamond operators of PDL formulas.
  \label{isa:pdl-calculus}
*}
consts
 Box :: "'a T \<Rightarrow> ('a \<Rightarrow> bool D) \<Rightarrow> bool D"     ("[# _]_" [0, 100] 100)
 Dmd :: "'a T \<Rightarrow> ('a \<Rightarrow> bool D) \<Rightarrow> bool D"     ("\<langle>_\<rangle>_" [0, 100] 100)

text {*
  Syntax translations that let you write e.g.
    @{text "[# x\<leftarrow>p; y\<leftarrow>q](ret (x=y))"}
  for 
    @{text "Box (do {x\<leftarrow>p; y\<leftarrow>q; ret (x,y)}) (\<lambda>(x,y). ret (x=y))"}
  Essentially, these translations collect all bound variables inside the 
  boxes and return them as a tuple. The lambda term that constitutes the 
  second argument of Box will then also take a tuple pattern as its sole
  argument.
*}
nonterminals
  bndseq bndstep
 
syntax (xsymbols)
  "_pdlbox"  :: "[bndseq, bool D] \<Rightarrow> bool D"        ("[# _]_" [0, 100] 100) 
  "_pdldmd"  :: "[bndseq, bool D] \<Rightarrow> bool D"        ("\<langle>_\<rangle>_" [0, 100] 100)
  "_pdlbnd"  :: "[idt, 'a T] \<Rightarrow> bndstep"           ("_\<leftarrow>_")
  "_pdlseq"  :: "[bndstep, bndseq] \<Rightarrow> bndseq"     ("_;/ _")
  ""         :: "bndstep \<Rightarrow> bndseq"               ("_")
  "_pdlin"   :: "[pttrn, bndseq] \<Rightarrow> bndseq"       
  "_pdlout"  :: "[pttrn, bndseq] \<Rightarrow> bndseq"      



translations 
  "_pdlbox (_pdlseq (_pdlbnd x p) r) phi"  
          \<rightharpoonup>  "Box (_pdlseq (_pdlbnd x p) (_pdlin x r)) phi"
  "_pdlbox (_pdlbnd x p) phi"  \<rightharpoonup> "Box p (\<lambda>x. phi)"
  "_pdldmd (_pdlseq (_pdlbnd x p) r) phi"  
          \<rightharpoonup>  "Dmd (_pdlseq (_pdlbnd x p) (_pdlin x r)) phi"
  "_pdldmd (_pdlbnd x p) phi"  \<rightharpoonup> "Dmd p (\<lambda>x. phi)"
  "_pdlin tpl (_pdlseq (_pdlbnd x p) r)"
          \<rightharpoonup>  "_pdlseq (_pdlbnd x p) (_pdlin (tpl, x) r)"
  "_pdlin tpl (_pdlbnd x p)"
          \<rightharpoonup>  "_pdlout (tpl,x) (do {x\<leftarrow>p; ret(tpl,x)})"
  "_pdlseq (_pdlbnd x p) (_pdlout tpl r)"
          \<rightharpoonup>  "_pdlout tpl (do {x\<leftarrow>p; r})"
  "Box (_pdlout tpl r) phi" 
          \<rightharpoonup>  "Box r (\<lambda>tpl. phi)"
  "Dmd (_pdlout tpl r) phi" 
          \<rightharpoonup>  "Dmd r (\<lambda>tpl. phi)"


text {* 
  The axioms of the proof calculus for propositional dynamic logic.
*}

axioms
  pdl_nec:   "(\<forall>x. \<turnstile> P x) \<Longrightarrow> \<turnstile> [# x\<leftarrow>p](P x)"
  pdl_mp_:    "\<lbrakk>\<turnstile> (P \<longrightarrow>\<^sub>D  Q); \<turnstile> P\<rbrakk> \<Longrightarrow> \<turnstile> Q"  -- {* Only repeated here for completeness. *}
 
  pdl_k1:    "\<turnstile> [# x\<leftarrow>p](P x \<longrightarrow>\<^sub>D Q x) \<longrightarrow>\<^sub>D [# x\<leftarrow>p](P x) \<longrightarrow>\<^sub>D [# x\<leftarrow>p](Q x)"
  pdl_k2:    "\<turnstile> [# x\<leftarrow>p](P x \<longrightarrow>\<^sub>D Q x) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(P x) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Q x)"
  pdl_k3B:   "\<turnstile> Ret P \<longrightarrow>\<^sub>D [# x\<leftarrow>p](Ret P)"
  pdl_k3D:   "\<turnstile> \<langle>x\<leftarrow>p\<rangle>(Ret P) \<longrightarrow>\<^sub>D Ret P"
  pdl_k4:    "\<turnstile> \<langle>x\<leftarrow>p\<rangle>(P x \<or>\<^sub>D Q x) \<longrightarrow>\<^sub>D (\<langle>x\<leftarrow>p\<rangle>(P x) \<or>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Q x))"
  pdl_k5:    "\<turnstile> (\<langle>x\<leftarrow>p\<rangle>(P x) \<longrightarrow>\<^sub>D [# x\<leftarrow>p](Q x)) \<longrightarrow>\<^sub>D [# x\<leftarrow>p](P x \<longrightarrow>\<^sub>D Q x)"
  pdl_seqB:  "\<turnstile> [# x\<leftarrow>p; y\<leftarrow>q x](P x y) \<longleftrightarrow>\<^sub>D [# x\<leftarrow>p][# y\<leftarrow>q x](P x y)"
  pdl_seqD:  "\<turnstile> \<langle>x\<leftarrow>p; y\<leftarrow>q x\<rangle>(P x y) \<longleftrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>\<langle>y\<leftarrow>q x\<rangle>(P x y)"
  pdl_ctrB:  "\<turnstile> [# x\<leftarrow>p; y\<leftarrow>q x](P y) \<longrightarrow>\<^sub>D [# y\<leftarrow>do {x\<leftarrow>p; q x}](P y)"
  pdl_ctrD:  "\<turnstile> \<langle>y\<leftarrow>do {x\<leftarrow>p; q x}\<rangle>(P y) \<longrightarrow>\<^sub>D  \<langle>x\<leftarrow>p; y\<leftarrow>q x\<rangle>(P y)"
  pdl_retB:  "\<turnstile> [# x\<leftarrow>ret a](P x) \<longleftrightarrow>\<^sub>D P a"
  pdl_retD:  "\<turnstile> \<langle>x\<leftarrow>ret a\<rangle>(P x) \<longleftrightarrow>\<^sub>D P a"
  pdl_dsefB: "dsef p \<Longrightarrow> \<turnstile> \<Up> (do {a\<leftarrow>p; \<Down> (P a)}) \<longleftrightarrow>\<^sub>D [# a\<leftarrow>p](P a)"
  pdl_dsefD: "dsef p \<Longrightarrow> \<turnstile> \<Up> (do {a\<leftarrow>p; \<Down> (P a)}) \<longleftrightarrow>\<^sub>D \<langle>a\<leftarrow>p\<rangle>(P a)"


text {* A simpler notion of sequencing is often more practical in real programs.
  Essentially this boils down to admitting just one binding within the modal
  operators. *}
axioms
pdl_seqB_simp: "\<turnstile> ( [# x\<leftarrow>p][# y\<leftarrow>q x](P y) ) \<longleftrightarrow>\<^sub>D ( [# y\<leftarrow>do {x\<leftarrow>p; q x}](P y) )"
pdl_seqD_simp: "\<turnstile> ( \<langle>x\<leftarrow>p\<rangle>\<langle>y\<leftarrow>q x\<rangle>(P y) ) \<longleftrightarrow>\<^sub>D ( \<langle>y\<leftarrow>do {x\<leftarrow>p; q x}\<rangle>(P y) )"

text {* 
  For simple monads \cite{SchroederMossakowski:PDL} both rules can be derived from
  axiom @{thm [source] pdl_seqB} (or @{thm [source] pdl_seqD}). Simplicity is
  exploited through the use of the converse rule of @{thm [source] pdl_ctrB}.
*}
lemma "\<turnstile> [# y\<leftarrow>do {x\<leftarrow>p; q x}](P y) \<longrightarrow>\<^sub>D [# x\<leftarrow>p; y\<leftarrow>q x](P y) \<Longrightarrow>
       \<turnstile> ( [# p](\<lambda>x. [# q x]P) ) \<longleftrightarrow>\<^sub>D ( [# do {x\<leftarrow>p; q x}]P )"
  apply(rule pdl_iffI)
  apply(rule pdl_imp_trans)
    apply(rule pdl_iffD2[OF pdl_seqB])
    apply(rule pdl_ctrB)  -- {* dispose of the trailing ret expression *}
  apply(rule pdl_imp_trans)
    apply(assumption)     -- {* this time dispose by the converse of @{thm [source] pdl_ctrB} *}
    apply(rule pdl_iffD1[OF pdl_seqB])
done


text {* Further axioms satisfied by logically regular monads (which we deal with here).
  Cf. \cite[Page 601]{SchroederMossakowski:PDL}
*}
axioms
  pdl_eqB: "\<turnstile> Ret (p = q) \<longrightarrow>\<^sub>D [# x\<leftarrow>p](P x) \<longrightarrow>\<^sub>D [# x\<leftarrow>q](P x)"
  pdl_eqD: "\<turnstile> Ret (p = q) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(P x) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>q\<rangle>(P x)"




subsection {* Derived Rules of Inference *}


text {* `Multiple' modus ponens, provided for convenience. *}
lemmas 
pdl_mp_2x = pdl_mp[THEN pdl_mp] and
pdl_mp_3x = pdl_mp[THEN pdl_mp, THEN pdl_mp]


text {* First half of the classical relationship between diamond and box. *}
lemma dmd_box_rel1: "\<turnstile> ([# x\<leftarrow>p](P x \<longrightarrow>\<^sub>D Ret False) \<longrightarrow>\<^sub>D Ret False) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(P x)" 
  (is "\<turnstile> (?b \<longrightarrow>\<^sub>D Ret False) \<longrightarrow>\<^sub>D ?d")
proof -
  -- {* Show a classically equivalent statement *}
  have "\<turnstile> (?d \<longrightarrow>\<^sub>D Ret False) \<longrightarrow>\<^sub>D ?b" 
  proof -
    -- {* The `usual' axiomatic proof method *}
    have f1: "\<turnstile> ((?d \<longrightarrow>\<^sub>D [# x\<leftarrow>p](Ret False)) \<longrightarrow>\<^sub>D ?b) \<longrightarrow>\<^sub>D 
                (?d \<longrightarrow>\<^sub>D Ret False) \<longrightarrow>\<^sub>D ?b"
      by (simp add: pdl_taut)
    have f2: "\<turnstile> (?d \<longrightarrow>\<^sub>D [# x\<leftarrow>p](Ret False)) \<longrightarrow>\<^sub>D ?b" 
      by (rule pdl_k5)
    from f1 f2 show ?thesis by (rule pdl_mp)
  qed
  thus ?thesis by (simp add: pdl_taut)
qed


text {* \dots and the second half. *}
lemma dmd_box_rel2: "\<turnstile> \<langle>x\<leftarrow>p\<rangle>(P x) \<longrightarrow>\<^sub>D [# x\<leftarrow>p](P x \<longrightarrow>\<^sub>D Ret False) \<longrightarrow>\<^sub>D Ret False"
proof -
  have "\<turnstile> (\<langle>x\<leftarrow>p\<rangle>(Ret False) \<longrightarrow>\<^sub>D Ret False) \<longrightarrow>\<^sub>D 
          ([# x\<leftarrow>p](P x \<longrightarrow>\<^sub>D Ret False) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(P x) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Ret False)) \<longrightarrow>\<^sub>D  
           \<langle>x\<leftarrow>p\<rangle>(P x) \<longrightarrow>\<^sub>D [# x\<leftarrow>p](P x \<longrightarrow>\<^sub>D Ret False) \<longrightarrow>\<^sub>D Ret False"
    by (simp add: pdl_taut)
  from this pdl_k3D pdl_k2 show ?thesis by (rule pdl_mp_2x)
qed


text {* 
  Inheriting the classical theorems from Isabelle/HOL, one also obtains the classical equivalence
  between the diamond and box operator.

  The proofs of @{thm [source] dmd_box_rel1} and @{thm [source] dmd_box_rel2} implicitly employ
  classical arguments through the use of the simplifier, since the algebraization of propositional
  logic behaves classically.
  \label{isa:dmd-box-rel}
*}
theorem dmd_box_rel: "\<turnstile> \<langle>x\<leftarrow>p\<rangle>(P x) \<longleftrightarrow>\<^sub>D \<not>\<^sub>D [# x\<leftarrow>p](\<not>\<^sub>D P x)"
  apply(rule pdl_iffI)
  apply(unfold NotD_def)
  apply(rule dmd_box_rel2)
  apply(rule dmd_box_rel1)
done

text {* Given @{thm [source] dmd_box_rel}, one easily obtains a dual one. *}
theorem box_dmd_rel: "\<turnstile> [# x\<leftarrow>p](P x) \<longleftrightarrow>\<^sub>D \<not>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(\<not>\<^sub>D P x)"
proof -
  have "\<turnstile> ( \<langle>x\<leftarrow>p\<rangle>(\<not>\<^sub>D P x) \<longleftrightarrow>\<^sub>D \<not>\<^sub>D [# x\<leftarrow>p](\<not>\<^sub>D \<not>\<^sub>D P x) ) \<longrightarrow>\<^sub>D 
          ( [# x\<leftarrow>p](P x) \<longleftrightarrow>\<^sub>D \<not>\<^sub>D \<not>\<^sub>D [# x\<leftarrow>p](\<not>\<^sub>D \<not>\<^sub>D P x) ) \<longrightarrow>\<^sub>D 
          ( [# x\<leftarrow>p](P x) \<longleftrightarrow>\<^sub>D \<not>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(\<not>\<^sub>D P x) ) " 
    by (simp add: pdl_taut)
  moreover 
  have "\<turnstile>  \<langle>x\<leftarrow>p\<rangle>(\<not>\<^sub>D P x) \<longleftrightarrow>\<^sub>D \<not>\<^sub>D [# x\<leftarrow>p](\<not>\<^sub>D \<not>\<^sub>D P x)"
    by (rule dmd_box_rel)
  moreover
  have "\<turnstile> [# x\<leftarrow>p](P x) \<longleftrightarrow>\<^sub>D \<not>\<^sub>D \<not>\<^sub>D [# x\<leftarrow>p](\<not>\<^sub>D \<not>\<^sub>D P x)"
    by (simp add: pdl_taut)
  ultimately 
  show ?thesis
    by (rule pdl_mp_2x)
qed



text {* 
  A specialized form of the equality rule @{thm [source] pdl_eqD} that only requires the arguments
  of a program @{term "p"} to be equal.
*}
theorem pdl_eqD_ext: "\<turnstile> Ret (a = b) \<longrightarrow>\<^sub>D \<langle>p a\<rangle>P \<longrightarrow>\<^sub>D \<langle>p b\<rangle>P" (is "\<turnstile> ?ab \<longrightarrow>\<^sub>D ?pa \<longrightarrow>\<^sub>D ?pb")
proof -
  have "\<turnstile> (Ret (a = b) \<longrightarrow>\<^sub>D Ret (p a = p b)) \<longrightarrow>\<^sub>D
          (Ret (p a = p b) \<longrightarrow>\<^sub>D ?pa \<longrightarrow>\<^sub>D ?pb) \<longrightarrow>\<^sub>D
          (?ab \<longrightarrow>\<^sub>D ?pa \<longrightarrow>\<^sub>D ?pb)" by (simp add: pdl_taut)
  moreover 
  have "\<turnstile> Ret (a = b) \<longrightarrow>\<^sub>D Ret (p a = p b)"
  proof (subst impD_Ret_hom[symmetric])
    show "\<turnstile> Ret (a = b \<longrightarrow> p a = p b)"
    proof (rule iffD2[OF Valid_Ret])
      show "a = b \<longrightarrow> p a = p b" by blast
    qed
  qed
  moreover
  have "\<turnstile> Ret (p a = p b) \<longrightarrow>\<^sub>D ?pa \<longrightarrow>\<^sub>D ?pb"
    by (rule pdl_eqD)
  ultimately 
  show ?thesis by (rule pdl_mp_2x)
qed





text {* 
  The following are simple consequences of the axioms above;
  rather than monadic implication, they use Isabelle's meta implication
  (and hence represent rules).
  \label{isa:pdl-derived-rules}
*}


lemma box_imp_distrib: "\<turnstile> [# x\<leftarrow>p](P x \<longrightarrow>\<^sub>D Q x) \<Longrightarrow> \<turnstile> [# x\<leftarrow>p](P x) \<longrightarrow>\<^sub>D [# x\<leftarrow>p](Q x)"
 by(rule pdl_k1[THEN pdl_mp])

lemma dmd_imp_distrib: "\<turnstile> [# x\<leftarrow>p](P x \<longrightarrow>\<^sub>D Q x) \<Longrightarrow> \<turnstile> \<langle>x\<leftarrow>p\<rangle>(P x) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Q x)"
  by (rule pdl_mp[OF pdl_k2])

lemma pdl_box_reg: " \<forall>x. \<turnstile> P x \<longrightarrow>\<^sub>D Q x \<Longrightarrow> \<turnstile> [# x\<leftarrow>p](P x) \<longrightarrow>\<^sub>D [# x\<leftarrow>p](Q x)"
  apply(rule box_imp_distrib)
  apply(rule pdl_nec)
  apply assumption
done

lemma pdl_dmd_reg: " \<forall>x. \<turnstile> P x \<longrightarrow>\<^sub>D Q x \<Longrightarrow> \<turnstile> \<langle>x\<leftarrow>p\<rangle>(P x) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Q x)"
  apply(rule dmd_imp_distrib)
  apply(rule pdl_nec)
  apply assumption
done


theorem pdl_wkB: "\<lbrakk>\<turnstile> [# x\<leftarrow>p](P x); \<forall>x. \<turnstile> P x \<longrightarrow>\<^sub>D Q x\<rbrakk> \<Longrightarrow> \<turnstile> [# x\<leftarrow>p](Q x)"
 apply(rule pdl_mp)
 apply(rule box_imp_distrib)
by(rule pdl_nec)


theorem pdl_wkD: "\<lbrakk>\<turnstile> \<langle>x\<leftarrow>p\<rangle>(P x); \<forall>x. \<turnstile> P x \<longrightarrow>\<^sub>D Q x\<rbrakk> \<Longrightarrow> \<turnstile> \<langle>x\<leftarrow>p\<rangle>(Q x)"
proof -
  assume a: "\<turnstile> \<langle>x\<leftarrow>p\<rangle>(P x)" and b: "\<forall>x. \<turnstile> P x \<longrightarrow>\<^sub>D Q x"
  from b have "\<turnstile> [# x\<leftarrow>p](P x  \<longrightarrow>\<^sub>D Q x)" by (rule pdl_nec)
  hence "\<turnstile> \<langle>x\<leftarrow>p\<rangle>(P x)  \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Q x)" by (rule pdl_k2[THEN pdl_mp])
  from this a show  "\<turnstile> \<langle>x\<leftarrow>p\<rangle>(Q x)" by (rule pdl_mp)
qed

text {* 
  The following rule comes in handy when program sequences occur inside the box.
*}
theorem pdl_plugB: "\<lbrakk>\<turnstile> [# x\<leftarrow>p](P x); \<forall>x. \<turnstile> P x \<longrightarrow>\<^sub>D [# y\<leftarrow>q x](C y)\<rbrakk> \<Longrightarrow> \<turnstile> [# do {x\<leftarrow>p; q x}]C"
  apply(drule pdl_wkB, assumption)
  by (rule pdl_iffD1[OF pdl_seqB_simp, THEN pdl_mp])

theorem pdl_plugD: "\<lbrakk>\<turnstile> \<langle>x\<leftarrow>p\<rangle>(P x); \<forall>x. \<turnstile> P x \<longrightarrow>\<^sub>D \<langle>y\<leftarrow>q x\<rangle>(C y)\<rbrakk> \<Longrightarrow> \<turnstile> \<langle>do {x\<leftarrow>p; q x}\<rangle>C"
  apply(drule pdl_wkD, assumption)
  by (rule pdl_iffD1[OF pdl_seqD_simp, THEN pdl_mp])

lemma box_conj_distrib1: "\<turnstile> [# x\<leftarrow>p](P x) \<and>\<^sub>D [# x\<leftarrow>p](Q x) \<longrightarrow>\<^sub>D [# x\<leftarrow>p](P x \<and>\<^sub>D Q x)"
proof -
  have "\<forall>x. \<turnstile> P x \<longrightarrow>\<^sub>D Q x \<longrightarrow>\<^sub>D P x \<and>\<^sub>D Q x"
  proof
    fix x show "\<turnstile> P x \<longrightarrow>\<^sub>D Q x \<longrightarrow>\<^sub>D P x \<and>\<^sub>D Q x"
      by (simp only: pdl_taut Valid_Ret)
  qed
  hence a2: "\<turnstile> [# x\<leftarrow>p](P x) \<longrightarrow>\<^sub>D [# x\<leftarrow>p](Q x \<longrightarrow>\<^sub>D (P x \<and>\<^sub>D Q x))"
    by (rule pdl_box_reg)
  from this pdl_k1 have "\<turnstile> [# x\<leftarrow>p](P x) \<longrightarrow>\<^sub>D [# x\<leftarrow>p](Q x) \<longrightarrow>\<^sub>D [# x\<leftarrow>p](P x \<and>\<^sub>D Q x)"
    by (rule pdl_imp_trans)
  thus ?thesis by (simp only: pdl_taut)
qed
  

lemma box_conj_distrib2: "\<turnstile> [# x\<leftarrow>p](P x \<and>\<^sub>D Q x) \<longrightarrow>\<^sub>D [# x\<leftarrow>p](P x) \<and>\<^sub>D [# x\<leftarrow>p](Q x)"
proof -
  have " \<forall>x. \<turnstile> P x \<and>\<^sub>D Q x \<longrightarrow>\<^sub>D P x" by (simp add: pdl_taut)
  hence a1: "\<turnstile> [# x\<leftarrow>p] (P x \<and>\<^sub>D Q x) \<longrightarrow>\<^sub>D [# x\<leftarrow>p](P x)" by (rule pdl_box_reg)
  have " \<forall>x. \<turnstile> P x \<and>\<^sub>D Q x \<longrightarrow>\<^sub>D Q x"   by (simp add: pdl_taut)
  hence a2: "\<turnstile> [# x\<leftarrow>p] (P x \<and>\<^sub>D Q x) \<longrightarrow>\<^sub>D [# x\<leftarrow>p](Q x)" by (rule pdl_box_reg)
  let ?P = "[# x\<leftarrow>p](P x)" and ?Q = "[# x\<leftarrow>p](Q x)" and ?PQ = "[# x\<leftarrow>p](P x \<and>\<^sub>D Q x)"
  have "\<turnstile> (?PQ \<longrightarrow>\<^sub>D ?P) \<longrightarrow>\<^sub>D (?PQ \<longrightarrow>\<^sub>D ?Q) \<longrightarrow>\<^sub>D (?PQ \<longrightarrow>\<^sub>D ?P \<and>\<^sub>D ?Q)"
    by (simp only: pdl_taut Valid_Ret)
  from this a1 have "\<turnstile> (?PQ \<longrightarrow>\<^sub>D ?Q) \<longrightarrow>\<^sub>D (?PQ \<longrightarrow>\<^sub>D ?P \<and>\<^sub>D ?Q)" by (rule pdl_mp)
  from this a2 show ?thesis by (rule pdl_mp)
qed

text {* The box operator distributes over (finite) conjunction. *}
theorem box_conj_distrib: "\<turnstile> [# x\<leftarrow>p](P x \<and>\<^sub>D Q x) \<longleftrightarrow>\<^sub>D [# x\<leftarrow>p](P x) \<and>\<^sub>D [# x\<leftarrow>p](Q x)"
  apply (rule pdl_iffI)
  apply (rule box_conj_distrib2)
  apply (rule box_conj_distrib1)
done




text {* Split and join rules for boxes and diamonds. *}
lemma pdl_seqB_split: "\<turnstile> [# do {x\<leftarrow>p; y\<leftarrow>q x; ret (x, y)}](\<lambda>(x, y). P x y) 
                         \<Longrightarrow> \<turnstile> [# p](\<lambda>x. [# q x]P x)"
  by (rule pdl_seqB[THEN pdl_iffD1, THEN pdl_mp])

lemma pdl_seqB_join: "\<turnstile> [# p](\<lambda>x. [# q x]P x) 
                         \<Longrightarrow> \<turnstile> [# do {x\<leftarrow>p; y\<leftarrow>q x; ret (x, y)}](\<lambda>(x, y). P x y)"
  by (rule pdl_seqB[THEN pdl_iffD2, THEN pdl_mp])

lemma pdl_seqD_split: "\<turnstile> \<langle>do {x\<leftarrow>p; y\<leftarrow>q x; ret (x, y)}\<rangle>(\<lambda>(x, y). P x y) 
                         \<Longrightarrow> \<turnstile> \<langle>p\<rangle>(\<lambda>x. \<langle>q x\<rangle>P x)"
  by (rule pdl_seqD[THEN pdl_iffD1, THEN pdl_mp])

lemma pdl_seqD_join: "\<turnstile> \<langle>p\<rangle>(\<lambda>x. \<langle>q x\<rangle>P x) 
                         \<Longrightarrow> \<turnstile> \<langle>do {x\<leftarrow>p; y\<leftarrow>q x; ret (x, y)}\<rangle>(\<lambda>(x, y). P x y)"
  by (rule pdl_seqD[THEN pdl_iffD2, THEN pdl_mp])



text {*
  Working in an axiomatic proof system requires a lot of auxiliary 
  rules; especially the lack of an implication introduction rule 
  (@{thm  impI[no_vars]}) cries for lots of lemmas that are essentially just
  basic lemmas lifted over some premiss.
  \label{isa:pdl-lifted-lemmas}
*}

lemma pdl_wkB_lifted1: "\<lbrakk> \<turnstile> A \<longrightarrow>\<^sub>D [# p]B; \<forall>x. \<turnstile> B x \<longrightarrow>\<^sub>D C x\<rbrakk> \<Longrightarrow> \<turnstile> A \<longrightarrow>\<^sub>D [# p]C"
proof -
  assume a1: "\<turnstile> A \<longrightarrow>\<^sub>D [# p]B" and a2: "\<forall>x. \<turnstile> B x \<longrightarrow>\<^sub>D C x"
  from a2 have "\<turnstile> [# p]B \<longrightarrow>\<^sub>D [# p]C" by (rule pdl_box_reg)
  with a1 show ?thesis by (rule pdl_imp_trans)
qed

lemma pdl_wkD_lifted1: "\<lbrakk> \<turnstile> A \<longrightarrow>\<^sub>D \<langle>p\<rangle>B; \<forall>x. \<turnstile> B x \<longrightarrow>\<^sub>D C x\<rbrakk> \<Longrightarrow> \<turnstile> A \<longrightarrow>\<^sub>D \<langle>p\<rangle>C"
proof -  
  assume a1: "\<turnstile> A \<longrightarrow>\<^sub>D \<langle>p\<rangle>B" and a2: "\<forall>x. \<turnstile> B x \<longrightarrow>\<^sub>D C x"
  from a2 have "\<turnstile> \<langle>p\<rangle>B \<longrightarrow>\<^sub>D \<langle>p\<rangle>C" by (rule pdl_dmd_reg)
  with a1 show ?thesis by (rule pdl_imp_trans)
qed

lemma box_conj_distrib_lifted1: "\<turnstile> (A \<longrightarrow>\<^sub>D [# p](\<lambda>x. P x \<and>\<^sub>D Q x)) \<longleftrightarrow>\<^sub>D ((A \<longrightarrow>\<^sub>D [# p]P) \<and>\<^sub>D (A \<longrightarrow>\<^sub>D [# p]Q))"
proof (rule pdl_iffI)
  show "\<turnstile> (A \<longrightarrow>\<^sub>D [# p](\<lambda>x. P x \<and>\<^sub>D Q x)) \<longrightarrow>\<^sub>D (A \<longrightarrow>\<^sub>D [# p]P) \<and>\<^sub>D (A \<longrightarrow>\<^sub>D [# p]Q)"
  proof -
    have "\<turnstile> ([# p](\<lambda>x. P x \<and>\<^sub>D Q x) \<longrightarrow>\<^sub>D [# p]P \<and>\<^sub>D [# p]Q) \<longrightarrow>\<^sub>D
            (A \<longrightarrow>\<^sub>D [# p](\<lambda>x. P x \<and>\<^sub>D Q x)) \<longrightarrow>\<^sub>D 
             (A \<longrightarrow>\<^sub>D [# p]P) \<and>\<^sub>D (A \<longrightarrow>\<^sub>D [# p]Q)"
      by (simp add: pdl_taut)
    from this box_conj_distrib2 show ?thesis by (rule pdl_mp)
  qed
next
  show "\<turnstile> ((A \<longrightarrow>\<^sub>D [# p]P) \<and>\<^sub>D (A \<longrightarrow>\<^sub>D [# p]Q)) \<longrightarrow>\<^sub>D A \<longrightarrow>\<^sub>D [# p](\<lambda>x. P x \<and>\<^sub>D Q x)"
  proof -
    have "\<turnstile> ([# p]P \<and>\<^sub>D [# p]Q \<longrightarrow>\<^sub>D [# p](\<lambda>x. P x \<and>\<^sub>D Q x)) \<longrightarrow>\<^sub>D
            ((A \<longrightarrow>\<^sub>D [# p]P) \<and>\<^sub>D (A \<longrightarrow>\<^sub>D [# p]Q)) \<longrightarrow>\<^sub>D 
             A \<longrightarrow>\<^sub>D [# p](\<lambda>x. P x \<and>\<^sub>D Q x)"
      by (simp add: pdl_taut)
    from this box_conj_distrib1 show ?thesis by (rule pdl_mp)
  qed
qed

lemma pdl_seqB_lifted1: "\<turnstile> ( A \<longrightarrow>\<^sub>D [# p](\<lambda>x. [# q x]P) ) \<longleftrightarrow>\<^sub>D ( A \<longrightarrow>\<^sub>D [# do {x\<leftarrow>p; q x}]P )"
proof (rule pdl_iffI)
  show "\<turnstile> (A \<longrightarrow>\<^sub>D [# p](\<lambda>x. [# q x]P)) \<longrightarrow>\<^sub>D A \<longrightarrow>\<^sub>D [# do {x\<leftarrow>p; q x}]P"
  proof -
    have "\<turnstile> ([# p](\<lambda>x. [# q x]P) \<longrightarrow>\<^sub>D [# do {x\<leftarrow>p; q x}]P) \<longrightarrow>\<^sub>D
             (A \<longrightarrow>\<^sub>D [# p](\<lambda>x. [# q x]P)) \<longrightarrow>\<^sub>D
             (A \<longrightarrow>\<^sub>D [# do {x\<leftarrow>p; q x}]P)"
      by (simp add: pdl_taut)
    from this pdl_iffD1[OF pdl_seqB_simp] show ?thesis by (rule pdl_mp)
  qed
next
  show "\<turnstile> (A \<longrightarrow>\<^sub>D [# do {x\<leftarrow>p; q x}]P) \<longrightarrow>\<^sub>D A \<longrightarrow>\<^sub>D [# p](\<lambda>x. [# q x]P)"
  proof -
    have "\<turnstile> ([# do {x\<leftarrow>p; q x}]P \<longrightarrow>\<^sub>D [# p](\<lambda>x. [# q x]P)) \<longrightarrow>\<^sub>D
            (A \<longrightarrow>\<^sub>D [# do {x\<leftarrow>p; q x}]P) \<longrightarrow>\<^sub>D
            (A \<longrightarrow>\<^sub>D [# p](\<lambda>x. [# q x]P))"
      by (simp add: pdl_taut)
    from this pdl_iffD2[OF pdl_seqB_simp] show ?thesis by (rule pdl_mp)
  qed
qed

lemma pdl_seqD_lifted1: "\<turnstile> ( A\<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>\<langle>q x\<rangle>P ) \<longleftrightarrow>\<^sub>D (A \<longrightarrow>\<^sub>D \<langle>do {x\<leftarrow>p; q x}\<rangle>P )"
proof (rule pdl_iffI)
  show "\<turnstile> (A \<longrightarrow>\<^sub>D \<langle>p\<rangle>(\<lambda>x. \<langle>q x\<rangle>P)) \<longrightarrow>\<^sub>D A \<longrightarrow>\<^sub>D \<langle>do {x\<leftarrow>p; q x}\<rangle>P"
  proof -
    have "\<turnstile> (\<langle>p\<rangle>(\<lambda>x. \<langle>q x\<rangle>P) \<longrightarrow>\<^sub>D \<langle>do {x\<leftarrow>p; q x}\<rangle>P) \<longrightarrow>\<^sub>D
             (A \<longrightarrow>\<^sub>D \<langle>p\<rangle>(\<lambda>x. \<langle>q x\<rangle>P)) \<longrightarrow>\<^sub>D
             (A \<longrightarrow>\<^sub>D \<langle>do {x\<leftarrow>p; q x}\<rangle>P)"
      by (simp add: pdl_taut)
    from this pdl_iffD1[OF pdl_seqD_simp] show ?thesis by (rule pdl_mp)
  qed
next
  show "\<turnstile> (A \<longrightarrow>\<^sub>D \<langle>do {x\<leftarrow>p; q x}\<rangle>P) \<longrightarrow>\<^sub>D A \<longrightarrow>\<^sub>D \<langle>p\<rangle>(\<lambda>x. \<langle>q x\<rangle>P)"
  proof -
    have "\<turnstile> (\<langle>do {x\<leftarrow>p; q x}\<rangle>P \<longrightarrow>\<^sub>D \<langle>p\<rangle>(\<lambda>x. \<langle>q x\<rangle>P)) \<longrightarrow>\<^sub>D
            (A \<longrightarrow>\<^sub>D \<langle>do {x\<leftarrow>p; q x}\<rangle>P) \<longrightarrow>\<^sub>D
            (A \<longrightarrow>\<^sub>D \<langle>p\<rangle>(\<lambda>x. \<langle>q x\<rangle>P))"
      by (simp add: pdl_taut)
    from this pdl_iffD2[OF pdl_seqD_simp] show ?thesis by (rule pdl_mp)
  qed
qed

  

lemma pdl_plugB_lifted1: "\<lbrakk> \<turnstile> A \<longrightarrow>\<^sub>D [# p]B; \<forall>x. \<turnstile> B x \<longrightarrow>\<^sub>D [# q x]C\<rbrakk> \<Longrightarrow> \<turnstile> A \<longrightarrow>\<^sub>D [# do {x\<leftarrow>p; q x}]C"
proof -
  assume a1: "\<turnstile> A \<longrightarrow>\<^sub>D [# p]B" and a2: "\<forall>x. \<turnstile> B x \<longrightarrow>\<^sub>D [# q x]C"
  from a1 a2 have "\<turnstile> A \<longrightarrow>\<^sub>D [# p](\<lambda>x. [# q x]C)" by (rule pdl_wkB_lifted1)
  thus ?thesis by (rule pdl_iffD1[OF pdl_seqB_lifted1, THEN pdl_mp])
qed

lemma pdl_plugD_lifted1: "\<lbrakk> \<turnstile> A \<longrightarrow>\<^sub>D \<langle>p\<rangle>B; \<forall>x. \<turnstile> B x \<longrightarrow>\<^sub>D \<langle>q x\<rangle>C\<rbrakk> \<Longrightarrow> \<turnstile> A \<longrightarrow>\<^sub>D \<langle>do {x\<leftarrow>p; q x}\<rangle>C"
proof -
  assume a1: "\<turnstile> A \<longrightarrow>\<^sub>D \<langle>p\<rangle>B" and a2: "\<forall>x. \<turnstile> B x \<longrightarrow>\<^sub>D \<langle>q x\<rangle>C"
  from a1 a2 have "\<turnstile> A \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>\<langle>q x\<rangle>C" by (rule pdl_wkD_lifted1)
  thus ?thesis by (rule pdl_iffD1[OF pdl_seqD_lifted1, THEN pdl_mp])
qed


lemma imp_box_conj1: "\<turnstile> A \<longrightarrow>\<^sub>D [# p](\<lambda>x. B x \<and>\<^sub>D C x) \<Longrightarrow> \<turnstile> A \<longrightarrow>\<^sub>D [# p]B"
proof (rule pdl_wkB_lifted1)
  assume "\<turnstile> A \<longrightarrow>\<^sub>D [# p](\<lambda>x. B x \<and>\<^sub>D C x)"
  show "\<turnstile> A \<longrightarrow>\<^sub>D [# p](\<lambda>x. B x \<and>\<^sub>D C x)" .
next
  assume "\<turnstile> A \<longrightarrow>\<^sub>D [# p](\<lambda>x. B x \<and>\<^sub>D C x)"
  show "\<forall>x. \<turnstile> B x \<and>\<^sub>D C x \<longrightarrow>\<^sub>D B x"
  proof 
    fix x show "\<turnstile> B x \<and>\<^sub>D C x \<longrightarrow>\<^sub>D B x" by (simp add: pdl_taut)
  qed
qed


lemma imp_box_conj2: "\<turnstile> A \<longrightarrow>\<^sub>D [# p](\<lambda>x. B x \<and>\<^sub>D C x) \<Longrightarrow> \<turnstile> A \<longrightarrow>\<^sub>D [# p]C"
proof (rule pdl_wkB_lifted1)
  assume "\<turnstile> A \<longrightarrow>\<^sub>D [# p](\<lambda>x. B x \<and>\<^sub>D C x)"
  show "\<turnstile> A \<longrightarrow>\<^sub>D [# p](\<lambda>x. B x \<and>\<^sub>D C x)" .
next
  assume "\<turnstile> A \<longrightarrow>\<^sub>D [# p](\<lambda>x. B x \<and>\<^sub>D C x)"
  show "\<forall>x. \<turnstile> B x \<and>\<^sub>D C x \<longrightarrow>\<^sub>D C x"
  proof 
    fix x show "\<turnstile> B x \<and>\<^sub>D C x \<longrightarrow>\<^sub>D C x" by (simp add: pdl_taut)
  qed
qed



text {* 
  The following lemmas show how one can split and join boxes freely with the help
  of axiom @{thm [source] pdl_seqB_simp}.
*}
lemma pdl_imp_id: "\<turnstile> A \<longrightarrow>\<^sub>D A"
  by (simp add: pdl_taut)

lemma "\<turnstile> [# do {x1\<leftarrow>p1; x2\<leftarrow>p2; x3\<leftarrow>p3; r x1 x2 x3}]P \<longrightarrow>\<^sub>D
         [# x1\<leftarrow>p1][# x2\<leftarrow>p2][# x3\<leftarrow>p3][# r x1 x2 x3]P"
  apply(rule pdl_imp_trans, rule pdl_iffD2[OF pdl_seqB_simp], rule pdl_box_reg ,rule allI)+
  by (simp add: pdl_taut)


lemma "\<turnstile> [# x1\<leftarrow>p1][# x2\<leftarrow>p2][# x3\<leftarrow>p3][# x4\<leftarrow>p4][# r x1 x2 x3 x4]P \<longrightarrow>\<^sub>D
          [# do {x1\<leftarrow>p1; x2\<leftarrow>p2; x3\<leftarrow>p3; x4\<leftarrow>p4; r x1 x2 x3 x4}]P"
  apply(rule pdl_plugB_lifted1, rule pdl_imp_id, rule allI)+
  by (simp add: pdl_taut)

(* Testing ground *)
(*<*)


lemma "\<turnstile> [# x\<leftarrow>ret a](Ret (a = x))"
proof -
  have "\<turnstile> [# x\<leftarrow>ret a](Ret (a = x)) \<longleftrightarrow>\<^sub>D Ret (a = a)"
    by (rule pdl_retB)
  thus ?thesis by (simp add: pdl_taut)
qed

lemma "\<turnstile> P \<Longrightarrow> \<turnstile> [# x\<leftarrow>p; y\<leftarrow>q]P"
  apply(rule pdl_nec)
  apply(rule allI)
  apply(unfold split_def)
  apply(assumption)
done


(* somewhat stupid *)
lemma "(\<forall>x. \<turnstile> Ret (x = c)) \<Longrightarrow> \<turnstile> [# x\<leftarrow>p] (Ret (x = c))"
  apply(rule pdl_nec)
  apply(assumption)
done


(* text {* *}
theorem box_conj_distrib_eq: "(\<turnstile> [# x\<leftarrow>p](P x \<and>\<^sub>D Q x)) = ( \<turnstile> [# x\<leftarrow>p](P x) \<and>\<^sub>D [# x\<leftarrow>p](Q x))"
 apply(rule iffI)
 apply(rule box_conj_distrib2[THEN pdl_mp], assumption)
 apply(rule box_conj_distrib1[THEN pdl_mp], assumption)
done
*)

lemma "\<turnstile> [# a\<leftarrow>p; b\<leftarrow>q](P a b) \<longrightarrow>\<^sub>D [# a\<leftarrow>p][# x\<leftarrow>q](P a x)"
by (rule pdl_iffD1[OF pdl_seqB])



(* 
  Testing the applicability of mpB for typical uses during a program correctness
  proof
*)



lemma "\<lbrakk> \<turnstile> [# x\<leftarrow>p](Ret (x = c)); \<forall>x. (\<turnstile> Ret (x = c) \<longrightarrow>\<^sub>D [# y\<leftarrow>q x](P y))\<rbrakk> \<Longrightarrow> \<turnstile> [# x\<leftarrow>p; y\<leftarrow>q x](P y)"
  apply(rule pdl_seqB_join)
  apply(rule pdl_wkB)
  apply(assumption)
  apply(assumption)
  done



text {*
  Let's see if @{thm [source] pdl_seqB} is suitable for expressing what we intend to
*}


(* Once the principle is understood, one can apply a two-step tactic that solves
  these proofs *)
lemma "\<turnstile> [# x1\<leftarrow>p1; x2\<leftarrow>p2; x3\<leftarrow>p3; x4\<leftarrow>p4](P x1 x2 x3 x4) \<Longrightarrow>
       \<turnstile> [# x1\<leftarrow>p1][# x2\<leftarrow>p2][# x3\<leftarrow>p3][# x4\<leftarrow>p4](P x1 x2 x3 x4)"
  apply(rule pdl_seqB_split, unfold split_def)+
  apply(simp add: mon_ctr)
done

lemma "\<turnstile> [# do {x\<leftarrow>p; y\<leftarrow>q x; f y}] P \<longleftrightarrow>\<^sub>D
         [# do {y\<leftarrow>do {x\<leftarrow>p; q x}; f y}] P"
  apply(simp del: bind_assoc add: mon_ctr pdl_taut)
done

(*>*)
(* End Testing Ground *)

subsection {* Examples *}

text {*
 Examples from \cite[Theorem 6]{HarelKozen02}.
  \label{isa:harel-kozen}
*}

lemma "\<turnstile> \<langle>x\<leftarrow>p\<rangle>(P x) \<or>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Q x) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(P x \<or>\<^sub>D Q x)"
proof -
  have " \<forall>x. \<turnstile> P x \<longrightarrow>\<^sub>D P x  \<or>\<^sub>D Q x" by (simp add: pdl_taut) 
  hence a1: "\<turnstile> \<langle>x\<leftarrow>p\<rangle>(P x) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(P x  \<or>\<^sub>D Q x)" by (rule pdl_dmd_reg)
  have " \<forall>x. \<turnstile> Q x \<longrightarrow>\<^sub>D P x  \<or>\<^sub>D Q x" by (simp add: pdl_taut)
  hence a2: "\<turnstile> \<langle>x\<leftarrow>p\<rangle>(Q x) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(P x  \<or>\<^sub>D Q x)" by (rule pdl_dmd_reg)
  let ?P = "\<langle>x\<leftarrow>p\<rangle>(P x)" and ?Q = "\<langle>x\<leftarrow>p\<rangle>(Q x)" and ?PQ = "\<langle>x\<leftarrow>p\<rangle>(P x \<or>\<^sub>D Q x)"
  have "\<turnstile> (?P \<longrightarrow>\<^sub>D ?PQ) \<longrightarrow>\<^sub>D (?Q \<longrightarrow>\<^sub>D ?PQ) \<longrightarrow>\<^sub>D (?P  \<or>\<^sub>D ?Q \<longrightarrow>\<^sub>D ?PQ)"
    by (simp only: pdl_taut Valid_Ret)
  from this a1 have "\<turnstile> (?Q \<longrightarrow>\<^sub>D ?PQ) \<longrightarrow>\<^sub>D (?P  \<or>\<^sub>D ?Q \<longrightarrow>\<^sub>D ?PQ)" by (rule pdl_mp)
  from this a2 show ?thesis  by (rule pdl_mp)
qed

lemma "\<turnstile> \<langle>x\<leftarrow>p\<rangle>(P x) \<and>\<^sub>D [# x\<leftarrow>p](Q x)  \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(P x \<and>\<^sub>D Q x)"
proof -
  have " \<forall>x.  \<turnstile> Q x \<longrightarrow>\<^sub>D P x \<longrightarrow>\<^sub>D P x \<and>\<^sub>D Q x" by (simp add: pdl_taut)
  hence "\<turnstile> [# x\<leftarrow>p](Q x)  \<longrightarrow>\<^sub>D [# x\<leftarrow>p](P x  \<longrightarrow>\<^sub>D P x \<and>\<^sub>D Q x)"
    by (rule pdl_box_reg)
  moreover have "\<turnstile> [# x\<leftarrow>p](P x \<longrightarrow>\<^sub>D P x \<and>\<^sub>D Q x) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(P x) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(P x \<and>\<^sub>D Q x)"
    by (rule pdl_k2)
  ultimately have "\<turnstile> [# x\<leftarrow>p](Q x) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(P x) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(P x \<and>\<^sub>D Q x)"
    by (rule pdl_imp_trans)  -- {* transitivity of implication *}
  thus ?thesis by (simp only: pdl_taut)
qed

lemma pdl_conj_dmd: "\<turnstile> \<langle>x\<leftarrow>p\<rangle>(P x \<and>\<^sub>D Q x) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(P x) \<and>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Q x)"
proof -
  -- {* first proving the `P-part' *}
  have dp: "\<turnstile> \<langle>x\<leftarrow>p\<rangle>(P x \<and>\<^sub>D Q x) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(P x)"
  proof -
    have fa: "\<forall>x. \<turnstile> P x \<and>\<^sub>D Q x \<longrightarrow>\<^sub>D P x" by (simp add: pdl_taut)
    thus ?thesis
    proof - 
      assume "\<forall>x. \<turnstile> P x \<and>\<^sub>D Q x \<longrightarrow>\<^sub>D P x"
      thus "\<turnstile> \<langle>x\<leftarrow>p\<rangle>(P x \<and>\<^sub>D Q x) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(P x)" by (rule pdl_dmd_reg)
    qed
  qed
  -- {* the same for Q *}
  moreover 
  have dq: "\<turnstile> \<langle>x\<leftarrow>p\<rangle>(P x \<and>\<^sub>D Q x) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Q x)"
  proof -
    have fa: "\<forall>x. \<turnstile> P x \<and>\<^sub>D Q x \<longrightarrow>\<^sub>D Q x"  by (simp add: pdl_taut)
    thus ?thesis
    proof - 
      assume "\<forall>x. \<turnstile> P x \<and>\<^sub>D Q x \<longrightarrow>\<^sub>D Q x"
      thus "\<turnstile> \<langle>x\<leftarrow>p\<rangle>(P x \<and>\<^sub>D Q x) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Q x)" by (rule pdl_dmd_reg)
    qed
  qed
  -- {* Now assemble the results to arrive at the main thesis *}
  ultimately show ?thesis by (rule  pdl_conjI_lifted)
qed

lemma "\<turnstile> [# x\<leftarrow>p](P x) \<or>\<^sub>D [# x\<leftarrow>p](Q x) \<longrightarrow>\<^sub>D [# x\<leftarrow>p](P x \<or>\<^sub>D Q x)"
proof -
  have " \<forall>x. \<turnstile> P x \<longrightarrow>\<^sub>D P x  \<or>\<^sub>D Q x"  by (simp add: pdl_taut)
  hence a1: "\<turnstile> [# x\<leftarrow>p](P x) \<longrightarrow>\<^sub>D [# x\<leftarrow>p](P x  \<or>\<^sub>D Q x)" by (rule pdl_box_reg)
  have " \<forall>x. \<turnstile> Q x \<longrightarrow>\<^sub>D P x  \<or>\<^sub>D Q x" by (simp add: pdl_taut)
  hence a2: "\<turnstile> [# x\<leftarrow>p](Q x) \<longrightarrow>\<^sub>D [# x\<leftarrow>p](P x  \<or>\<^sub>D Q x)" by (rule pdl_box_reg)
  let ?P = "[# x\<leftarrow>p](P x)" and ?Q = "[# x\<leftarrow>p](Q x)" and ?PQ = "[# x\<leftarrow>p](P x  \<or>\<^sub>D Q x)"
  have "\<turnstile> (?P \<longrightarrow>\<^sub>D ?PQ) \<longrightarrow>\<^sub>D (?Q \<longrightarrow>\<^sub>D ?PQ) \<longrightarrow>\<^sub>D (?P  \<or>\<^sub>D ?Q \<longrightarrow>\<^sub>D ?PQ)"
    by (simp only: pdl_taut Valid_Ret)
  from this a1 a2 show ?thesis by (rule pdl_mp_2x)
qed

end
