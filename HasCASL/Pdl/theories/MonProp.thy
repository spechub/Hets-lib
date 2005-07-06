(*
   Theory MonProp proves the necessary properties (copyability, discardability,
   deterministic side-effect freeness) of monadic programs to finally introduce
   the subtype ('a D) of ('a T) of dsef programs. 
   Furthermore, it introduces lifting operations liftM, liftM2, liftM3, ap ($$),
   and provides Theorem dsef_ret_ap, which is needed in the definition of the
   monadic logical connectives.
*)


header {* Basic Notions of Monadic Programs *}

theory MonProp = Monads:


subsection {* Discardability and Copyability *}

text {*
  Properties of monadic programs which are needed for the further development,
  e.g. for the definition of a subtype @{text "'a D"} of deterministically
  side-effect free (@{text "dsef"}) programs.
*}
constdefs
  -- {* Discardable programs *}
  dis :: "'a T \<Rightarrow> bool"
  "dis(p) \<equiv> (do {x\<leftarrow>p; ret()}) = ret ()"
  -- {* Copyable programs *}
  cp  :: "'a T \<Rightarrow> bool"
  "cp(p) \<equiv> (do {x\<leftarrow>p; y\<leftarrow>p; ret(x,y)}) = (do {x\<leftarrow>p; ret(x,x)})"
  -- {* @{text "dsef"} programs are @{term "cp"} and @{term "dis"} and
        commute with all such programs *}
  dsef :: "'a T \<Rightarrow> bool"
  "dsef(p) \<equiv> cp(p) \<and> dis(p) \<and> (\<forall>q::bool T. cp(q) \<and> dis(q) \<longrightarrow> 
                                    cp(do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)}))"


lemma dsef_cp: "dsef p \<Longrightarrow> cp p"
  apply(unfold dsef_def)
by blast

lemma dsef_dis: "dsef p \<Longrightarrow> dis p"
  apply(unfold dsef_def)
by blast

text {*
  This is Lemma 4.5 of \cite{SchroederMossakowski:PDL} that allows us to actually discard
  discardable programs in front of arbitrary programs.
*}

lemma dis_left: "dis(p) \<Longrightarrow> do {p; q} = q"
proof -
  assume d: "dis(p)"
  have "do {p; q} = do {p; ret (); q}"
    by (simp add: seq_def)
  also from d have "\<dots> = do {ret (); q}"
    by (simp add: dis_def seq_def del: ret_lunit)
  also have "\<dots> = q" by (simp add: seq_def)
  finally show ?thesis .
qed

text {* 
  Essentially the same as @{thm [source] dis_left}, but expressed
  with binding.
*}
lemma dis_left2: "dis p \<Longrightarrow> do {x\<leftarrow>p; q} = q"
proof -
  assume a: "dis p"
  have "do {x\<leftarrow>p; q} = do {p; q}" by (simp only: seq_def)
  also from a have "\<dots> = q" by (rule dis_left)
  finally show ?thesis .
qed


text {* 
  This is Lemma 4.22 of \cite{SchroederMossakowski:PDL} which allows us to insert or remove
  copies of @{term "cp"} programs whose result values may be substituted for each other
  in the following program sequence @{term "r"}.
*}

lemma cp_arb: "cp p \<Longrightarrow> do {x\<leftarrow>p; y\<leftarrow>p; r x y} = do {x\<leftarrow>p; r x x}"
proof (unfold cp_def)
  assume c: " do {x\<leftarrow>p; y\<leftarrow>p; ret (x, y)} = do {x\<leftarrow>p; ret (x, x)}"
  have "do {x\<leftarrow>p; y\<leftarrow>p; r x y} = do {x\<leftarrow>p; y\<leftarrow>p; z\<leftarrow>ret(x,y); r (fst z) (snd z)}"
    by (simp)
  also have "\<dots> = do {z\<leftarrow>do {x\<leftarrow>p; y\<leftarrow>p; ret(x,y)}; r (fst z) (snd z)}"
    by (simp add: mon_ctr)
  also from c have "\<dots> = do {z\<leftarrow>do {x\<leftarrow>p; ret(x,x)}; r (fst z) (snd z)}"
    by simp
  also have "\<dots> = do {x\<leftarrow>p; z\<leftarrow>ret (x,x); r (fst z) (snd z)}"
    by (simp add: mon_ctr)
  also have "\<dots> = do {x\<leftarrow>p; r x x}"
    by simp
  finally show ?thesis .
qed


text {*
  This is Lemma 4.23 of \cite{SchroederMossakowski:PDL}, asserting a weak composability of copyable programs.
  It is generally not the case that sequences of copyable programs constitute
  a copyable program.
*}

lemma weak_cp_seq: "cp p \<Longrightarrow> cp (do {x\<leftarrow>p; ret (f x)})"
proof -
  assume c: "cp p"
  let ?q = "do {x\<leftarrow>p; ret (f x)}"
  have "do {u\<leftarrow>?q; v\<leftarrow>?q; ret(u,v)} = do {x\<leftarrow>p; u\<leftarrow>ret (f x); y\<leftarrow>p; v\<leftarrow>ret (f y); ret(u,v)}"
    by (simp add: mon_ctr)
  also have "\<dots> = do {x\<leftarrow>p; y\<leftarrow>p; ret (f x, f y)}"
    by simp
  also from c  have "\<dots> = do {x\<leftarrow>p; ret (f x, f x)}"
    by (simp add: cp_arb)
  also have "\<dots> = do {x\<leftarrow>p; u\<leftarrow>ret (f x); ret(u,u)}"
    by simp
  also have "\<dots> = do {u\<leftarrow>?q; ret(u,u)}"
    by (simp add: mon_ctr)
  finally show ?thesis by (simp add: cp_def)
qed


text {* 
  One can reduce the copyability of a program of a certain form to a simpler
  form. 
*}
lemma cp_seq_ret: "cp (do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)}) \<Longrightarrow> cp (do {x\<leftarrow>p; y\<leftarrow>q; ret (f x y)})"
proof -
  assume "cp (do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)})"
  hence c: "cp (do {u\<leftarrow>do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)}; ret (f (fst u) (snd u))})" 
    by (simp add: weak_cp_seq)
  have "do {u\<leftarrow>do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)}; ret (f (fst u) (snd u))}
        = do {x\<leftarrow>p; y\<leftarrow>q; ret (f x y)}"
    by (simp add: mon_ctr)
  with c show ?thesis by simp
qed


text {*
  We also have a weak notion of stability under sequencing for @{term "dsef"}
  programs.
*}
lemma weak_dis_seq: "dis p \<Longrightarrow> dis (do {x\<leftarrow>p; ret (f x)})"
proof -
  assume d: "dis p"
  have "do {z\<leftarrow>do {x\<leftarrow>p; ret (f x)}; ret ()} = do {x\<leftarrow>p; z\<leftarrow>ret (f x); ret ()}"
    by (simp only: mon_ctr)
  also have "\<dots> = do {x\<leftarrow>p; ret()}"
    by simp
  also from d have "\<dots> = ret ()" by (simp add: dis_def)
  finally show ?thesis by (simp add: dis_def)
qed


text {*
  The following lemmas @{text "commute_X_Y"} are proofs of the Propositions 
  4.24 of \cite{SchroederMossakowski:PDL} where @{text "X"} is the respective premiss
  and @{text "Y"} is the conclusion.
*}


lemma commute_1_2: "\<lbrakk>cp q; cp p; dis q; dis p\<rbrakk> \<Longrightarrow> cp (do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)})
                    \<Longrightarrow> do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)} = do {y\<leftarrow>q; x\<leftarrow>p; ret(x,y)}"
proof -
  assume a: "cp q" "cp p" "dis q" "dis p"
  let ?s = "do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)}"
  from a have ds: "dis ?s" by (simp add: dis_def dis_left mon_ctr)
  assume c: "cp (do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)})"
  have "?s = do {z\<leftarrow>?s; ret z}" by (rule ret_runit[symmetric])
  also have "\<dots> = do {z\<leftarrow>?s; ret (fst z, snd z)}" by simp
  also from c have "\<dots> = do {w\<leftarrow>?s; z\<leftarrow>?s; ret (fst z, snd w)}" by (simp add: cp_arb)
  also have "\<dots> = do {u\<leftarrow>p; v\<leftarrow>q; w\<leftarrow>ret(u,v); x\<leftarrow>p; y\<leftarrow>q; z\<leftarrow>ret(x,y); ret(fst z, snd w)}"
    by (simp only:mon_ctr)
  also have "\<dots> = do {p; v\<leftarrow>q; x\<leftarrow>p; q; ret(x,v)}" by (simp add: seq_def)
  also from a have "\<dots> = do {v\<leftarrow>q; x\<leftarrow>p; ret(x,v)}" by (simp only: dis_left)
  finally show ?thesis .
qed


lemma commute_2_3: "\<lbrakk>cp q; cp p; dis q; dis p\<rbrakk> \<Longrightarrow> 
                    do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)} = do {y\<leftarrow>q; x\<leftarrow>p; ret(x,y)} \<Longrightarrow>
                    \<forall>r. do {x\<leftarrow>p; y\<leftarrow>q; r x y} = do {y\<leftarrow>q; x\<leftarrow>p; r x y}"
proof
  fix r
  assume a: "cp q" "cp p" "dis q" "dis p"
  assume b: "do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)} = do {y\<leftarrow>q; x\<leftarrow>p; ret(x,y)}"
  have "do {x\<leftarrow>p; y\<leftarrow>q; r x y} = do {x\<leftarrow>p; y\<leftarrow>q; z\<leftarrow>ret(x,y); r (fst z) (snd z)}"
    by simp
  also have "\<dots> = do {z\<leftarrow>do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)}; r (fst z) (snd z)}"
    by (simp only: mon_ctr)
  also from b have "\<dots> = do {z\<leftarrow>do {y\<leftarrow>q; x\<leftarrow>p; ret(x,y)}; r (fst z) (snd z)}"
    by simp
  also have "\<dots> = do {y\<leftarrow>q; x\<leftarrow>p; r x y}" by (simp add: mon_ctr)
  finally show "do {x\<leftarrow>p; y\<leftarrow>q; r x y} = do {y\<leftarrow>q; x\<leftarrow>p; r x y}" .
qed


(*<*)
(* Once more, type related unification problems prevent us from stating a
   formula without type restrictions *)
lemma " \<forall>(r::'a T). (do {p; r} = do {q; r}) \<Longrightarrow> 
           do {x\<leftarrow>r2; p; ret x :: 'a T} = do {x\<leftarrow>r2; q; ret x}"
by(simp add: seq_def)
(*>*)

text {* In this case, type annotations are necessary, since we cannot
  quantify over types of programs. The type for @{text "r"} given here
  is needed for the proof to go through.
*}
lemma commute_3_1: "\<lbrakk>cp q; cp p; dis q; dis p\<rbrakk> \<Longrightarrow>
                    \<forall>r::'a \<Rightarrow> 'b \<Rightarrow> (('a*'b)*('a*'b)) T.
                      do {x\<leftarrow>p; y\<leftarrow>q; r x y} = do {y\<leftarrow>q; x\<leftarrow>p; r x y} \<Longrightarrow>
                    cp (do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)::('a * 'b) T})"
proof -
  let ?s = "do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)}"
  assume a: "cp q" "cp p" "dis q" "dis p"
  assume c: "\<forall>r::'a \<Rightarrow> 'b \<Rightarrow> (('a*'b)*('a*'b)) T. 
                do {x\<leftarrow>p; y\<leftarrow>q; r x y} = do {y\<leftarrow>q; x\<leftarrow>p; r x y}"
  have "do {w\<leftarrow>?s; z\<leftarrow>?s; ret (w,z)} = do {u\<leftarrow>p; v\<leftarrow>q; x\<leftarrow>p; y\<leftarrow>q; ret((u,v),(x,y))}"
    by (simp add: mon_ctr)
  also from c have "\<dots> = do {u\<leftarrow>p; x\<leftarrow>p; v\<leftarrow>q; y\<leftarrow>q; ret((u,v),(x,y))}" by simp
  also from a have "\<dots> = do {u\<leftarrow>p; v\<leftarrow>q; ret((u,v),(u,v))}" by (simp only: cp_arb)
  also have "\<dots> = do {w\<leftarrow>?s; ret(w,w)}" by (simp add:mon_ctr)
  finally show ?thesis by (simp add: cp_def)
qed


lemma commute_1_3: "\<lbrakk>cp q; cp p; dis q; dis p\<rbrakk> \<Longrightarrow>
                    cp (do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)}) \<Longrightarrow>
                    \<forall>r. do {x\<leftarrow>p; y\<leftarrow>q; r x y} = do {y\<leftarrow>q; x\<leftarrow>p; r x y}"
  -- {* More or less just transitivity of implication *}
  apply(rule commute_2_3)
  apply(simp_all)
  apply(rule commute_1_2)
  apply(simp_all)
done



text {*
  This weird axiom is needed to obtain the commutativity of an arbitrary program
  from its commuting  with all @{typ "bool"} valued programs.
*}
axioms
  commute_bool_arb: "(\<forall>q::bool T. cp(q) \<and> dis(q) \<longrightarrow> cp(do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)})) \<Longrightarrow>
                   (\<forall>q. cp(q) \<and> dis(q) \<longrightarrow> cp(do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)}))"



text {* In order to introduce the subtype of @{term "dsef"} programs, we
  must prove it is not empty.
*}
theorem dsef_ret [simp]: "dsef (ret x)"
proof (unfold dsef_def)
  have "cp (ret x)" by (simp add: cp_def)
  moreover have "dis (ret x)" by (simp add: dis_def)
  moreover have "(\<forall>q. cp q \<and> dis q \<longrightarrow> cp (do {x\<leftarrow>ret x; y\<leftarrow>q; ret (x, y)}))"
    by (simp add: weak_cp_seq)
  ultimately show "cp (ret x) \<and> dis (ret x) \<and> 
                   (\<forall>q. cp q \<and> dis q \<longrightarrow> cp (do {x\<leftarrow>ret x; y\<leftarrow>q; ret (x, y)}))"
    by blast
qed


subsection {* Introducing the Subtype of \emph{dsef} Programs *}

text {*
  Introducing the subtype @{text "'a D"} of @{typ "'a T"} comprising the 
@{term "dsef"} programs;
  since Isabelle lacks true subtyping, it is simply declared as a new type
  with coercion functions 
    @{text "Rep_Dsef :: 'a D \<Rightarrow> 'a T"}
  and 
    @{text "Abs_Dsef :: 'a T \<Rightarrow> 'a D"}
  where @{text "Abs_Dsef p"} is of course only sensibly defined if @{term "dsef p"}
   holds.
*}

typedef (Dsef) ('a) D = "{p::'a T. dsef p}"
  apply(rule_tac x = "ret x" in exI)
  apply(blast intro: dsef_ret)
done


text {* 
  Minimizing the clutter caused by @{term "Abs_Dsef"} and @{term "Rep_Dsef"}
*}
syntax
  "_absdsef"            :: "'a T \<Rightarrow> 'a D"      ("\<Up> _" [200] 199)
  "_repdsef"            :: "'a D \<Rightarrow> 'a T"      ("\<Down> _" [200] 199)
translations
  "\<Up> p"      \<rightleftharpoons>     "Abs_Dsef p"
  "\<Down> p"      \<rightleftharpoons>     "Rep_Dsef p"



text {* All representatives of terms of type @{typ "'a D"} are dsef and thus in 
        particular discardable and copyable. *}

lemma dsef_Rep_Dsef [simp]: "dsef (\<Down> a)"
proof (induct a rule: Abs_Dsef_induct)
  fix a
  assume "a : Dsef"
  thus "dsef (\<Down> (\<Up> a))"
    by (simp add: Abs_Dsef_inverse Dsef_def)
qed

lemma dis_Rep_Dsef: "dis (\<Down> a)"
  apply(insert dsef_Rep_Dsef[of a])
  apply(unfold dsef_def)
  apply(blast)
done

lemma cp_Rep_Dsef: "cp (\<Down> a)"
  apply(insert dsef_Rep_Dsef[of a])
  apply(unfold dsef_def)
  apply(blast)
done



text {*
  \textbf{Convention:} We will denote functions in @{term "D"} that are simply
abstracted versions
  of appropriate functions in @{term "T"} by the same name with the first
  letter capitalised.
*}
constdefs 
  Ret :: "'a \<Rightarrow> 'a D"
  "Ret x \<equiv> \<Up> (ret x)"


lemma Ret_ret: "\<Down> (Ret x) = ret x"
proof -
  have "\<Down> (Ret x) = \<Down> (\<Up> (ret x))" by (simp only: Ret_def)
  also have "\<dots> = ret x" by (simp add: Dsef_def Abs_Dsef_inverse)
  finally show ?thesis .
qed



text {*
  Lifting operations will allow us to introduce monadic connectives @{text "\<and>, \<or>"}, etc.
  by simply lifting the HOL ones. Theorem @{thm [source] "dsef_ret"} will
  assert these to be @{term "dsef"} (see below).  
*} 

constdefs
 liftM :: "['a \<Rightarrow> 'b, 'a T] \<Rightarrow> 'b T"
 "liftM f p \<equiv> do {x \<leftarrow> p; ret (f x)}"
 liftM2 :: "['a \<Rightarrow> 'b \<Rightarrow> 'c, 'a T, 'b T] \<Rightarrow> 'c T"
 "liftM2 f p q \<equiv> do {x \<leftarrow> p; y \<leftarrow> q; ret (f x y)}"
 liftM3 :: "['a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd, 'a T, 'b T, 'c T] \<Rightarrow> 'd T"
 "liftM3 f p q r \<equiv> do {x \<leftarrow> p; y \<leftarrow> q; z \<leftarrow> r; ret (f x y z)}"
 -- {* The most general form of lifting; the above may be expressed by it *}
 ap :: "[('a \<Rightarrow> 'b) T, 'a T] \<Rightarrow> 'b T"         (infixl "$$" 100)
 "ap m p \<equiv> do {f \<leftarrow> m; x \<leftarrow> p; ret (f x)}"

lemma liftM_ap: "liftM f x = (ret f $$ x)"
by (simp add: ap_def liftM_def)

lemma liftM2_ap: "liftM2 f x y = (ret f $$ x $$ y)"
by (simp add: mon_ctr ap_def liftM2_def)

lemma liftM3_ap: "liftM3 f x y z = ret f $$ x $$ y $$ z"
 by(simp add: mon_ctr ap_def liftM3_def)




theorem dsef_ret_ap: "dsef p \<Longrightarrow> dsef (ret f $$ p)"
  apply(simp add: ap_def dsef_def)
  apply(clarify)
  apply(rule conjI)
  apply(erule weak_cp_seq)
  apply(rule conjI)
  apply(erule weak_dis_seq)
  apply(clarify)
  apply(drule_tac x = q in spec)
  apply(simp add: mon_ctr weak_cp_seq)
  apply(simp (no_asm_simp) only: cp_seq_ret)
done


text {* @{term "dsef"} programs may be swapped. *}
lemma commute_dsef: "\<lbrakk>dsef p; dsef q\<rbrakk> \<Longrightarrow> 
                      \<forall>r. do {x\<leftarrow>p; y\<leftarrow>q; r x y} = do {y\<leftarrow>q; x\<leftarrow>p; r x y}"
  apply(rule commute_1_3)
  apply(simp_all add: dsef_def)
  apply(clarify)
  apply(drule commute_bool_arb)
  apply(drule_tac x = q in spec)
by(blast)
  
lemma commute_bool: "\<lbrakk>dsef p; cp (q::bool T); dis q\<rbrakk> \<Longrightarrow> 
                     \<forall>r. do {x\<leftarrow>p; y\<leftarrow>q; r x y} = do {y\<leftarrow>q; x\<leftarrow>p; r x y}"
by (rule commute_1_3, simp_all add: dsef_def)
  

text {*
  A formalisation of the essential fact that @{term "dsef"} programs
  are actually stable under sequencing; this has only been proposed
  in \cite{SchroederMossakowski:PDL}, but has not been shown.
*}
theorem dsef_seq: "\<lbrakk>dsef p; \<forall>x. dsef (q x)\<rbrakk> \<Longrightarrow> dsef (do {x\<leftarrow>p; q x})"
proof -
  assume a1: "dsef p" 
  assume a2: "\<forall>x. dsef (q x)"
  from a1 have disp: "dis p" by (rule dsef_dis)
  from a1 have cpp: "cp p" by (rule dsef_cp)
  from a2 have disq: "\<forall>x. dis (q x)" by (unfold dsef_def, blast)
  from a2 have cpq: "\<forall>x. cp (q x)" by (unfold dsef_def, blast)
  let ?s = "do {x\<leftarrow>p; q x}"
  -- {* The proof proceeds in three parts, each one asserting some property stated
        in the definition of @{text "dsef"} terms. Firstly, @{text "dsef"} terms 
        are discardable. *}
  have "dis ?s"
  proof -
    have "do {x\<leftarrow>?s; ret ()} = do {x\<leftarrow>p; q x; ret ()}" by (simp add: seq_def)
    also from disp disq 
    have "\<dots> = ret ()" by (simp add: dis_left dis_left2)
    finally show ?thesis by (simp add: dis_def)
  qed
  -- {* @{text "dsef"} terms are also copyable. We unfold the definition and prove
        the required equation directly. *}
  moreover have "cp ?s"
  proof -
    have "do {x\<leftarrow>?s; y\<leftarrow>?s; ret (x,y)} = 
      do {u\<leftarrow>p; x\<leftarrow>q u; v\<leftarrow>p; y\<leftarrow>q v; ret (x,y)}"
      by simp
    also have "\<dots> = do {u\<leftarrow>p; v\<leftarrow>p; x\<leftarrow>q u; y\<leftarrow>q v; ret (x,y)}"
    proof -
      -- {* This swapping step is a bit more difficult; we have to assist 
            the simplifier by the following general statement: *}
      have "\<forall>u. do {x\<leftarrow>q u; v\<leftarrow>p; y\<leftarrow>q v; ret (x,y)} = do {v\<leftarrow>p; x\<leftarrow>q u; y\<leftarrow>q v; ret (x,y)}"
	(is "\<forall>u. ?A u = ?B u")
      proof 
	fix u
	from a2 have "dsef (q u)" by (rule spec)
	from this a1 
	have "\<forall>r::'b\<Rightarrow>'a\<Rightarrow>('b*'b) T. do {x\<leftarrow>q u; v\<leftarrow>p; r x v} = do {v\<leftarrow>p; x\<leftarrow>q u; r x v}"
	  by (rule commute_dsef)
	thus "?A u = ?B u" by (rule spec)
      qed
      thus ?thesis by simp
    qed
    also from cpp cpq have "\<dots> = do {u\<leftarrow>p; x\<leftarrow>q u; ret (x,x)}"
      by (simp add: cp_arb)
    finally show ?thesis by (simp add: cp_def)
  qed
  -- {* The final step is that @{term "?s"} commutes with bool-valued programs: *}
  moreover have "\<forall>q::bool T. cp q \<and> dis q \<longrightarrow> cp (do {x\<leftarrow>?s; y\<leftarrow>q; ret(x,y)})"
  proof
    -- {* The proof is carried out by a so called raw proof block, where the succeeding
          application of blast spares us having to do the trivial proof steps. *}
    fix qa
    { assume cpqa: "cp (qa::bool T)"
      assume disqa: "dis qa"
      have "cp (do {x\<leftarrow>do{u\<leftarrow>p; q u}; y\<leftarrow>qa; ret (x, y)})"
      proof -
	let ?w = "do {x\<leftarrow>do{u\<leftarrow>p; q u}; y\<leftarrow>qa; ret (x, y)}"
	have "do {x\<leftarrow>?w; y\<leftarrow>?w; ret (x,y)} = 
              do {u\<leftarrow>p; x\<leftarrow>q u; y\<leftarrow>qa; u'\<leftarrow>p; x'\<leftarrow>q u'; y'\<leftarrow>qa; ret((x,y),(x',y'))}"
	  by (simp del: bind_assoc add: mon_ctr)
	also from a1 cpqa disqa 
	have "\<dots> = do {u\<leftarrow>p; x\<leftarrow>q u; u'\<leftarrow>p; y\<leftarrow>qa; x'\<leftarrow>q u'; y'\<leftarrow>qa; ret((x,y),(x',y'))}"
	  by (simp add: commute_bool)
	also from a1 a2
	have "\<dots> = do {u\<leftarrow>p; u'\<leftarrow>p; x\<leftarrow>q u; y\<leftarrow>qa; x'\<leftarrow>q u'; y'\<leftarrow>qa; ret((x,y),(x',y'))}"
	proof - 
	  -- {* This fact is needed to help the simplifier solve the goal *}
	  have "\<forall>u. do {x\<leftarrow>q u; u'\<leftarrow>p; y\<leftarrow>qa; x'\<leftarrow>q u'; y'\<leftarrow>qa; ret((x,y),(x',y'))} =
	            do {u'\<leftarrow>p; x\<leftarrow>q u; y\<leftarrow>qa; x'\<leftarrow>q u'; y'\<leftarrow>qa; ret((x,y),(x',y'))}"
	    (is "\<forall>u. ?A u = ?B u")
	  proof
	    fix u
	    from a2 have "dsef (q u)" by (rule spec)
	    from this a1 have "\<forall>r. do {x\<leftarrow>q u; u'\<leftarrow>p; r x u'} = do {u'\<leftarrow>p; x\<leftarrow>q u; r x u'}"
	      by (rule commute_dsef)
	    thus "?A u = ?B u" by (rule spec)
	  qed
	  thus ?thesis by simp
	qed
	also from a2 cpqa disqa 
	have "\<dots> = do {u\<leftarrow>p; u'\<leftarrow>p; x\<leftarrow>q u; x'\<leftarrow>q u'; y\<leftarrow>qa; y'\<leftarrow>qa; ret((x,y),(x',y'))}"
	  by (simp add: commute_bool)
	also from cpp cpq cpqa have "\<dots> = do {u\<leftarrow>p; x\<leftarrow>q u; y\<leftarrow>qa; ret((x,y),(x,y))}"
	  by (simp add: cp_arb)
	finally show ?thesis by (simp del: bind_assoc add: mon_ctr cp_def)
      qed
    }
    thus "cp (qa::bool T) \<and> dis qa \<longrightarrow> cp (do {x\<leftarrow>do {u\<leftarrow>p; q u}; y\<leftarrow>qa; ret (x, y)})"
      by blast
  qed
  ultimately show "dsef ?s" by (simp add:dsef_def)
qed


text {* Given that @{term "dsef"} programs are stable under sequencing, this
        weak form, which comes in handy sometimes, can easily be proved.  *}
lemma weak_dsef_seq: "dsef p \<Longrightarrow> dsef (do {x\<leftarrow>p; ret (f x)})"
  by(simp add: dsef_seq)


text {* 
  With the help of theorem @{thm [source] dsef_seq} the following proof is
  immediate.
*}

lemma dsef_liftM2: "\<lbrakk>dsef p; dsef q\<rbrakk> \<Longrightarrow> dsef (liftM2 f p q)"
proof -
  assume a1: "dsef p" and a2: "dsef q"
  from a1 have "dsef (do {x\<leftarrow>p; y\<leftarrow>q; ret (f x y)})"
  proof (rule dsef_seq)
    show " \<forall>x. dsef (do {y\<leftarrow>q; ret (f x y)})"
    proof 
      fix x from a2 show "dsef (do {y\<leftarrow>q; ret (f x y)})"
      proof (rule dsef_seq)
	show " \<forall>y. dsef (ret (f x y))"
	proof 
	  fix y show "dsef (ret (f x y))" by (rule dsef_ret)
	qed
      qed
    qed
  qed
  thus "dsef (liftM2 f p q)" by (simp only: liftM2_def)
qed


lemma Abs_Dsef_inverse_liftM2 [simp]: "\<lbrakk>dsef p; dsef q\<rbrakk> \<Longrightarrow> 
  \<Down> (\<Up> (liftM2 f p q)) = liftM2 f p q"
by (simp add: Abs_Dsef_inverse Dsef_def dsef_liftM2)




end


(*
 Interesting note about polymorphism:

  polymorphism prevents this lemma from being provable:

consts
  p :: "'a \<Rightarrow> bool"
lemma "p a \<Longrightarrow> \<exists>x. p x"
  oops

  whereas the following, monomorphic version does not cause any problems

consts
  p :: "nat \<Rightarrow> bool"
lemma "p a \<Longrightarrow> \<exists>x. p x" by blast

*)


(*

  The following is an example of type coercion; Lemma tst only goes through because
  we may "coerce r's type" into that of ret.
consts
  p :: "'a T"
  
lemma typ_coerc: " \<forall>r::'a\<Rightarrow>'c T. do {x\<leftarrow>p; r x} = do {p; x\<leftarrow>p; r x} \<Longrightarrow> \<forall>r::'b \<Rightarrow> 'd T. do {x\<leftarrow>p; r x} = do {p; x\<leftarrow>p; r x}"
  sorry

lemma tst: " \<forall>r. do {x\<leftarrow>p; r x} = do {p; x\<leftarrow>p; r x} \<Longrightarrow> do {x\<leftarrow>p; ret x} = do {p; x\<leftarrow>p; ret x}"
  apply(drule typ_coerc)
  apply(drule_tac x = "ret" in spec)
  apply(assumption)
done
*)


(* we cannot chain lemmas 2_3 and 3_1 together because of typing problems *)
(* 
lemma "\<lbrakk>cp p; cp q; dis p; dis q\<rbrakk> \<Longrightarrow> 
       do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)} = do {y\<leftarrow>q; x\<leftarrow>p; ret(x,y)} \<Longrightarrow>
       cp (do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)})"
  apply(frule_tac q = q in commute_2_3)
  apply(simp_all)
  apply(frule_tac q = q in commute_3_1)
  apply(simp_all)
  oops
*)
