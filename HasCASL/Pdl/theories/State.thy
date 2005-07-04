(*
  Axiomatization of the state monad.
  For a first attempt, we only consider partial correctness
  2005-03-16  Dennis Walter

  UPDATE 2005-07-02:
    Trying to prove total correctness of Russian multiplication
         2005-07-04:
    Finished the proof, somewhat polished the documentation
*)


header {* A simple reference monad with \texttt{while} and \texttt{if} *}
theory State = PDL:



text {* 
  Read/write operations on references of arbitrary type, and a while loop.
*}

typedecl 'a ref

consts
  newRef     :: "'a \<Rightarrow> 'a ref T"
  readRef    :: "'a ref \<Rightarrow> 'a T"               
  writeRef   :: "'a ref \<Rightarrow> 'a \<Rightarrow> unit T"           ("(_ := _)" [100, 10] 10)
  MonWhile   :: "bool D \<Rightarrow> unit T \<Rightarrow> unit T"       ("WHILE (4_) /DO (4_) /END")
  

text {*
  To make the dsef operation of reading a reference more readable (pun unintended),
  we introduce a translation: @{text "*r"} stands for @{term "\<Up> readRef r"}.
*}
syntax 
  "_readRefD"  :: "'a ref \<Rightarrow> 'a D"                ("*_" [100] 100)

translations
  "_readRefD r"         ==    "\<Up> (readRef r)"


text {* This definition is rather useless as it stands, since one actually wants
  @{text "oldref r"} to be a formula in @{typ "bool D"}. The quantifier is necessary to
  avoid introducing a fresh variable @{term "a"} on the right hand side of the
  definition.
  
  The idea is appealing however, since it would provide a statement about the
  existence of @{term "r"} as a reference. 
 *} 
constdefs
  oldref     :: "'a ref \<Rightarrow> bool"
  "oldref r  \<equiv>  \<forall>a. \<turnstile> [# s\<leftarrow>newRef a](Ret (\<not>(r=s)))"


text {*
  The basic axioms of a simple while language with references. In the following we will not
  make use of operation @{term "newRef"} and hence neither of its axioms.
*}
axioms
dsef_read:     "dsef (readRef r)"
read_write:    "\<turnstile> [# r := x](\<lambda>uu. *r =\<^sub>D Ret x)"
read_write_other: "\<turnstile> ( *r =\<^sub>D Ret x) \<longrightarrow>\<^sub>D [# s := y](\<lambda>uu. Ret (r\<noteq>s) \<longrightarrow>\<^sub>D ( *r =\<^sub>D Ret x))"
read_write_other_gen: "\<turnstile> \<Up> (do {u\<leftarrow>readRef r; ret (f u)}) \<longrightarrow>\<^sub>D 
                            [# s := y](\<lambda>uu. Ret (r\<noteq>s) \<longrightarrow>\<^sub>D \<Up> (do {u\<leftarrow>readRef r; ret (f u)}))"
while_par:     "\<turnstile> P \<and>\<^sub>D b \<longrightarrow>\<^sub>D [# p](\<lambda>u. P) \<Longrightarrow> \<turnstile> P \<longrightarrow>\<^sub>D [# WHILE b DO p END](\<lambda>x. P \<and>\<^sub>D \<not>\<^sub>D b)"
read_new:      "\<turnstile> [# r\<leftarrow>newRef a]( Ret a =\<^sub>D *r)"
read_new_other: "\<turnstile> (Ret x =\<^sub>D *r) \<longrightarrow>\<^sub>D [# s \<leftarrow> newRef y]((Ret x =\<^sub>D *r) \<or>\<^sub>D Ret (r=s))"
new_distinct:   "\<turnstile> [# r\<leftarrow>newRef a; t\<leftarrow>p; s\<leftarrow>newRef b](Ret (\<not>(r=s)))"



text {* 
  Definitions of oddity and evenness of natural numbers, as well as an algorithm
  for computing Russian multiplication @{text "rumult"}.
*}
constdefs
  nat_even  :: "nat \<Rightarrow> bool"
  "nat_even n \<equiv> 2 dvd n"
  nat_odd   :: "nat \<Rightarrow> bool"
  "nat_odd n \<equiv> \<not> nat_even n"
  rumult     :: "nat \<Rightarrow> nat \<Rightarrow> nat ref \<Rightarrow> nat ref \<Rightarrow> nat ref \<Rightarrow> nat T"
  "rumult a b x y r \<equiv> do {x:=a; y:=b; r:=0;
                          WHILE (\<Up> (do {u\<leftarrow>readRef x; ret (0 < u)}))
                             DO do {u\<leftarrow>readRef x; v\<leftarrow>readRef y; w\<leftarrow>readRef r;
                                    if (nat_odd u) then (r := w + v) else ret ();
                                    x := u div 2; y := v * 2} END; readRef r}"

subsection {* General auxiliary lemmas *}

text {*
  Following are several auxiliary lemmas which are not general enough to be placed
  inside the general theory files, but which are used more than once below -- and thus
  justify their mere existence.
*}

text {* Some weakening rules *}

lemma mon_conj_imp_wk1: "\<turnstile> A \<longrightarrow>\<^sub>D C \<Longrightarrow> \<turnstile> A \<and>\<^sub>D B \<longrightarrow>\<^sub>D C"
proof -
  assume "\<turnstile> A \<longrightarrow>\<^sub>D C"
  have "\<turnstile> (A \<longrightarrow>\<^sub>D C) \<longrightarrow>\<^sub>D A \<and>\<^sub>D B \<longrightarrow>\<^sub>D C"
    by (simp add: pdl_taut)
  thus ?thesis by (rule pdl_mp)
qed

lemma mon_conj_imp_wk2: "\<turnstile> B \<longrightarrow>\<^sub>D C \<Longrightarrow> \<turnstile> A \<and>\<^sub>D B \<longrightarrow>\<^sub>D C"
proof -
  assume "\<turnstile> B \<longrightarrow>\<^sub>D C"
  have "\<turnstile> (B \<longrightarrow>\<^sub>D C) \<longrightarrow>\<^sub>D A \<and>\<^sub>D B \<longrightarrow>\<^sub>D C"
    by (simp add: pdl_taut)
  thus ?thesis by (rule pdl_mp)
qed


text {*
  The following can be used to prove a specific goal by proving two parts separately. It is
  similar to @{thm [source] mon_iffD2[OF box_conj_distrib_lifted1, THEN pdl_mp]}, which is

  @{thm mon_iffD2[OF box_conj_distrib_lifted1, THEN pdl_mp, no_vars]}
*}
lemma mon_conj_imp_box_split: "\<lbrakk>\<turnstile> A \<longrightarrow>\<^sub>D [# p]C; \<turnstile> B \<longrightarrow>\<^sub>D [# p]D\<rbrakk> \<Longrightarrow> \<turnstile> A \<and>\<^sub>D B \<longrightarrow>\<^sub>D [# x\<leftarrow>p](C x \<and>\<^sub>D D x)"
proof (rule mon_iffD2[OF box_conj_distrib_lifted1, THEN pdl_mp])
  assume a1: "\<turnstile> A \<longrightarrow>\<^sub>D [# p]C" and a2: "\<turnstile> B \<longrightarrow>\<^sub>D [# p]D"
  show "\<turnstile> (A \<and>\<^sub>D B \<longrightarrow>\<^sub>D [# p]C) \<and>\<^sub>D (A \<and>\<^sub>D B \<longrightarrow>\<^sub>D [# p]D)"
  proof (rule mon_conjI)
    show "\<turnstile> A \<and>\<^sub>D B \<longrightarrow>\<^sub>D [# p]C"
    proof (rule mon_conj_imp_wk1) 
      show "\<turnstile> A \<longrightarrow>\<^sub>D [# p]C" .
    qed
  next
    show "\<turnstile> A \<and>\<^sub>D B \<longrightarrow>\<^sub>D [# p]D"
    proof (rule mon_conj_imp_wk2)
      show "\<turnstile> B \<longrightarrow>\<^sub>D [# p]D" .
    qed
  qed
qed



text {*
  Since dsef programs may be discarded, a formula is equal to itself prefixed
  by such a program.
*}
lemma dsef_form_eq: "dsef p \<Longrightarrow> P = \<Up> (do {a\<leftarrow>p; \<Down> P})"
proof -
  assume a1: "dsef p"
  have f1: "do {a\<leftarrow>p; \<Down> P} = \<Down> P"
  proof (rule dis_left2)
    show "dis p"
      by (rule dsef_dis[OF a1])
  qed
  thus ?thesis 
  proof -
    have "P  = \<Up> (\<Down> P)"
      by (rule Rep_Dsef_inverse[symmetric])
    with f1 show ?thesis by simp
  qed
qed


text {*
  A rendition of @{thm [source] pdl_dsefB}.
*}
lemma dsefB_D: "dsef p \<Longrightarrow> \<turnstile> P \<longrightarrow>\<^sub>D [# x\<leftarrow>p]P"
by(subst dsef_form_eq[of p P], assumption, rule mon_iffD1[OF pdl_dsefB])




text {*
  An even number is equal to the sum of its div-halves.
*}
lemma even_div_eq: "nat_even n = (n div 2 + n div 2 = n)"
  apply(unfold nat_even_def)
  by arith 

text {*
  Dividing $n$ by two and adding the result to itself yields a number one less
  than $n$.
*}
lemma odd_div_eq: "nat_odd (x::nat) = (x div 2 + x div 2 + 1 = x)"
  apply(simp add: nat_odd_def nat_even_def)
  by (arith)


text {*
  A slight variant of @{thm [source] pdl_dsefB} for stateless formulas.
*}
lemma pdl_dsefB_ret: "dsef p \<Longrightarrow> \<turnstile> \<Up> (do {a\<leftarrow>p; ret (P a)}) \<longleftrightarrow>\<^sub>D [# a\<leftarrow>p](Ret (P a))"
  apply(subgoal_tac "\<forall>a. ret (P a) = \<Down> Ret (P a)")
  apply(simp)
  apply(rule pdl_dsefB)
  apply(assumption)
  apply(simp add: Ret_ret)
done


subsection {* Specific auxiliary lemmas of no general importance *}

text {*
  The following lemmas are required for the final correctness proof to go through, but
  are of rather limited interest in general.
*}

lemma var_aux1: "\<turnstile> ( *y =\<^sub>D Ret b \<and>\<^sub>D Ret (x \<noteq> y \<and> y \<noteq> r \<and> x \<noteq> r) \<and>\<^sub>D (Ret (x \<noteq> y) \<longrightarrow>\<^sub>D *x =\<^sub>D Ret a) ) \<longrightarrow>\<^sub>D
               ( *x =\<^sub>D Ret a \<and>\<^sub>D *y =\<^sub>D Ret b \<and>\<^sub>D Ret (x \<noteq> y \<and> y \<noteq> r \<and> x \<noteq> r) )"
  by (simp add: conjD_Ret_hom pdl_taut)


lemma var_aux2: "\<turnstile> (( *r =\<^sub>D Ret 0 \<and>\<^sub>D Ret (x \<noteq> y \<and> y \<noteq> r \<and> x \<noteq> r)) \<and>\<^sub>D (Ret (x \<noteq> r) \<longrightarrow>\<^sub>D *x =\<^sub>D Ret a)) \<and>\<^sub>D
                   (Ret (y \<noteq> r) \<longrightarrow>\<^sub>D *y =\<^sub>D Ret b) \<longrightarrow>\<^sub>D
                   ( *x =\<^sub>D Ret a \<and>\<^sub>D *y =\<^sub>D Ret b \<and>\<^sub>D *r =\<^sub>D Ret (0::nat) \<and>\<^sub>D Ret (x \<noteq> y \<and> y \<noteq> r \<and> x \<noteq> r))"
  by (simp add: conjD_Ret_hom pdl_taut)


text {*
  The following proof it typical: since some formulas are built from do-terms and then lifted
  into @{typ "bool D"}, the usual proof rules will not get us far. The standard scheme in this 
  case is to proceed as documented in the following side remarks.
*}
lemma derive_inv_aux: " \<turnstile> *x =\<^sub>D Ret a \<and>\<^sub>D *y =\<^sub>D Ret b \<and>\<^sub>D *r =\<^sub>D Ret (0::nat) \<and>\<^sub>D Ret (x \<noteq> y \<and> y \<noteq> r \<and> x \<noteq> r) 
                         \<longrightarrow>\<^sub>D Ret (x \<noteq> y \<and> y \<noteq> r \<and> x \<noteq> r) \<and>\<^sub>D 
                               \<Up> (do {u\<leftarrow>readRef x; v\<leftarrow>readRef y; w\<leftarrow>readRef r; ret (u*v+w = a*b)})"
  (is "\<turnstile> ?x \<and>\<^sub>D ?y \<and>\<^sub>D ?r \<and>\<^sub>D ?diff \<longrightarrow>\<^sub>D ?diff \<and>\<^sub>D ?seq")
proof -
  -- {* Simplify the goal by proving something tautologously equivalent. *}
  have "\<turnstile> (?x \<and>\<^sub>D ?y \<and>\<^sub>D ?r \<longrightarrow>\<^sub>D ?seq) \<longrightarrow>\<^sub>D
          (?x \<and>\<^sub>D ?y \<and>\<^sub>D ?r \<and>\<^sub>D ?diff \<longrightarrow>\<^sub>D ?diff \<and>\<^sub>D ?seq)" by (simp add: pdl_taut)
  moreover
  have "\<turnstile> ?x \<and>\<^sub>D ?y \<and>\<^sub>D ?r \<longrightarrow>\<^sub>D ?seq"
    -- {* Turn the formula into a straight program sequence *}
    apply(simp add: liftM2_def impD_def conjD_def MonEq_def dsef_read Abs_Dsef_inverse Dsef_def Ret_ret)
    apply(simp add: dsef_read Abs_Dsef_inverse Dsef_def dsef_seq)
    apply(simp add: mon_ctr del: bind_assoc)
    -- {* Sort programs so that equal ones are next to each other *}
    apply(simp del: dsef_ret add: commute_dsef[of "readRef r" "readRef x"] dsef_read)
    apply(simp del: dsef_ret add: commute_dsef[of "readRef y" "readRef x"] dsef_read)
    apply(simp del: dsef_ret add: commute_dsef[of "readRef r" "readRef y"] dsef_read)
    -- {* Remove duplicate occurrences of all programs *}
    apply(simp add: dsef_cp[OF dsef_read[of "x"]] cp_arb)
    apply(simp add: dsef_cp[OF dsef_read[of "y"]] cp_arb)
    apply(simp add: dsef_cp[OF dsef_read[of "r"]] cp_arb)
    -- {* Finally prove the returned stateless formula and conclude by reducing 
          the program to @{term "ret True"} *}
    apply(simp add: dsef_dis[OF dsef_read] dis_left2)
    apply(simp add: Valid_simp Abs_Dsef_inverse Dsef_def)
    done
  ultimately show ?thesis by (rule pdl_mp)
qed



lemma doterm_eq1_aux: "do {u\<leftarrow>readRef x; v\<leftarrow>readRef y; w\<leftarrow>readRef r; ret (u * v + w = a * b)} =
                       do {u\<leftarrow>readRef x; \<Down> (\<Up> (do {v\<leftarrow>readRef y; w\<leftarrow>readRef r; ret (u * v + w = a * b)}))}"
(*<*)
proof -
  have "\<forall>u. \<Down> (\<Up> (do {v\<leftarrow>readRef y; w\<leftarrow>readRef r; ret (u * v + w = a * b)})) = 
                 do {v\<leftarrow>readRef y; w\<leftarrow>readRef r; ret (u * v + w = a * b)}"
    apply(rule allI)
    apply(rule Abs_Dsef_inverse)
    apply(simp add: Dsef_def)
    apply(rule dsef_seq, rule dsef_read, rule allI)+
    apply(rule dsef_ret)
    done
  thus ?thesis by simp
qed
(*>*)

lemma doterm_eq2_aux: "do {v\<leftarrow>readRef y; w\<leftarrow>readRef r; ret (u * v + w = a * b)} =
                       do {v\<leftarrow>readRef y; \<Down> (\<Up> (do {w\<leftarrow>readRef r; ret (u * v + w = a * b)}))}"
(*<*)
proof -
  have "\<forall>u v. \<Down> (\<Up> (do {w\<leftarrow>readRef r; ret (u * v + w = a * b)})) = 
              do {w\<leftarrow>readRef r; ret (u * v + w = a * b)}"
    apply(rule allI)+
    apply(rule Abs_Dsef_inverse)
    apply(simp add: Dsef_def)
    apply(rule dsef_seq, rule dsef_read, rule allI)
    apply(rule dsef_ret)
    done
  thus ?thesis by simp
qed
(*>*)

lemma arith_aux: "\<lbrakk>nat_odd u; u * v + w = a * b\<rbrakk> \<Longrightarrow> (u div 2 + u div 2) * v + (w + v) = a * b"
(*<*)
proof -
  assume a1: "nat_odd u"
  assume a2: "u * v + w = a * b"
  have "u * v = (u div 2 + u div 2) * v + v"
  proof -
    from a1 
    have f1: "u = (u div 2 + u div 2 + 1)" by (rule iffD1[OF odd_div_eq, symmetric])
    hence "u * v = (u div 2 + u div 2 + 1) * v" 
      by(rule arg_cong)
    also have "\<dots> = (u div 2 + u div 2) * v + v"
      by(simp add: add_mult_distrib)
    finally show ?thesis .
  qed
  with a2 show ?thesis by simp
qed
(*>*)


lemma rel1_aux: "nat_odd u \<Longrightarrow> \<turnstile>  ( Ret (x \<noteq> y \<and> y \<noteq> r \<and> x \<noteq> r) \<and>\<^sub>D *r =\<^sub>D Ret (w + v) \<and>\<^sub>D Ret (u * v + w = a * b) ) \<longrightarrow>\<^sub>D
                    Ret (x\<noteq>y \<and> y\<noteq>r \<and> x\<noteq>r) \<and>\<^sub>D \<Up> (do {w\<leftarrow>readRef r; ret ((u div 2 + u div 2) * v + w = a * b)})"
  (is "?odd \<Longrightarrow> \<turnstile> (?diff \<and>\<^sub>D ?r \<and>\<^sub>D ?ar) \<longrightarrow>\<^sub>D ?diff \<and>\<^sub>D ?seq")
(*<*)
proof -
  assume a1: "nat_odd u"
  have "\<turnstile> (?r \<and>\<^sub>D ?ar \<longrightarrow>\<^sub>D ?seq) \<longrightarrow>\<^sub>D
          (?diff \<and>\<^sub>D ?r \<and>\<^sub>D ?ar) \<longrightarrow>\<^sub>D ?diff \<and>\<^sub>D ?seq"
    by (simp add: pdl_taut)
  moreover 
  have "\<turnstile> (?r \<and>\<^sub>D ?ar \<longrightarrow>\<^sub>D ?seq)"
    apply(simp add: MonEq_def conjD_def impD_def liftM2_def Ret_ret)
    apply (simp add: Abs_Dsef_inverse Dsef_def dsef_read dsef_seq)
    apply(simp del: bind_assoc add: mon_ctr)
    apply(insert dsef_cp[OF dsef_read[of r]])
    apply(insert dsef_dis[OF dsef_read[of r]])
    apply(simp add: cp_arb)
    apply(insert a1)
    apply(subgoal_tac "u * v + w = a * b \<longrightarrow> (u div 2 + u div 2) * v + (w + v) = a * b")
    apply(unfold nat_odd_def nat_even_def)   
    apply(simp add: dis_left2 Valid_simp Abs_Dsef_inverse Dsef_def)
    apply(clarify)
    by(rule arith_aux)
  ultimately
  show "\<turnstile> (?diff \<and>\<^sub>D ?r \<and>\<^sub>D ?ar) \<longrightarrow>\<^sub>D ?diff \<and>\<^sub>D ?seq"
    by (rule pdl_mp)
qed
(*>*)

lemma wrt_other_aux: "\<turnstile> Ret ( x\<noteq>y \<and> y\<noteq>r \<and> x\<noteq>r ) \<and>\<^sub>D \<Up> (do {w\<leftarrow>readRef r; ret (f w)}) \<longrightarrow>\<^sub>D 
                        [# x := a](\<lambda>uu. Ret (x\<noteq>y \<and> y\<noteq>r \<and> x\<noteq>r) \<and>\<^sub>D \<Up> (do {w\<leftarrow>readRef r; ret (f w)}))"
(*<*)
  apply(rule pdl_mpB_lifted1)
  apply(rule mon_conj_imp_box_split)
  apply(rule pdl_k3B)
  apply(rule read_write_other_gen)
  apply(subst eq_sym_conv[of r x])
  apply(simp add: conjD_Ret_hom pdl_taut)
done
(*>*)


lemma wrt_other2_aux:  "\<turnstile> Ret ( x\<noteq>y \<and> y\<noteq>r \<and> x\<noteq>r ) \<and>\<^sub>D \<Up> (do {w\<leftarrow>readRef r; ret (f w)}) \<longrightarrow>\<^sub>D 
                        [# y := b](\<lambda>uu. Ret (x\<noteq>y \<and> y\<noteq>r \<and> x\<noteq>r) \<and>\<^sub>D \<Up> (do {w\<leftarrow>readRef r; ret (f w)}))"
(*<*)
  apply(rule pdl_mpB_lifted1)
  apply(rule mon_conj_imp_box_split)
  apply(rule pdl_k3B)
  apply(rule read_write_other_gen)
  apply(subst eq_sym_conv[of r y])
  apply(simp add: conjD_Ret_hom pdl_taut)
done
(*>*)

lemma rd_seq_aux: "\<turnstile> \<Up> (do {w\<leftarrow>readRef r; ret (f a w)}) \<and>\<^sub>D *x =\<^sub>D Ret a \<longrightarrow>\<^sub>D
                     \<Up> (do {u\<leftarrow>readRef x; w\<leftarrow>readRef r; ret (f u w)})"
(*<*)
  apply(simp add: MonEq_def conjD_def impD_def liftM2_def Ret_ret)
  apply (simp add: Abs_Dsef_inverse Dsef_def dsef_read dsef_seq)
  apply(simp del: bind_assoc add: mon_ctr)
  apply(simp del: dsef_ret add: commute_dsef[of "readRef r" "readRef x"] dsef_read)
  apply(simp add: dsef_cp[OF dsef_read[of "x"]] cp_arb)
  apply(simp add: dsef_cp[OF dsef_read[of "r"]] cp_arb)
  apply(simp add: dsef_dis[OF dsef_read] dis_left2)
  apply(simp add: Valid_simp Abs_Dsef_inverse Dsef_def)
done
(*>*)

lemma arith2_aux: "(u div (2::nat) + u div 2) * v + w = a * b \<longrightarrow> u div 2 * (v * 2) + w = a * b"
(*<*)
proof
  assume a1: "(u div 2 + u div 2) * v + w = a * b"
  have "(u div 2 + u div 2) * v = u div 2 * (v * 2)"
  proof -
    have "(u div 2 + u div 2) * v = (2 * (u div 2)) * v" by simp
    also have "2 * (u div 2) * v = (u div 2) * (v * 2)" by simp
    finally show ?thesis .
  qed
  with a1 show "u div 2 * (v * 2) + w = a * b" by simp
qed
(*>*)


lemma asm_results_aux: " \<turnstile> (Ret (x \<noteq> y) \<longrightarrow>\<^sub>D *x =\<^sub>D Ret (u div (2::nat))) \<and>\<^sub>D
         *y =\<^sub>D Ret (v * 2) \<and>\<^sub>D
         Ret (x \<noteq> y \<and> y \<noteq> r \<and> x \<noteq> r) \<and>\<^sub>D \<Up> (do {w\<leftarrow>readRef r; ret ((u div 2 + u div 2) * v + w = a * b)}) \<longrightarrow>\<^sub>D
         Ret (x \<noteq> y \<and> y \<noteq> r \<and> x \<noteq> r) \<and>\<^sub>D \<Up> (do {u\<leftarrow>readRef x; v\<leftarrow>readRef y; w\<leftarrow>readRef r; ret (u * v + w = a * b)})"
(*<*)
  apply(simp add: MonEq_def conjD_def impD_def liftM2_def Ret_ret)
  apply (simp add: Abs_Dsef_inverse Dsef_def dsef_read dsef_seq)
  apply(simp del: bind_assoc add: mon_ctr)
  apply(simp del: dsef_ret add: commute_dsef[of "readRef r" "readRef x"] dsef_read)
  apply(simp del: dsef_ret add: commute_dsef[of "readRef y" "readRef x"] dsef_read)
  apply(simp del: dsef_ret add: commute_dsef[of "readRef r" "readRef y"] dsef_read)
  apply(simp add: dsef_cp[OF dsef_read[of "x"]] cp_arb)
  apply(simp add: dsef_cp[OF dsef_read[of "y"]] cp_arb)
  apply(simp add: dsef_cp[OF dsef_read[of "r"]] cp_arb)
  apply(simp add: arith2_aux)
  apply(simp add: dsef_dis[OF dsef_read] dis_left2)
  apply(simp add: Valid_simp Abs_Dsef_inverse Dsef_def)
done
(*>*)

text {* Yet another dsef formula extension *}
lemma yadfe: " \<lbrakk>dsef p; dsef q; dsef r; \<forall>x y z. f x y z\<rbrakk> \<Longrightarrow> \<turnstile> \<Up> (do {x\<leftarrow>p; y\<leftarrow>q; z\<leftarrow>r; ret (f x y z)})"
proof -
  assume ds: "dsef p" "dsef q" "dsef r"
  assume a1: "\<forall>x y z. f x y z"
  hence "\<Down> (\<Up> (do {x\<leftarrow>p; y\<leftarrow>q; z\<leftarrow>r; ret (f x y z)})) = 
         \<Down> (\<Up> (do {x\<leftarrow>p; y\<leftarrow>q; z\<leftarrow>r; ret True}))"
    by (simp)
  also from ds have "\<dots> = ret True" 
    by (simp add: Abs_Dsef_inverse Dsef_def dsef_seq dis_left2 dsef_dis)
  finally show ?thesis by (simp add: Valid_simp)
qed


lemma conclude_aux: " \<turnstile> (Ret (x \<noteq> y \<and> y \<noteq> r \<and> x \<noteq> r) \<and>\<^sub>D 
         \<Up> (do {u\<leftarrow>readRef x; v\<leftarrow>readRef y; w\<leftarrow>readRef r; ret (u * v + w = (a::nat) * b)})) \<and>\<^sub>D
         \<not>\<^sub>D \<Up> (do {u\<leftarrow>readRef x; ret (0 < u)}) \<longrightarrow>\<^sub>D
         [# readRef r](\<lambda>x. Ret (x = a * b))"
(*<*)
  apply(rule pdl_imp_trans)
  prefer 2
  apply(rule mon_iffD1[OF pdl_dsefB])
  apply(rule dsef_read)
  apply(simp add: MonEq_def NotD_def conjD_def impD_def liftM2_def Ret_ret)
  apply(simp add: Abs_Dsef_inverse Dsef_def dsef_read dsef_seq)
  apply(simp del: bind_assoc add: mon_ctr)
  apply(simp del: dsef_ret add: commute_dsef[of "readRef r" "readRef x"] dsef_read)
  apply(simp del: dsef_ret add: commute_dsef[of "readRef y" "readRef x"] dsef_read)
  apply(simp add: dsef_cp[OF dsef_read[of "x"]] cp_arb)
  apply(simp add: dsef_cp[OF dsef_read[of "r"]] cp_arb)
  apply(rule yadfe)
  apply(rule dsef_read)+
  apply(clarsimp)
done
(*>*)




subsection {* Correctness of Russian multiplication *}

text {*
  Equipped with all these prerequisites, the correctness proof of Russian multiplication
  is `at your fingertips'\texttrademark. 
*}

theorem russian_mult: "\<turnstile> (Ret ( x\<noteq>y \<and> y\<noteq>r \<and> x\<noteq>r)) \<longrightarrow>\<^sub>D [# rumult a b x y r](\<lambda>x. Ret (x = a * b))"
(*<*)
  apply(unfold rumult_def)
  apply(simp only: seq_def) -- {* make plug rules applicable *}
  apply(rule pdl_plug_lifted1) -- {* working on @{text [# x := a]} box *}
  apply(rule mon_iffD2[OF box_conj_distrib_lifted1, THEN pdl_mp])
  apply(rule mon_conjI)
  apply(rule pdl_k3B)
  apply(rule mon_imp_wk)
  apply(rule read_write)
  apply(rule allI)
  apply(rule pdl_plug_lifted1)   -- {* working on @{text [# y := b]} box *}
  apply(rule mon_iffD2[OF box_conj_distrib_lifted1, THEN pdl_mp])
  apply(rule mon_conjI)
  apply(rule mon_imp_wk)
  apply(rule read_write) -- {* used the first goal to establish value of y *}
  apply(rule mon_iffD2[OF box_conj_distrib_lifted1, THEN pdl_mp])
  apply(rule mon_conjI)
  apply(rule mon_conj_imp_wk1)
  apply(rule pdl_k3B)
  apply(rule mon_conj_imp_wk2) 
  apply(rule read_write_other)
  apply(rule allI)
  apply(rule pdl_imp_trans)
  apply(rule var_aux1)
  apply(rule pdl_plug_lifted1) -- {* working on @{text [# r := 0]} box *}
  apply(rule mon_iffD2[OF box_conj_distrib_lifted1, THEN pdl_mp])
  apply(rule mon_conjI)
  apply(rule mon_iffD2[OF box_conj_distrib_lifted1, THEN pdl_mp])
  apply(rule mon_conjI)
  apply(rule mon_iffD2[OF box_conj_distrib_lifted1, THEN pdl_mp])
  apply(rule mon_conjI) -- {* four identical goals, one for each conjunct needed inside the box. *}
  apply(rule mon_imp_wk)
  apply(rule read_write)
  apply(rule mon_conj_imp_wk2)+
  apply(rule pdl_k3B)
  apply(rule mon_conj_imp_wk1)
  apply(rule read_write_other)
  apply(rule mon_conj_imp_wk2, rule mon_conj_imp_wk1)
  apply(rule read_write_other)
  apply(rule allI)
  apply(rule pdl_imp_trans)
  apply(rule var_aux2) -- {* arrived at the while loop *}
  apply(rule pdl_imp_trans) -- {* derive invariant from the premiss *}
  apply(rule derive_inv_aux)
  apply(rule pdl_plug_lifted1)
  apply(rule while_par)  -- {* applied the while rule *}
  apply(simp del: bind_assoc) -- {* work off read operations *}
  apply(rule pdl_plug_lifted1)
  apply(rule mon_iffD2[OF box_conj_distrib_lifted1, THEN pdl_mp])
  apply(rule mon_conjI)
  apply(rule mon_conj_imp_wk2) 
  apply(rule mon_iffD1[OF pdl_dsefB_ret], rule dsef_read)
  apply(rule mon_conj_imp_wk1)
  apply(rule mon_iffD2[OF box_conj_distrib_lifted1, THEN pdl_mp])
  apply(rule mon_conjI)
  apply(rule mon_conj_imp_wk1)
  apply(rule dsefB_D)
  apply(rule dsef_read)
  apply(rule mon_conj_imp_wk2)
  apply(subst doterm_eq1_aux)
  apply(rule mon_iffD1[OF pdl_dsefB])
  apply(rule dsef_read)
  apply(rule allI) (* work off y *)
  apply(rule pdl_plug_lifted1)
  apply(rule mon_conj_imp_box_split)
  apply(rule pdl_k3B)
  apply(rule mon_conj_imp_box_split)
  apply(rule dsefB_D)
  apply(rule dsef_read)
  apply(subst doterm_eq2_aux)
  apply(rule mon_iffD1[OF pdl_dsefB])
  apply(rule dsef_read)
  apply(rule allI) (* work away r *)
  apply(rule pdl_plug_lifted1) 
  apply(rule mon_conj_imp_box_split)
  apply(rule pdl_k3B)
  apply(rule mon_conj_imp_box_split)
  apply(rule dsefB_D)
  apply(rule dsef_read)
  apply(rule mon_iffD2[OF box_conj_distrib_lifted1, THEN pdl_mp])
  apply(rule mon_conjI)
  apply(rule mon_iffD1[OF pdl_dsefB_ret])
  apply(rule dsef_read)
  apply(rule dsefB_D)
  apply(rule dsef_read)
  apply(rule allI) -- {* arrived at the if-then-else construct *}
  apply(rule pdl_plug_lifted1)
  apply(simp add: split_if)
  apply(safe)  -- {* now we have to prove the two different branches  *}
  apply(rule pdl_mpB_lifted1) (* dropping 0 < u, since we don't need it (is appears) *)
  apply(rule mon_conj_imp_wk2)
  apply(rule mon_conj_imp_box_split)
  apply(rule pdl_k3B)
  apply(rule mon_conj_imp_wk1)
  apply(rule mon_iffD2[OF box_conj_distrib_lifted1, THEN pdl_mp]) 
  apply(rule mon_conjI)
  apply(rule mon_imp_wk)
  apply(rule read_write)
  apply(rule pdl_k3B)
  apply(rule allI)
  apply(rule rel1_aux)
  apply(assumption)
  apply(rule mon_conj_imp_wk2)
  apply(rule mon_conj_imp_box_split)
  apply(rule pdl_k3B)
  apply(rule mon_conj_imp_wk2)
  apply(simp add: even_div_eq nat_odd_def)
  apply(rule mon_iffD2[OF pdl_retB]) -- {* arrived at @{text "x := u div 2"} *}
  apply(rule pdl_plug_lifted1)
  apply(rule mon_iffD2[OF box_conj_distrib_lifted1, THEN pdl_mp])
  apply(rule mon_conjI)
  apply(rule mon_imp_wk)
  apply(rule read_write)
  apply(rule wrt_other_aux)
  apply(rule allI) -- {* almost done, just the @{text "y := v * 2"} remaining *}
  apply(rule pdl_mpB_lifted1)
  apply(rule mon_conj_imp_box_split)
  apply(rule read_write_other)
  apply(rule mon_iffD2[OF box_conj_distrib_lifted1, THEN pdl_mp])
  apply(rule mon_conjI)
  apply(rule mon_imp_wk)
  apply(rule read_write)
  apply(rule wrt_other2_aux)
  apply(rule allI)
  apply(rule asm_results_aux)  
(*>*)
  -- {* \dots Just 124 straightforward proof steps later *}
  apply(rule conclude_aux)
done


end

