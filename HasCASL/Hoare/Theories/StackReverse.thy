(*  
    Title:      StackReverse.thy
    ID:         $Id$
    Author:     Sergey Goncharov
*)

header {* Double reversre of a stack, an example of Kleene monad usage *}

theory StackReverse 
imports KleeneSyntax 
begin

text{*
  Here the contants for doing stacks are defined. A stack should be
  thought of as a stateful computation monad, whose state happens to
  be a stack. Interface to it is provided by the operations @{text"pop"},
  @{text"push"} and @{text"is_empty"}.*}

consts
  pop        :: "nat T"
  push       :: "nat \<Rightarrow> unit T" 
  is_empty   :: "unit T"

-- "not used in this example"
  empty      :: "unit T"
  not_empty  :: "unit T"

constdefs
  rev :: "unit T"
  "rev == do {p \<leftarrow> star {p \<leftarrow> ret is_empty; x \<leftarrow> pop; ret (do {p; push x})}; p}"
  rev_susp :: "unit T T \<Rightarrow> unit T T T"
  "(rev_susp l) == star {p \<leftarrow> ret l; ret (do{x \<leftarrow> pop; t \<leftarrow> p; ret (do {t; push x})})}"
  rev_dup_susp :: "unit T T \<Rightarrow> unit T T \<Rightarrow> (unit T T \<times> unit T T) T"
  "(rev_dup_susp p q) == star {(p, q) \<leftarrow> ret (p, q); ret (do{x \<leftarrow> pop; t \<leftarrow> p; ret (do {t; push x})},
                                                          do{x \<leftarrow> pop; t \<leftarrow> q; ret (do {t; push x})})}"
  id_susp :: "unit T T \<Rightarrow> unit T T T"
  "(id_susp l) == star {p \<leftarrow> ret l; ret (do{x \<leftarrow> pop; t \<leftarrow> p; ret (do {push x; t})})}"
  length_inv :: "unit T \<Rightarrow> bool"
  "(length_inv p) == (do{q \<leftarrow> id_susp (ret (ret ())); z \<leftarrow> q; z; p; z \<leftarrow> q; z} = p)"
  length_mut :: "unit T \<Rightarrow> bool"
  "(length_mut p) == (do{q \<leftarrow> id_susp (ret (ret ())); z \<leftarrow> q; z; p; z \<leftarrow> q; z} = \<delta>)"

text{*
  The most essential stack axioms reflect the duality of  @{text"pop"},
  @{text"push"}. These are  @{text"pop_push"} and @{text"push_pop"}.
  Inequality sign in @{text"pop_push"} is notable: inequality becomes 
  strict, when the stack is empty. *}

axioms 
  empty_pur[simp]    : "do {is_empty; is_empty; p}   = do {is_empty; p}"
  pop_push[simp]     : "do {x \<leftarrow> pop; push x; p} \<preceq> p"
  push_pop[simp]     : "do {push x; x \<leftarrow> pop; p x} = p x"

lemma rev_lemma : "do{p \<leftarrow> star {p \<leftarrow> ret p; ret (do{x \<leftarrow> pop; t \<leftarrow> p; ret (do {t; push x})})};
                      q \<leftarrow> star {p \<leftarrow> ret (ret ()); x \<leftarrow> pop; ret (do {push x; p})}; z \<leftarrow> p; z; z \<leftarrow> p; z; q} \<preceq>
                   do{q \<leftarrow> star {p \<leftarrow> ret (ret ()); x \<leftarrow> pop; ret (do {push x; p})}; z \<leftarrow> p; z; z \<leftarrow> p; z; q}"
  apply (subst fstUnitLaw)
  apply (rule ind_left [THEN allE])
  prefer 2
  apply assumption 
  apply simp
  apply (subst unf_right) back
  apply simp
  apply (subst comm)
  apply (rule allI)
  by (rule ileq_plusMon)

lemmas rev_lemma_inst = rev_lemma [of "ret (ret ())", simplified]

text{* Following lemma is a variant of the double reverse property. 
  Informaly it reads as follows. First a payload, presenting a countable
  collection of reversing programms is prepared and bound to the variable
  @{term"p"}. Each of these programs reverses a finite prefix of the stack.
  then each of them is executed twice. The result is expected to 
  be less then @{term"ret ()"} (It straightforwardly greater then
  @{term"ret ()"}).*}

lemma rev_rev_fin : "do{p \<leftarrow> rev_susp (ret (ret ())); z \<leftarrow> p; z; z \<leftarrow> p; z} \<preceq> ret ()"
  apply (unfold rev_susp_def)
  apply (rule ileq_assoc [of _ "do{q \<leftarrow> star {p \<leftarrow> ret (ret ()); x \<leftarrow> pop; ret (do {push x; p})}; q}"])
  apply (insert rev_lemma_inst)
  apply (subst (asm) unf_left) back
  apply (subst (asm) comm)
  apply simp
  apply (rule ileq_plusE)
  apply assumption
  apply (subst fstUnitLaw [THEN sym, of id "ret ()", unfolded id_def]) back
  apply (rule indLeft [THEN allE])
  prefer 2
  apply assumption
  by simp

lemma rev_dup_lemma : "do{(p, q) \<leftarrow> rev_dup_susp p q;
                      t \<leftarrow> star {p \<leftarrow> ret (ret ()); x \<leftarrow> pop; ret (do {push x; p})}; z \<leftarrow> p; z; z \<leftarrow> q; z; t} \<preceq>
                   do{t \<leftarrow> star {p \<leftarrow> ret (ret ()); x \<leftarrow> pop; ret (do {push x; p})}; z \<leftarrow> p; z; z \<leftarrow> q; z; t}"
  apply (unfold rev_dup_susp_def)
  apply (subst fstUnitLaw)
  apply (rule_tac x = "(p, q)" and q1 = "\<lambda>(x,y).(?q2 x y)" in ind_left [THEN allE])
  prefer 2
  apply simp
  apply (subst unf_right) back
  apply simp
  apply (subst comm)
  apply (rule allI)+
  by (rule ileq_plusMon)

-- "to be relocated"
lemma ret_star_comm: "do {y \<leftarrow> star {x \<leftarrow> ret a; ret (b x)}; p; q y} = do {p; y \<leftarrow> star {x \<leftarrow> ret a; ret (b x)}; q y}"
  apply simp
  apply (subst do_assoc2 [THEN sym])
  sorry

lemma rev_dup_lemma2 : "do{(p, q) \<leftarrow> rev_dup_susp p q; z \<leftarrow> p; z; z \<leftarrow> q; z} \<preceq> 
                        do{t \<leftarrow> star {p \<leftarrow> ret (ret ()); x \<leftarrow> pop; ret (do {push x; p})}; z \<leftarrow> p; z; z \<leftarrow> q; z; t}"
  apply (rule ileq_assoc)
  prefer 2
  apply (rule rev_dup_lemma) 
  apply (subst unf_left)
  apply (unfold split_def)
  apply simp
  apply (subst comm)
  apply (rule ileq_plusI)
  by simp

-- "should follow from rev_dup_lemma"
lemma cut_dup_lema1 : "do {p \<leftarrow> rev_susp (ret is_empty); (p, q) \<leftarrow> rev_dup_susp p (ret is_empty); z \<leftarrow> p; z; z \<leftarrow> q; z} \<preceq> 
                       do {t \<leftarrow> star {p \<leftarrow> ret (ret ()); x \<leftarrow> pop; ret (do {push x; p})}; is_empty; t}"
  apply (rule ileq_assoc)
  apply (rule ileqBindLeft [THEN allE])
  prefer 2
  apply assumption
  apply (rule allI)
  apply (rule rev_dup_lemma2)
  apply simp

sorry

-- "should follow from rev_dup_lemma"
lemma cut_dup_lema2 : "do {q \<leftarrow> rev_susp (ret is_empty); (p, q) \<leftarrow> rev_dup_susp (ret is_empty) q; z \<leftarrow> p; z; z \<leftarrow> q; z} \<preceq> 
                       do {(p, q) \<leftarrow> rev_dup_susp (ret is_empty) (ret is_empty); z \<leftarrow> p; z; z \<leftarrow> q; z}"
sorry

lemma rev_susp_main: "rev_susp (do {x\<leftarrow>pop; t\<leftarrow>p; ret (do {t; push x})}) =
                      do {p\<leftarrow>rev_susp p; ret (do {x\<leftarrow>pop; t\<leftarrow>p; ret (do {t; push x})})}"
  apply (unfold rev_susp_def)
  apply (subst fstUnitLaw) back
  apply (rule inv_lemma [THEN allE])
  prefer 2
  apply (rule sym)
  apply assumption
  by simp

lemma rev_susp_comm_left: "do{ p \<leftarrow> rev_susp p; rev_dup_susp p q } = 
                      do{ (p,q) \<leftarrow> rev_dup_susp p q; p \<leftarrow> rev_susp p; ret (p,q) }"
  apply (subst tensorRight)
  apply (subst fst_conv [THEN sym, of p q])
  apply (subst fst_conv [THEN sym, of p q]) back
  apply (subst snd_conv [THEN sym, of q p]) back
  apply (subst snd_conv [THEN sym, of q p]) back back back
  apply (rule sym)
  apply (rule allE [of _ "(p, q)"])
  prefer 2
  apply assumption

  apply (unfold rev_dup_susp_def)   
  apply (unfold split_def)
  apply (simp only: fstUnitLaw fst_conv snd_conv pair_collapse)
  apply (rule inv_lemma)
  apply (rule allI)
  apply simp
  apply (subst rev_susp_main)
  by simp

lemma rev_susp_comm_right: "do{ q \<leftarrow> rev_susp q; rev_dup_susp p q } = 
                            do{ (p,q) \<leftarrow> rev_dup_susp p q; q \<leftarrow> rev_susp q; ret (p,q) }"

  apply (subst tensorLeft)
  apply (subst fst_conv [THEN sym, of p q])
  apply (subst fst_conv [THEN sym, of p q]) back
  apply (subst snd_conv [THEN sym, of q p])
  apply (subst snd_conv [THEN sym, of q p]) back back back
  apply (rule sym)
  apply (rule allE [of _ "(p, q)"])
  prefer 2
  apply assumption

  apply (unfold rev_dup_susp_def)   
  apply (unfold split_def)
  apply (simp only: fstUnitLaw fst_conv snd_conv pair_collapse)
  apply (rule inv_lemma)
  apply (rule allI)
  apply simp
  apply (subst rev_susp_main)
  by simp

lemma cut_dup_lemma :  "do {p \<leftarrow> rev_susp p; q \<leftarrow> rev_susp q; z \<leftarrow> p; z; z \<leftarrow> q; z} \<preceq> 
                       (do {p \<leftarrow> rev_susp p; (p, q) \<leftarrow> rev_dup_susp p q; z \<leftarrow> p; z; z \<leftarrow> q; z} \<oplus> 
                        do {q \<leftarrow> rev_susp q; (p, q) \<leftarrow> rev_dup_susp p q; z \<leftarrow> p; z; z \<leftarrow> q; z})" (is "?A p q \<preceq> ?B p q")
  apply (rule ileq_assoc [of _ "do {p\<leftarrow>rev_susp p; ?B p q}"])
  apply simp
  apply (rule ileq_plusI)
  apply (subst split_def)
  apply (subst rev_dup_susp_def)
  apply (subst unf_right)
  apply simp
  apply (subst comm)
  apply (rule ileq_plusI)
  apply auto
  apply (subst rev_susp_def)
  apply (subst fstUnitLaw)
  apply (rule ind_left [THEN allE, of "%p. ret (do {x\<leftarrow>pop; t\<leftarrow>p; ret (do {t; push x})})" "%p. ?B p q" p, simplified])
  prefer 2
  apply (unfold rev_susp_def)
  apply simp
  apply (fold rev_susp_def)
  apply (rule allI)
  apply (rule ileq_plus_cong1)
  apply (subst comm)
  apply (rule ileq_plusI)
  apply (unfold rev_susp_def)
  apply (subst unf_left) back
  apply simp
  apply (rule ileq_plusI)
  apply simp

  apply (fold rev_susp_def)


  apply (subst rev_susp_def)
  apply (subst unf_right)
  apply simp
  apply (rule ileq_plus_cong1)

  apply (subst comm)
  apply (rule ileq_plusI)
  apply (subst rev_susp_def)
  apply (subst unf_left)
  apply simp  
  apply (rule ileq_plusI)

  apply (subst unf_left)
  apply simp  
  apply (subst comm)
  apply (rule ileq_plusI)
  apply auto

  apply (rule ileq_plusI)
  apply (unfold rev_susp_def  rev_dup_susp_def)
  apply (subst unf_left) back back back
  apply (unfold split_def)
  apply simp
  apply (rule ileq_plusI)
  by auto

-- "should follow from rev_dup_lemma"
lemma cut_dup_lema1 : "do {p \<leftarrow> rev_susp (ret is_empty); (p, q) \<leftarrow> rev_dup_susp p (ret is_empty); z \<leftarrow> p; z; z \<leftarrow> q; z} = 
                       do {(p, q) \<leftarrow> rev_dup_susp (ret is_empty) (ret is_empty); z \<leftarrow> p; z; z \<leftarrow> q; z}"
sorry

-- "should follow from rev_dup_lemma"
lemma cut_dup_lema2 : "do {q \<leftarrow> rev_susp (ret is_empty); (p, q) \<leftarrow> rev_dup_susp (ret is_empty) q; z \<leftarrow> p; z; z \<leftarrow> q; z} =
                       do {(p, q) \<leftarrow> rev_dup_susp (ret is_empty) (ret is_empty); z \<leftarrow> p; z; z \<leftarrow> q; z}"
sorry


lemma rev_as_rev_susp: "rev = do {p \<leftarrow> rev_susp (ret is_empty); z \<leftarrow> p; z}"
  sorry

lemma rev_comm: "do{x \<leftarrow>rev_susp (ret is_empty); y \<leftarrow> q; ret (x, y)} = do {y \<leftarrow> q; x \<leftarrow>rev_susp (ret is_empty); ret (x, y)}"
  sorry

text{* Double reverse lemma, as it was originally thougt. *}
-- "should follow from cut_dup_lemma"
lemma rev_rev : "do {rev; rev} \<preceq> (ret ())"
  apply (subst rev_as_rev_susp)
  apply (subst rev_as_rev_susp)
  apply simp
  
  apply (rule ileq_assoc)
  apply (unfold rev_def)


end
