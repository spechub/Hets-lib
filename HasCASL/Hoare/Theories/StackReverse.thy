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
  "rev == do {p \<leftarrow> star {p \<leftarrow> ret empty; x \<leftarrow> pop; ret (do {push x; p})}; p}"
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

lemma rev_rev_fin : "do{p \<leftarrow> star {p \<leftarrow> ret (ret (ret ())); ret (do{x \<leftarrow> pop; t \<leftarrow> p; ret (do {t; push x})})}; 
                        z \<leftarrow> p; z; z \<leftarrow> p; z} \<preceq> ret ()"
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

lemma cut_dup_lemma :  "do {p \<leftarrow> rev_susp p; q \<leftarrow> rev_susp q; z \<leftarrow> p; z; z \<leftarrow> q; z} = 
                       (do {p \<leftarrow> rev_susp p; (p, q) \<leftarrow> rev_dup_susp p q; z \<leftarrow> p; z; z \<leftarrow> q; z} \<oplus> 
                        do {q \<leftarrow> rev_susp q; (p, q) \<leftarrow> rev_dup_susp p q; z \<leftarrow> p; z; z \<leftarrow> q; z})"
sorry

-- "should follow from rev_dup_lemma"
lemma cut_dup_lema1 : "do {p \<leftarrow> rev_susp (ret is_empty); (p, q) \<leftarrow> rev_dup_susp p (ret is_empty); z \<leftarrow> p; z; z \<leftarrow> q; z} = 
                       do {(p, q) \<leftarrow> rev_dup_susp (ret is_empty) (ret is_empty); z \<leftarrow> p; z; z \<leftarrow> q; z}"
sorry

-- "should follow from rev_dup_lemma"
lemma cut_dup_lema2 : "do {q \<leftarrow> rev_susp (ret is_empty); (p, q) \<leftarrow> rev_dup_susp (ret is_empty) q; z \<leftarrow> p; z; z \<leftarrow> q; z} =
                       do {(p, q) \<leftarrow> rev_dup_susp (ret is_empty) (ret is_empty); z \<leftarrow> p; z; z \<leftarrow> q; z}"
sorry


text{* Double reverse lemma, as it was originally thougt. *}
-- "should follow from cut_dup_lemma"
lemma rev_rev : "do {rev; rev} \<preceq> (ret ())"
  sorry


end
