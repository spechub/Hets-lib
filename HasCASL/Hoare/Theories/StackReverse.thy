(*  
    Title:      StackReverse.thy
    ID:         $Id$
    Author:     Sergey Goncharov
*)
theory StackReverse imports KleeneSyntax begin

consts
  pop        :: "nat T"
  push       :: "nat \<Rightarrow> unit T" 
  is_empty   :: "unit T"

  (* not used in this example *)
  empty      :: "unit T"
  not_empty  :: "unit T"

constdefs
  rev :: "unit T"
  "rev == do {p \<leftarrow> star {p \<leftarrow> ret empty; x \<leftarrow> pop; ret (do {push x; p})}; p}"
  
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


lemma rev_rev : "do {rev; rev} = (ret ())"
  sorry

end