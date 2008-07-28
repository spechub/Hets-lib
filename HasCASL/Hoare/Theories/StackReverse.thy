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

lemma rev_susp_dup :  "do {p \<leftarrow> rev_susp (ret is_empty); q \<leftarrow> rev_susp (ret is_empty); z \<leftarrow> p; z; z \<leftarrow> q; z} = 
                      (do {p \<leftarrow> rev_susp (ret is_empty); q \<leftarrow> rev_susp (p); z \<leftarrow> p; z; z \<leftarrow> q; z} \<oplus> 
                       do {q \<leftarrow> rev_susp (ret is_empty); p \<leftarrow> rev_susp (p); z \<leftarrow> p; z; z \<leftarrow> q; z})"

lemma "do {t \<leftarrow> ret(rev_susp (ret (ret (ret ())))); p \<leftarrow> rev_susp (p); q \<leftarrow> ret (do {t; p}); z \<leftarrow> p; z; z \<leftarrow> q; z} \<preceq> 
       do {q \<leftarrow> rev_susp (p); z \<leftarrow> p; z; z \<leftarrow> q; z}"


(*
text{* Double reverse lemma, as it was originally thougt. It is expected 
  to follow from  @{text"rev_rev_fin"}. *}
lemma rev_rev : "do {rev; rev} \<preceq> (ret ())"
  sorry
*)

end
