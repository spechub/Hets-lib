theory TwoStackReverse
imports KleeneSyntax 
begin

consts
  pop        :: "nat \<Rightarrow> nat T"          ("pop\<^sub>_")
  push       :: "nat \<Rightarrow> nat \<Rightarrow> unit T"   ("push\<^sub>__")
  isempty    :: "nat \<Rightarrow> unit T"         ("isempty\<^sub>_")                

axioms 
  empty_dup[simp]    : "do {isempty\<^sub>i; isempty\<^sub>i}   = isempty\<^sub>i"
  empty_push[simp]   : "do {push\<^sub>i x; isempty\<^sub>i} = \<delta>"
  empty_pop[simp]    : "do {isempty\<^sub>i; pop\<^sub>i} = \<delta>"
 
  pop_push[simp]     : "do {x \<leftarrow> pop\<^sub>i; push\<^sub>i x; p} \<preceq> p"
  push_pop[simp]     : "do {push\<^sub>i x; x \<leftarrow> pop\<^sub>i; p x} = p x"
  empty_sef[simp]    : "isempty\<^sub>i \<preceq> ret ()"


constdefs
  append :: "nat \<Rightarrow> nat \<Rightarrow> unit T" ("append\<^sub>_\<^sub>_")
  "append\<^sub>i\<^sub>j == do {star {_ \<leftarrow> ret (); x \<leftarrow> pop\<^sub>i; push\<^sub>j x}; isempty\<^sub>i}"

lemma rev_rev_aux : "do {star {_ \<leftarrow> ret (); x \<leftarrow> pop\<^sub>i; push\<^sub>j x}; append\<^sub>j\<^sub>i} = append\<^sub>j\<^sub>i"
  apply (rule ileq_asym)
  defer
  apply (subst unf_left)
  apply simp
  apply (rule ileq_plusMon)  
  apply simp
  apply (subst delBind [THEN sym])
  apply (rule ind_left [THEN allE])
  defer 
  apply assumption
  apply simp
  apply (unfold append_def)
  apply (subst unf_left)
  by simp


lemma rev_rev : "do {isempty\<^sub>j; append\<^sub>i\<^sub>j; append\<^sub>j\<^sub>i} \<preceq> isempty\<^sub>j"
  apply (subgoal_tac "isempty\<^sub>j = do{isempty\<^sub>j; append\<^sub>j\<^sub>i}")
  apply (erule ssubst) back
  apply (simp only: delBind [THEN sym])
  apply (rule ileqBindLeft)
  apply simp
  apply (subst append_def)
  apply (subst rev_rev_aux [THEN sym]) back
  apply simp
  apply (subst ileq_def)
  apply (subgoal_tac "append\<^sub>j\<^sub>i = do {ret (); append\<^sub>j\<^sub>i}")
  apply (erule ssubst) back

  apply (simp only: delBind [THEN sym] dist1 [THEN sym] dist2 [THEN sym])
  apply (subgoal_tac "ret () = (isempty\<^sub>i \<oplus> ret ())")
  apply (erule subst)
  apply simp
  apply (rule sym)
  apply (fold ileq_def)
  apply simp
  apply simp
  apply (unfold append_def)
  apply (subst unf_left)
  apply simp
  apply (simp only: do_assoc2 [THEN sym])
  apply (subst empty_pop)
  by simp


end