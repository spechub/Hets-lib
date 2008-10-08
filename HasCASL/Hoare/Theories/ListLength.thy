theory ListLength 
imports KleeneSyntax 
begin

consts
  pop        :: "nat \<Rightarrow> nat T"          ("pop\<^sub>_")
  push       :: "nat \<Rightarrow> nat \<Rightarrow> unit T"   ("push\<^sub>__")
  isempty    :: "nat \<Rightarrow> unit T"         ("isempty\<^sub>_")                
  leng       :: "nat \<Rightarrow> int T"          ("leng\<^sub>_")

axioms 
  empty_dup[simp]    : "do {isempty\<^sub>i; isempty\<^sub>i}   = isempty\<^sub>i"
  pop_push[simp]     : "do {x \<leftarrow> pop\<^sub>i; push\<^sub>i x; p} \<preceq> p"
  empty_push[simp]   : "do {push\<^sub>i x; isempty\<^sub>i} = \<delta>"
  empty_pop[simp]    : "do {isempty\<^sub>i; pop\<^sub>i} = \<delta>"

  push_pop[simp]     : "do {push\<^sub>i x; x \<leftarrow> pop\<^sub>i; p x} = p x"
  empty_sef[simp]    : "isempty\<^sub>i \<preceq> ret ()"
  length_empty       : "do {isempty\<^sub>i; leng\<^sub>i} = do {isempty\<^sub>i; ret 0}"
  length_push        : "do {x \<leftarrow> leng\<^sub>i; push\<^sub>i a; ret (x + 1)} = do {push\<^sub>i a; leng\<^sub>i}"
  empty_comm         : "do {isempty\<^sub>i; p} = do {x \<leftarrow>p ;isempty\<^sub>i; ret x}"
  leng_comm          : "do {x \<leftarrow> leng\<^sub>i; p; ret x} = do {p; leng\<^sub>i}"
  pop_comm           : "do {x \<leftarrow> pop\<^sub>i; y \<leftarrow> p; r x y} = do {y \<leftarrow> p; x \<leftarrow> pop\<^sub>i; r x y}"

constdefs
  append :: "nat \<Rightarrow> nat \<Rightarrow> unit T" ("append\<^sub>_\<^sub>_")
  "append\<^sub>i\<^sub>j == do {star {_ \<leftarrow> ret (); x \<leftarrow> pop\<^sub>i; push\<^sub>j x}; isempty\<^sub>i}"
  purge :: "nat \<Rightarrow> unit T" ("purge\<^sub>_")
  "purge\<^sub>i == do {star {_ \<leftarrow> ret 0; pop\<^sub>i}; isempty\<^sub>i}" 

lemma length_pop : "do {x \<leftarrow> leng\<^sub>i; z \<leftarrow> pop\<^sub>i; r x z} = do {z \<leftarrow> pop\<^sub>i; x \<leftarrow> leng\<^sub>i; r (x + 1) z}"
  apply (subgoal_tac "do {x \<leftarrow> leng\<^sub>i; z \<leftarrow> pop\<^sub>i; r x z} = do {x \<leftarrow> pop\<^sub>i; push\<^sub>i x; x \<leftarrow> leng\<^sub>i; z \<leftarrow> pop\<^sub>i; r x z}")
  apply (erule ssubst)
  apply (subst do_assoc2 [THEN sym])
  apply (subst length_push [THEN sym])
  apply simp
  sorry


lemma purge_empty: "do {isempty\<^sub>i; purge\<^sub>i} = isempty\<^sub>i"
  apply (unfold purge_def)
  apply simp
  apply (subst unf_left)
  apply simp
  apply (subst do_assoc2 [THEN sym])
  apply (subst empty_pop)
  by simp

lemma leng_inv: "do {z\<leftarrow>pop\<^sub>i; push\<^sub>j z; y\<leftarrow>leng\<^sub>i; x\<leftarrow>leng\<^sub>j; ret (x + y)}=
                 do {y\<leftarrow>leng\<^sub>i; x\<leftarrow>leng\<^sub>j; z\<leftarrow>pop\<^sub>i; push\<^sub>j z; ret (x + y)}"
  apply (subst do_assoc2 [THEN sym])
  apply (subst leng_comm [THEN sym])
  apply simp
  apply (subst do_assoc2 [THEN sym])
  apply (subst length_push [THEN sym])
  apply simp
  apply (subgoal_tac "do {z\<leftarrow>pop\<^sub>i; x\<leftarrow>leng\<^sub>i; xa\<leftarrow>leng\<^sub>j; push\<^sub>j z; ret (xa + 1 + x)} = 
                      do {(x, z) \<leftarrow> do{ z\<leftarrow>pop\<^sub>i; x\<leftarrow>leng\<^sub>i; ret ((x + 1), z)}; xa\<leftarrow>leng\<^sub>j; push\<^sub>j z; ret (xa + x)}")
  apply (erule ssubst)
  apply (subst length_pop [THEN sym])
  apply simp
  apply (subst pop_comm) 
  apply simp
  apply simp
  apply (subst add_commute) back back back
  apply (subst add_assoc)
  by simp

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

lemma leng_of_append : "do {x \<leftarrow> leng\<^sub>i; y \<leftarrow> leng\<^sub>j; purge\<^sub>i; purge\<^sub>j; ret (x + y)} = do {append\<^sub>i\<^sub>j; x \<leftarrow> leng\<^sub>j; purge\<^sub>j; ret x}"
 
  apply (subgoal_tac "do {append\<^sub>i\<^sub>j; x\<leftarrow>leng\<^sub>j; purge\<^sub>j; ret x} = 
                      do {append\<^sub>i\<^sub>j; y\<leftarrow>leng\<^sub>i; x\<leftarrow>leng\<^sub>j; purge\<^sub>i; purge\<^sub>j; ret (x+y)}")
  apply (erule ssubst)
  defer  
  apply (unfold append_def)
  apply simp
  apply (subst do_assoc2 [THEN sym] ) back
  apply (subst length_empty)
  apply (subst purge_empty [THEN sym])
  apply simp
  apply (subst do_assoc2 [THEN sym] )
  apply (subst leng_comm [THEN sym])
  apply simp

  apply (subst do_assoc3) 
  apply (subst do_assoc2 [THEN sym] )
  apply (subst leng_comm [THEN sym])
  apply simp
  apply (subst do_assoc2 [THEN sym] ) back
  apply (subst leng_comm [THEN sym])
  apply simp

  apply (subgoal_tac "do {((\<lambda>_. pop\<^sub>i \<guillemotright>= push j)\<^sup>*) (); y\<leftarrow>leng\<^sub>i; x\<leftarrow>leng\<^sub>j; isempty\<^sub>i; purge\<^sub>i; purge\<^sub>j; ret (x + y)} =
                      do {((\<lambda>_. pop\<^sub>i \<guillemotright>= push j)\<^sup>*) (); z \<leftarrow> do {y\<leftarrow>leng\<^sub>i; x\<leftarrow>leng\<^sub>j; ret (x + y)}; isempty\<^sub>i; purge\<^sub>i; purge\<^sub>j; ret z}") 
  defer
  apply simp
  apply (erule ssubst)
  apply (subst do_assoc2 [THEN sym])

  apply (subgoal_tac "do {((\<lambda>_. pop\<^sub>i \<guillemotright>= push j)\<^sup>*) (); y\<leftarrow>leng\<^sub>i; x\<leftarrow>leng\<^sub>j; ret (x + y)} = 
                      do {z\<leftarrow>do {y\<leftarrow>leng\<^sub>i; x\<leftarrow>leng\<^sub>j; ret (x + y)}; ((\<lambda>_. pop\<^sub>i \<guillemotright>= push j)\<^sup>*) (); ret z}")
  apply (erule ssubst)
  apply simp 
  apply (rule_tac f="%u. do {x \<leftarrow> leng i; u x}" in arg_cong)
  apply (rule ext)
  apply (rule_tac f="%u. do {x \<leftarrow> leng j; u x}" in arg_cong)
  apply (rule ext)
  apply (subst do_assoc3 [THEN sym]) back back
  apply (subst purge_empty)
  apply (subst do_assoc3 [THEN sym]) back back
  apply (subst empty_comm)
  apply simp
  apply (subgoal_tac "do {((\<lambda>_. pop\<^sub>i \<guillemotright>= push j)\<^sup>*) (); purge\<^sub>j} = do {star {_ \<leftarrow> ret 0; pop\<^sub>i}; purge\<^sub>j}")
  apply (subst do_assoc3 [THEN sym]) back

  apply (erule ssubst)
  apply (subst purge_def)
  apply simp
  apply (subst empty_comm)
  apply (subst add_commute)
  apply simp
  apply simp
  apply (rule trans)
  apply (subst delBind [THEN sym])
  apply (rule inv_lemma [THEN allE])
  prefer 2
  apply assumption
  prefer 2
  apply (rule sym)
  apply (subst delBind [THEN sym])
  apply (rule inv_lemma [THEN allE])
  prefer 2
  apply assumption
  apply simp
  apply (subst pop_comm [THEN sym, of _ i "%i x. ret ()"])
  apply simp
  apply simp

  apply (unfold purge_def)
  apply (subst unf_left)
  apply (simp)
  apply (subst empty_comm)
  apply simp
  apply (simp only: delBind [THEN sym])
  apply (subst pop_comm [THEN sym])
  apply simp
  apply (subst unf_left)
  apply (subst unf_left) back
  apply simp
  apply (rule trans)
  apply (subst delBind [THEN sym])
  apply (rule inv_lemma [THEN allE])
  prefer 2
  apply assumption
  apply simp
  apply (rule leng_inv)
  apply simp
  apply (rule_tac f="%u. do {y\<leftarrow>leng\<^sub>i; x\<leftarrow>leng\<^sub>j; u x y}" in arg_cong)
  apply (rule ext)+
  apply (rule_tac x="(x + y)" in fun_cong)
  apply (rule ext)
  apply simp
  apply (rule trans)
  prefer 2
  apply (subst delBind [THEN sym])
  apply (rule sym)
  apply (rule inv_lemma [THEN allE])
  prefer 2
  apply assumption
  apply simp
  by simp



end