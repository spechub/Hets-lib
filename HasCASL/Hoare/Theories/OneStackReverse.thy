theory StackReverseMain 
imports KleeneSyntax 
begin

consts
  pop        :: "nat T"
  push       :: "nat \<Rightarrow> unit T" 
  is_empty   :: "unit T"

axioms 
  empty_pur[simp]    : "do {is_empty; is_empty; p}   = do {is_empty; p}"
  pop_empty[simp]    : "do {is_empty; x \<leftarrow>pop; p x}  = \<delta>"  
  empty_push[simp]   : "do {push x; is_empty; p}     = \<delta>"

  pop_push[simp]     : "do {x \<leftarrow> pop; push x; p} \<preceq> p"
  push_pop[simp]     : "do {push x; x \<leftarrow> pop; p x} = p x"
  empty_sef[simp]    : "is_empty \<preceq> ret ()"

constdefs

  -- "Extraction: this removes the list from the memory and turns it into a spirit - 
      a program which saves the elements of it in the right order"
  extr' :: "unit T T"
  "extr' == star {p \<leftarrow> ret (ret ()); x \<leftarrow> pop; ret (do {push x; p})}"
 
  -- "Same as extr', but makes sure the bottom is riched"
  extr :: "unit T T"
  "extr == do {p \<leftarrow> extr'; is_empty; ret p}"

  -- "Dually to extr' saves the extracted elements in the reverse order" 
  rtxe' :: "unit T T"
  "rtxe' == star {p \<leftarrow> ret (ret ()); x \<leftarrow> pop; ret (do {p; push x})}"
 
  rtxe :: "unit T T"
  "rtxe == do {p \<leftarrow> rtxe'; is_empty; ret p}"

  rev :: "unit T"
  "rev == do {p \<leftarrow> rtxe'; is_empty; p}"
  

lemma extr'_prop: "extr' = (ret (ret ()) \<oplus> (do {x \<leftarrow> pop; p \<leftarrow> extr'; ret (do {p; push x})}))"
  apply (unfold extr'_def)
  apply (subst unf_left) 
  apply simp
  apply (rule arg_cong [of _ _ "%u. (ret (ret ()) \<oplus> do {x \<leftarrow> pop; u x})"])
  apply (rule ext)
  apply (rule trans)
  defer
  apply (rule inv_lemma [THEN allE, THEN sym])
  defer
  apply assumption
  apply simp
  apply (rule allI)
  by simp

lemma extr_leq_id : "do {p \<leftarrow> extr; p} \<preceq> ret ()"
  apply (rule ileq_assoc [of _ "do {p \<leftarrow> extr'; ret(); p}"]) 
  apply (subst delBind [THEN sym])
  apply (subst empty_sef [unfolded ileq_def, THEN sym])
  apply (simp only: dist1 dist2)
  apply (unfold extr_def)
  apply simp
  apply (rule ileq_plusMon)
  apply (rule ileq_assoc)
  apply (unfold extr'_def)
  apply (rule indLeft [THEN allE])
  defer 
  apply assumption
  apply simp
  by simp

lemma rev_rev_inv: "do {p \<leftarrow> rtxe'; q \<leftarrow> extr'; is_empty; p; star {q \<leftarrow> ret q; x \<leftarrow> pop; ret (do {q; push x})}} =
                    do {p \<leftarrow> rtxe'; q \<leftarrow> extr'; is_empty; p; ret q}"
  apply (rule ileq_asym)
  defer
  apply (subst unf_left)
  apply simp
  apply (rule ileq_plusMon)
  apply (simp only: assocLaw [THEN sym] do_assoc1 [THEN sym] do_assoc2 [THEN sym] do_assoc3 [THEN sym] )
  apply (rule indRight)
  apply simp
  apply (subst extr'_prop) back
  apply simp
  apply (unfold rtxe'_def)
  apply (subst unf_right)
  apply simp 
  apply (rule ileq_plusI)
  by simp

lemma rev_rev: "do {rev; rev} \<preceq> ret ()"
  apply (unfold rev_def)
  apply simp
  apply (subst rtxe'_def) back
  apply (simp only: assocLaw [THEN sym]  do_assoc2 [THEN sym]  )
  apply (subgoal_tac "do {x\<leftarrow>rtxe'; is_empty; x; ret (ret ())} = do {x\<leftarrow>rtxe'; is_empty; q \<leftarrow> extr'; is_empty; x; ret q}")
  apply (erule ssubst)
  apply simp
  apply (rule ileq_assoc [of _ "do{q \<leftarrow> do {p \<leftarrow> rtxe'; q \<leftarrow> extr'; is_empty; p; star {q \<leftarrow> ret q; x \<leftarrow> pop; ret (do {q; push x})}}; is_empty; q}"])
  apply simp
  apply (subst fstUnitLaw [THEN sym, of "%u. extr'" "()"]) back
  apply (subst empty_sef [unfolded ileq_def, THEN sym])
  apply simp  
  apply (rule ileq_plusMon)

  apply (subst rev_rev_inv)
  apply simp
  apply (subst rtxe'_def)
  apply (subst unf_right)
  apply simp
  apply (rule extr_leq_id [unfolded extr_def, simplified])
  apply (subst extr'_def)  
  apply (subst unf_left)
  by simp
 
end




