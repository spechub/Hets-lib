theory MultimonadSyntax imports MonadSyntax begin

text{*Definition of multiomonad operations: nondeterministic choice 
      \quak{@{text "\<oplus>"}} and deadlock \quak{@{text "\<delta>"}}*}

consts   
  choice  :: "('a T \<Rightarrow> 'a T \<Rightarrow> 'a T)"    (infixl "\<oplus>" 10)
  zero    :: "'a T" ("\<delta>")  

constdefs
  ileq   :: "('a T \<Rightarrow> 'a T \<Rightarrow> bool)"   (infix "\<preceq>" 10)
  "(p \<preceq>  q) == ((p \<oplus> q) = q)"

  igeq   :: "('a T \<Rightarrow> 'a T \<Rightarrow> bool)"   (infix "\<succeq>" 10)
  "(p \<succeq>  q) == ((p \<oplus> q) = p)"
  
  ile    :: "('a T \<Rightarrow> 'a T \<Rightarrow> bool)"   (infix "\<prec>" 10)
  "(p \<prec> q ) == ((p \<preceq> q) \<and> (p \<noteq> q))"

axioms
 plus0[simp]:            "(p \<oplus> \<delta>) = p"
 comm:                   "(p \<oplus> q) = (q \<oplus> p)"
 idmp [simp]:            "(p \<oplus> p) = p"
 plus:                   "((p \<oplus> q) \<oplus> r) = (p \<oplus> (q \<oplus> r))"
 dist1:                  "((p \<oplus> q) \<guillemotright>= r) = ((p \<guillemotright>= r) \<oplus> (q \<guillemotright>= r))" 
 dist2:                  "(p \<guillemotright>= (\<lambda>x. (q x \<oplus> r x))) = ((p \<guillemotright>= q) \<oplus> (p\<guillemotright>= r))"
 bind01:                 "(\<delta> \<guillemotright>= r) = \<delta>" 
 bind02:                 "(p \<guillemotright>= (\<lambda>x. \<delta>)) = \<delta>"

lemma plus0' [simp]: "(\<delta> \<oplus> p) = p"
  apply (subst comm)
  by (rule plus0)

lemma leftDistr [simp]:  "do{x\<leftarrow>(p \<oplus> q); r x} = (do{x\<leftarrow> p; r x} \<oplus> do{x\<leftarrow> q; r x})"
 by (rule dist1)

lemma leftDistr1 [simp]:  "do{(p \<oplus> q); r} = (do{p; r} \<oplus> do{q; r})"
 apply (simp only: delBind [THEN sym])
 by (rule leftDistr)

lemma rightDistr [simp]:  "do{x\<leftarrow> p;(q x \<oplus> r x)} = (do{x\<leftarrow> p; q x} \<oplus> do{x\<leftarrow> p; r x})"
 by (rule dist2)

lemma rightDistr1 [simp]:  "do{p; (q \<oplus> r)} = (do{p; q} \<oplus> do{p; r})"
 apply (simp only: delBind [THEN sym])
 by (rule rightDistr)

lemma leftBindDelta [simp]:  "do{x\<leftarrow>\<delta>; r x} = \<delta>"
 by (rule bind01)

lemma leftBindDelta1 [simp]:  "do{\<delta>; r} = \<delta>"
 apply (simp only: delBind [THEN sym])
 by (rule bind01)

lemma rightBindDelta [simp]:  "do{x\<leftarrow> p; \<delta>} = \<delta>"
 by (rule bind02)

lemma rightBindDelta1 [simp]:  "do{p; \<delta>} = \<delta>"
 apply (simp only: delBind [THEN sym])
 by (rule bind02)

lemma ileq_assoc: 
  assumes "(a \<preceq> b)" and "(b \<preceq> c)"
  shows   "(a \<preceq> c)"
proof -
 have "(a \<oplus> (b \<oplus> c)) = (a \<oplus> c)" 
  using assms(2) by (unfold "ileq_def") simp
 hence "((a \<oplus> b) \<oplus> c) = (a \<oplus> c)"
  by (unfold "plus")
 (* with assms(1) *)
 hence "(b \<oplus> c) = (a \<oplus> c)"
  using assms(1) by (unfold "ileq_def") simp
 (* with assms(2) *)
 hence "c = (a \<oplus> c)"
  using assms(2) by (unfold "ileq_def") simp
 then show ?thesis 
  by (unfold "ileq_def") simp
qed

lemma ileq_asym:
  assumes "a \<preceq> b" and "b \<preceq> a"
  shows "a = b"
proof -
  have "b = (a \<oplus> b)" and "(b \<oplus> a) = a"
   using assms by (unfold "ileq_def") simp
  hence "b = (a \<oplus> b)" and "(a \<oplus> b) = a"
   by (unfold "comm")
  thus ?thesis by simp
qed

lemma ileqBindLeft: "(\<forall>x. p x \<preceq> q x) ==> do{ x \<leftarrow> r; p x} \<preceq> do{ x \<leftarrow> r; q x}"
apply (unfold ileq_def)
apply (subst dist2 [THEN sym])
by simp

lemma ileq_plus_cong: "[| p1 \<preceq> q1; p2 \<preceq> q2 |] ==> (p1 \<oplus> p2) \<preceq> (q1 \<oplus> q2)"
  apply (unfold ileq_def)
  apply (subst plus)
  apply (subst plus [THEN sym]) back
  apply (subst comm) back
  apply (subst plus)
  apply (subst plus [THEN sym])
  apply (rule_tac f="%x. %y. x \<oplus> y" in arg_cong2)
  by auto

lemma ileq_plus_cong1: "[| p1 \<preceq> q; p2 \<preceq> q |] ==> (p1 \<oplus> p2) \<preceq> q"
  apply (subst idmp [THEN sym])
  back
  back
  back
  apply (rule ileq_plus_cong)
  by auto
  
lemma ileq_plusMon: "p \<preceq> (p \<oplus> q)"
  apply (unfold ileq_def)
  apply (subst plus [THEN sym])
  by simp

lemma ileq_plusI: "(p \<preceq> q) ==> (p \<preceq> (r \<oplus> q))"
  apply (unfold ileq_def)
  apply (subst comm)
  apply (subst plus)
  apply (subst comm) back
  apply (erule ssubst)
  by auto

lemma ileq_plusE: "((r \<oplus> p) \<preceq> q) ==> (p \<preceq> q)"
  apply (unfold ileq_def)
  apply (subst comm)
  apply (erule subst)
  apply (simp only: plus)
  apply (subst comm) back
  apply (simp only: plus)
  apply (subst comm) back
  apply (subst idmp)
  by auto


interpretation induced_po: order ["ileq" "ile"]
apply unfold_locales
apply (unfold "ile_def")
apply simp
apply (unfold "ileq_def")
apply (unfold idmp)
apply simp
apply (fold "ileq_def")
apply (erule "ileq_assoc")
apply simp
apply (erule "ileq_asym")
apply simp
done

constdefs
  mnot :: "bool T \<Rightarrow> bool T"
  "mnot b == do {x \<leftarrow> b; ret (\<not> x)}" 
  test' :: "bool T \<Rightarrow> 'a \<Rightarrow> 'a T"
  "(test' b a) == do {x \<leftarrow> b; if x then ret a else \<delta>}" 
  test :: "bool T \<Rightarrow> unit T"
  "(test b) == do {x \<leftarrow> b; if x then (ret ()) else \<delta>}"
  mif :: "bool T \<Rightarrow> 'a T \<Rightarrow> 'a T \<Rightarrow> 'a T" ("if {_, _, _}")
  "mif b p q == do{test b; p} \<oplus> do{test (mnot b); q}"

lemma mifDistr: "do {x \<leftarrow> if {b, p, q}; t x} = if {b, do {x \<leftarrow> p; t x}, do {x \<leftarrow> q; t x}}"
  apply (unfold mif_def)
  apply (simp only: dist1)
  apply auto
done

lemma ifDistr1: "do {(if b then p else q); t} = (if b then do{p; t} else do {q; t})"
  apply (subst split_if) back
  apply simp
done

lemma testProp: "(test' b a) = do {test b; ret a}"
  apply (unfold test_def)
  apply (unfold test'_def)
  apply (simp add: ifDistr1)
  apply (subst fstUnitLaw1)     -- "Why the simplifier does not apply this rule itself?"
  apply (subst leftBindDelta1)
  by auto

(* Uncomment if needed
lemma testPlus [simp]: "test(a \<oplus> b) = (test(a) \<oplus> test(b))"
  sorry

lemma testBind [simp]: "test(do {x \<leftarrow> p; q x}) = do{x \<leftarrow> p; test(q x)}"
  sorry

lemma testBind1 [simp]: "test (do{p; q}) = do{p; test(q)}"
  sorry
*)

lemma testTrue [simp]: "test (ret \<top>) = ret ()"
  apply (unfold test_def)
  by simp
     
 
lemma testFalse [simp]: "test (ret \<bottom>) = \<delta>"
  apply (unfold test_def)
  by simp
	
      
lemma mnotTrue [simp]: "mnot (ret \<top>) = ret (\<bottom>)"
  apply (unfold mnot_def)
  by simp
	     
end

