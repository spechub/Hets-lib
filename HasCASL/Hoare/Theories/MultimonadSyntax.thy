theory MultimonadSyntax imports MonadSyntax begin

text{*Definition of multiomonad operations: nondeterministic choice 
      \quak{@{text "\<oplus>"}} and deadlock \quak{@{text "\<delta>"}}*}

consts   
  choice  :: "('a T \<Rightarrow> 'a T \<Rightarrow> 'a T)"    (infixl "\<oplus>" 10)
  zero    :: "'a T" ("\<delta>")  

constdefs
  ileq   :: "('a T \<Rightarrow> 'a T \<Rightarrow> bool)"   (infix "\<preceq>" 10)
  "(p \<preceq>  q) == ((p \<oplus> q) = q)"
  
  ile    :: "('a T \<Rightarrow> 'a T \<Rightarrow> bool)"   (infix "\<prec>" 10)
  "(p \<prec> q ) == ((p \<preceq> q) \<and> (p \<noteq> q))"

axioms
 plus0:            "(p \<oplus> \<delta>) = p"
 comm:             "(p \<oplus> q) = (q \<oplus> p)"
 idmp:             "(p \<oplus> p) = p"
 plus:             "((p \<oplus> q) \<oplus> r) = (p \<oplus> (q \<oplus> r))"
 dist1:            "((p \<oplus> q) \<guillemotright>= r) = ((p \<guillemotright>= r) \<oplus> (q \<guillemotright>= r))" 
 dist2:            "(p \<guillemotright>= (\<lambda>x. (q x \<oplus> r x))) = ((p \<guillemotright>= q) \<oplus> (p\<guillemotright>= r))"
 bind01:           "(\<delta> \<guillemotright>= r) = \<delta>" 
 bind02:           "(p \<guillemotright>= (\<lambda>x. \<delta>)) = \<delta>"

lemma leftDistr [simp]:  "do{x\<leftarrow>(p \<oplus> q); r x} = (do{x\<leftarrow> p; r x} \<oplus> do{x\<leftarrow> q; r x})"
 by (rule dist1)

lemma rightDistr [simp]:  "do{x\<leftarrow> p;(q x \<oplus> r x)} = (do{x\<leftarrow> p; q x} \<oplus> do{x\<leftarrow> p; r x})"
 by (rule dist2)

lemma leftBindDelta [simp]:  "do{x\<leftarrow>\<delta>; r x} = \<delta>"
 by (rule bind01)

lemma rightBindDelta [simp]:  "do{x\<leftarrow> p; \<delta>} = \<delta>"
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
end

