theory KleeneSyntax imports MultimonadSyntax begin

text{*Definition of monad type and the two monadic funtions 
  \quak{@{text "\<guillemotright>="}} and ret *}

consts   
  uplus :: "('a \<Rightarrow> 'a T) \<Rightarrow> ('a \<Rightarrow> 'a T)" ("_^[+]" [1000] 999)

notation (xsymbols) uplus ("_\<^sup>+" [1000] 999)

axioms
 unf_left:   "(p^[+]) = (\<lambda>x. p x \<oplus> ((p^[+]) x \<guillemotright>= p))"
 unf_right:  "(p^[+]) = (\<lambda>x. p x \<oplus> (p x \<guillemotright>= (p^[+])))"
 ind_left:   "\<forall>x. ((p x \<guillemotright>= q) \<preceq> (q x)) \<Longrightarrow> \<forall>x. (((p^[+]) x \<guillemotright>= q) \<preceq> (q x))"
 ind_right:  "\<forall>x. ((p x \<guillemotright>= q) \<preceq> (p x)) \<Longrightarrow> \<forall>x. ((p x \<guillemotright>= (q^[+])) \<preceq> (p x))"

constdefs
  test :: "bool \<Rightarrow> unit T"
  "(test b) == if b then ret () else \<delta>" 

syntax
  "_monstar"  :: "[pttrn, 'a T, monseq]\<Rightarrow> monseq"  ("((_\<leftarrow>\<^sup>*(_));/ _)" [110,6,5]5)

translations
  "_monseq(_monstar x p q)"    => "(_monseq q) \<oplus> ((((%x. p)^[+]) x) \<guillemotright>= (%x. (_monseq q)))"
  "_monseq(_monstar x p q)"    <= "_monseq (_monstar x p (_monseq q))"

lemma unfLeft: "(do {x \<leftarrow>\<^sup>* p x; q x}) = (q x \<oplus> do{x \<leftarrow>\<^sup>* p x; x \<leftarrow> p x; q x})"
proof -
  have "(q x \<oplus> ((p^[+]) x \<guillemotright>= q)) = (q x \<oplus> (p x \<oplus> ((p^[+]) x \<guillemotright>= p) \<guillemotright>= q))"
    using unf_left [of p] by (rule_tac f="%z. (q x \<oplus> ((z x) \<guillemotright>= q))" in arg_cong, auto) (*, rule_tac x="x" in fun_cong, auto*)
  thus ?thesis by (simp add: dist1)
qed

lemma unfRight: "(do {x \<leftarrow>\<^sup>* p x; q x}) = (q x \<oplus> do{x \<leftarrow> p x; x \<leftarrow>\<^sup>* p x; q x})"
proof -
  have "(q x \<oplus> ((p^[+]) x \<guillemotright>= q)) = (q x \<oplus> (p x \<oplus> (p x \<guillemotright>= (p^[+])) \<guillemotright>= q))"
    using unf_right [of p] by (rule_tac f="%z. (q x \<oplus> ((z x) \<guillemotright>= q))" in arg_cong, auto)
  thus ?thesis by (simp add: dist2)
qed

lemma indLeft:
  assumes "\<forall>x. (do {x \<leftarrow> p x; q x})  \<preceq> q x"
  shows   "\<forall>x. (do {x \<leftarrow>\<^sup>* p x; q x}) \<preceq> q x"
proof-
  have "\<forall>x. (((p^[+]) x \<guillemotright>= q) \<preceq> (q x))"
    using assms by (rule ind_left)
  hence "\<forall>x. (q x = (((p^[+]) x \<guillemotright>= q) \<oplus> (q x)))"
    by (unfold "ileq_def") simp
  hence "\<forall>x. (q x = (((p^[+]) x \<guillemotright>= q) \<oplus> (q x) \<oplus> (q x)))"    
    by (simp add: idmp)
  hence "\<forall>x. (q x = ((q x) \<oplus> ((p^[+]) x \<guillemotright>= q) \<oplus> (q x)))"    
    by (unfold "comm") simp
  thus ?thesis
    by (unfold ileq_def) simp
qed

lemma indRight:
  assumes "\<forall>x. (do {x \<leftarrow> p x; q x})  \<preceq> p x"
  shows   "\<forall>x. (do {x \<leftarrow> p x; x \<leftarrow>\<^sup>* q x; r x}) \<preceq> do { x \<leftarrow> p x; r x}"  (is "ALL x. ?P x")
proof
  fix x
  have "\<forall>x. ((p x \<guillemotright>= (q^[+])) \<preceq> (p x))"
    using assms by (rule ind_right)
  hence "((p x \<guillemotright>= (q^[+])) \<preceq> (p x))"
    by auto
  hence "(p x = ((p x \<guillemotright>= (q^[+])) \<oplus> (p x)))"
    by (unfold "ileq_def") simp
  hence "((p x \<guillemotright>= r) = (((p x \<guillemotright>= (q^[+])) \<oplus> (p x)) \<guillemotright>=r))"    
    by (rule_tac f="%x. x \<guillemotright>= r" in arg_cong)
  hence "(p x \<guillemotright>= r) = ((p x \<guillemotright>= (q^[+]) \<guillemotright>=r) \<oplus> (p x \<guillemotright>=r))"    
    by (simp only: dist1)
  hence "(p x \<guillemotright>= r) = ((p x \<guillemotright>= (q^[+]) \<guillemotright>= r) \<oplus> (p x \<guillemotright>= r) \<oplus> (p x \<guillemotright>= r))"    
    by (simp add: idmp)
  hence "(p x \<guillemotright>= r) = (((p x \<guillemotright>= (\<lambda>x. (q^[+]) x \<guillemotright>= r)) \<oplus>  (p x \<guillemotright>= r)) \<oplus> (p x \<guillemotright>= r))"
    by (simp only: assoc)
  hence "(p x \<guillemotright>= r) = ((p x \<guillemotright>= (\<lambda>x. ((((q^[+]) x) \<guillemotright>= r) \<oplus> (r x)))) \<oplus> (p x \<guillemotright>= r) )"
    by (simp only: dist2)
  hence "(p x \<guillemotright>= r) = ( (p x \<guillemotright>= (\<lambda>x. ((r x) \<oplus> (((q^[+]) x) \<guillemotright>= r)))) \<oplus> (p x \<guillemotright>= r))"
    by (simp add: comm)
  hence "(p x \<guillemotright>= (\<lambda>x. ((r x) \<oplus> (((q^[+]) x) \<guillemotright>= r)))) \<preceq> (p x \<guillemotright>= r)"
    by (unfold ileq_def) simp
  thus "?P x" by auto
 qed

lemma bindStar: "do {x \<leftarrow> p x; x \<leftarrow>\<^sup>* p x; q x} = do { x \<leftarrow> do { x \<leftarrow>\<^sup>* p x; p x}; q x }"
apply (simp only: dist1 dist2 assoc [THEN sym])
apply (rule_tac f="%z. ((p x \<guillemotright>= q) \<oplus> z)" in arg_cong)
apply (rule_tac f="%z. (z \<guillemotright>= q)" in arg_cong)
apply (subst unf_left)
apply (rule sym)
apply (subst unf_right)
apply (simp only: dist1 dist2 assoc)

end
