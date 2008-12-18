theory KleeneSyntax imports MultimonadSyntax begin

text{*Definition the Kleene star and acompanying constructions. *}

consts   
  ustar :: "('a \<Rightarrow> 'a T) \<Rightarrow> ('a \<Rightarrow> 'a T)" ("_^[*]" [1000] 999)

constdefs
  uplus :: "('a \<Rightarrow> 'a T) \<Rightarrow> ('a \<Rightarrow> 'a T)" ("_^[+]" [1000] 999)
  "(uplus f) == \<lambda>x. (f x \<guillemotright>= (f^[*]))"

notation (xsymbols) ustar ("_\<^sup>*" [1000] 999)
notation (xsymbols) uplus ("_\<^sup>+" [1000] 999)

axioms
 unf_right: "(p^[*]) = (\<lambda>x. ret x \<oplus> ((p^[*]) x \<guillemotright>= p))"
 unf_left:  "(p^[*]) = (\<lambda>x. ret x \<oplus> (p x \<guillemotright>= (p^[*])))"
 ind_right: "((p \<guillemotright>= q) \<preceq> p) \<Longrightarrow> ((p \<guillemotright>= (q^[*])) \<preceq> p)"
 ind_left:  "\<forall>x. ((p x \<guillemotright>= q) \<preceq> (q x)) \<Longrightarrow> \<forall>x. (((p^[*]) x \<guillemotright>= q) \<preceq> (q x))"

syntax
  "_monstar"  :: "monseq \<Rightarrow> 'a T" ("(star {(_)})"    [5] 100)

translations
  (* input macros; replace do-notation by bind/seq *)
  "_monstar(_mongen x p q)"    => "p \<guillemotright>= (%x. (_monseq q))^[*]"
  "_monstar(_monexp p q)"      => "p \<guillemotright>= (%_. (_monseq q))^[*]"
  "_monstar(_monexp0 q)"       => "((%_. q)^[*]) ()"
  (* Retranslation of bind/seq into do-notation *)
  "_monstar(_mongen x p q)"    <= "p \<guillemotright>= (%x. q)^[*]"
  "_monstar(_monexp p q)"      <= "p \<guillemotright>  (%x. q)^[*]"

  (* Normalization macros *)
  "_monstar(_monexp p q)"      <= "_monstar (_monexp p (_monseq q))"
  "_monstar(_mongen x p q)"    <= "_monstar (_mongen x p (_monseq q))"

lemma unfLeft: "(star {x \<leftarrow> p; q x}) = (p \<oplus> star {x \<leftarrow> do {x \<leftarrow> p; q x}; q x})"
proof -
  have "(star {x \<leftarrow> p; q x}) = do {x \<leftarrow>p; (ret x \<oplus> star {x \<leftarrow> q x; q x})}"
    using unf_left [of q] by (rule_tac f="%z. do {x \<leftarrow> p; z x}" in arg_cong)
  thus ?thesis by simp
qed

lemma unfRight: "(star {x \<leftarrow> p; q x}) = (p \<oplus> do{x \<leftarrow> star {x \<leftarrow> p; q x}; q x})"
proof -
  have  "(star {x \<leftarrow> p; q x}) = (do {x \<leftarrow> p; ret x \<oplus> do{x \<leftarrow> (q^[*]) x; q x}})"
    using unf_right [of q] by (rule_tac f="%z. do {x \<leftarrow> p; z x}" in arg_cong)
  thus ?thesis by (subst assoc) simp
qed

lemma indRight:
  assumes "do   {x \<leftarrow> p; q x} \<preceq> p"
  shows   "star {x \<leftarrow> p; q x} \<preceq> p"
proof-
  have "do {x \<leftarrow> p; q x} \<preceq> p"
    using assms by auto
  thus ?thesis
    by (rule ind_right)
qed

lemma indLeft:
  assumes "\<forall>x. do {x \<leftarrow> p x; q x}  \<preceq> q x"
  shows   "\<forall>x. do {x \<leftarrow> star {x \<leftarrow> r; p x}; q x} \<preceq> do {x \<leftarrow> r; q x}"
proof-
  have "\<forall>x. do {x \<leftarrow> (p^[*]) x; q x}  \<preceq> q x"
    using assms by (rule ind_left)
  hence "do {x \<leftarrow> r; x \<leftarrow> (p^[*]) x; q x} \<preceq> do {x \<leftarrow> r; q x}"
    by (rule ileqBindLeft)
  thus ?thesis by (subst assoc) simp
qed

lemma inv_lemma: "\<forall>x. ((p x \<guillemotright>= q) = (q x \<guillemotright>= r)) \<Longrightarrow> \<forall>x. (((p^[*]) x \<guillemotright>= q) = (q x \<guillemotright>= (r^[*])))"
  apply (rule allI)
  apply (rule ileq_asym)
  apply (rule_tac b="do {x \<leftarrow> (p^[*]) x; x \<leftarrow> q x; (r^[*]) x}" in ileq_assoc)
  apply (subst unf_right) back back
  apply simp
  apply (rule ileq_plusMon)
  apply (rule_tac x=x in spec)
  apply (rule ind_left)
  apply simp
  apply (subst assocLaw[THEN sym])
  apply (rule allI)
  apply (erule_tac x=x in allE)
  apply (erule ssubst)  
  apply (subst unf_left) back back
  apply simp
  apply (subst comm)
  apply (rule ileq_plusMon)
  
  apply (rule_tac b="do {x \<leftarrow> (p^[*]) x; x \<leftarrow> q x; (r^[*]) x}" in ileq_assoc)
  apply (subst unf_right) back
  apply simp
  apply (rule ileq_plusMon)
  apply (subst assocLaw[THEN sym])
  apply (rule ind_right) 
  apply simp  
  apply (rule_tac x=x in spec)
  apply simp
  apply (subgoal_tac "(\<lambda>x. do {x \<leftarrow> p x; q x}) = (\<lambda>x. do {x \<leftarrow> q x; r x})")
  apply (erule subst)
  apply (subst unf_right) back
  apply simp
  apply (subst comm)
  apply (rule allI)
  apply (rule ileq_plusMon)
  apply (rule ext)
  by simp

lemma bindStar: "star {x \<leftarrow> do{x \<leftarrow> p; q x}; r x} = do {x \<leftarrow> p; star {x \<leftarrow> q x; r x}}"
  by simp

lemma ret_star: "star {x \<leftarrow> p; q x} = do {p \<leftarrow> star {p \<leftarrow> ret p; ret (do{x \<leftarrow>  p; q x})}; p}"
  apply simp
  apply (rule sym)
  apply (rule inv_lemma [THEN allE])
  prefer 2
  apply assumption 
  by simp

lemma starTensorRight: "do {x \<leftarrow> star {x \<leftarrow> p; q x}; r x y} = 
                        do {(x, y) \<leftarrow> star {(x, y) \<leftarrow> do {x \<leftarrow> p; ret (x, y)}; x \<leftarrow> q x; ret (x, y)}; r x y}"
  apply (subgoal_tac "do {x\<leftarrow>(p \<guillemotright>= q\<^sup>*); r x y} = do {(x, y) \<leftarrow> do {x\<leftarrow>(p \<guillemotright>= q\<^sup>*); ret (x, y)}; r x y}")
  apply (erule ssubst)
  apply (rule_tac f="%u. do {(x, y) \<leftarrow> u; r x y}" in arg_cong)
  apply simp
  apply (rule_tac f="%u. do {x \<leftarrow> p; u x}" in arg_cong)
  apply (rule ext)
  apply (rule trans)
  apply (rule inv_lemma [THEN allE])
  prefer 2
  apply assumption
  prefer 2
  apply simp
  apply simp
  apply simp
done
lemma starTensorLeft: "do {x \<leftarrow> star {x \<leftarrow> p; q x}; r y x} = 
                        do {(y, x) \<leftarrow> star {(y, x) \<leftarrow> do {x \<leftarrow> p; ret (y, x)}; x \<leftarrow> q x; ret (y, x)}; r y x}"
  apply (subgoal_tac "do {x\<leftarrow>(p \<guillemotright>= q\<^sup>*); r y x} = do {(y, x) \<leftarrow> do {x\<leftarrow>(p \<guillemotright>= q\<^sup>*); ret (y, x)}; r y x}")
  apply (erule ssubst)
  apply (rule_tac f="%u. do {(y, x) \<leftarrow> u; r y x}" in arg_cong)
  apply simp
  apply (rule_tac f="%u. do {x \<leftarrow> p; u x}" in arg_cong)
  apply (rule ext)
  apply (rule trans)
  apply (rule inv_lemma [THEN allE])
  prefer 2
  apply assumption
  prefer 2
  apply simp
  apply simp
  apply simp
done


lemma cutStar0: 
  assumes "\<forall>a b. F (a \<oplus> b) = (F a \<oplus> F b)"
  shows   "F p \<preceq> F (star {x \<leftarrow> p; q x})"
proof-
  have  "F (star {x \<leftarrow> p; q x}) = (F p \<oplus> F (star {x \<leftarrow> do {x \<leftarrow> p; q x}; q x}))"
    using assms [THEN spec [of _ p], THEN spec [of _ "star {x \<leftarrow> do {x \<leftarrow> p; q x}; q x}"]] by (subst unfLeft)
  hence "(F p \<oplus> F (star {x \<leftarrow> do {x \<leftarrow> p; q x}; q x})) \<preceq> F (star {x \<leftarrow> p; q x})"
    by simp
  thus ?thesis
    by (subst (asm) comm) (rule ileq_plusE)
qed   

lemma cutStar1: 
  assumes "\<forall>a b. F (a \<oplus> b) = (F a \<oplus> F b)"
  shows   "F (do {x \<leftarrow> p; q x}) \<preceq> F (star {x \<leftarrow> p; q x})"
proof-
  from assms have A:"F (do {x \<leftarrow> p; q x}) \<preceq> F (star {x \<leftarrow> do {x \<leftarrow> p; q x}; q x})"
    proof-
      assume "\<forall>a b. F (a \<oplus> b) = (F a \<oplus> F b)"
      thus ?thesis by (rule cutStar0 [of F "do {x \<leftarrow> p; q x}" q])
    qed
  from assms [THEN spec [of _ p], THEN spec [of _ "star {x \<leftarrow> do {x \<leftarrow> p; q x}; q x}"]]
    have "F (star {x \<leftarrow> p; q x}) = (F p \<oplus> F (star {x \<leftarrow> do {x \<leftarrow> p; q x}; q x})) "
      by (subst unfLeft) simp
    hence "(F p \<oplus> F (star {x \<leftarrow> do {x \<leftarrow> p; q x}; q x})) \<preceq> F (star {x \<leftarrow> p; q x})"
      by simp
    hence B: "F (star {x \<leftarrow> do {x \<leftarrow> p; q x}; q x}) \<preceq> F (star {x \<leftarrow> p; q x})"
      by (rule ileq_plusE)
  from A and B show ?thesis
    by (rule ileq_assoc)
qed 
end


