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

lemma inv_lemma: "\<forall>x. ((p x \<guillemotright>= q) = (q x \<guillemotright>= r)) \<Longrightarrow> \<forall>x. (((p^[*]) x \<guillemotright>= q) = (q x \<guillemotright>= (r^[*])))"
  sorry 
 
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
  hence "\<forall>x. do {x \<leftarrow> r; x \<leftarrow> (p^[*]) x; q x} \<preceq> do {x \<leftarrow> r; q x}"
    by (rule ileqBindLeft)
  thus ?thesis by (subst assoc) simp
qed

lemma bindStar: "star {x \<leftarrow> do{x \<leftarrow> p; q x}; r x} = do {x \<leftarrow> p; star {x \<leftarrow> q x; r x}}"
  by simp

(* uncoment and fix, when needed *)
(*
-- "TODO: convert to the concrete synax, once it is decided"
lemma indLeftAlt: "(\<forall>x. (t x \<oplus> (p x \<guillemotright>= q)) \<preceq> q x) \<Longrightarrow> (\<forall>x. ((p^[*]) x \<guillemotright>= t) \<preceq> q x)"
sorry

-- "TODO: convert to the concrete synax, once it is decided"
lemma indRightAlt: "(\<forall>x. (t x \<oplus> (p x \<guillemotright>= q)) \<preceq> p x) \<Longrightarrow> (\<forall>x. (t x \<guillemotright>= (q^[*])) \<preceq> p x)"
sorry

lemma rev_lemma : "star {p \<leftarrow> do {reverse; ret p}; do{x \<leftarrow> pop; ret (do{p; push x})}} = 
                   do   {p \<leftarrow> star {p \<leftarrow> ret p; do{x \<leftarrow> pop; ret (do{push x; p})}}; do {reverse; ret p}}"
  apply (simp only: fstUnitLaw)
  apply (rule sym)
  apply (rule inv_lemma [THEN allE])
  prefer 2
  apply assumption
  apply simp


lemma starEq: "(\<forall>x. do{x \<leftarrow> a x; b x} = do {x \<leftarrow> b x; c x}) \<Longrightarrow> 
               (\<forall>x. do{x \<leftarrow> (a^[*]) x; b x} = do {x \<leftarrow> b x; (c^[*]) x})"
  apply (rule allI)
  apply (rule ileq_asym [THEN sym])
  apply (rule_tac b="do{x \<leftarrow> (a^[*]) x; x \<leftarrow> b x; (c^[*]) x}" in ileq_assoc)
  apply (subst unfRightStar) back back
  apply simp
  apply (rule ileq_plusMon)
  apply (simp only: assoc [THEN sym])
  apply (rule ind_right' [THEN allE])
  prefer 2
  apply (assumption) back back
  apply simp
  apply (subst (asm) expand_fun_eq [THEN sym])
  apply (rule_tac t="\<lambda>x.(b x \<guillemotright>= c)" in subst)
  apply assumption
  apply (subst unfLeftStar) back
  apply (simp (no_asm))
  apply (rule allI)
  apply (rule ileq_plusI)
  apply simp
  apply (rule_tac b="do{x \<leftarrow> (a^[*]) x; x \<leftarrow> b x; (c^[*]) x}" in ileq_assoc)
  apply (subst unfLeftStar) back back
  apply (simp (no_asm))
  apply (subst comm)
  apply (subst ileq_plusI)
  apply simp
  apply simp
  apply (rule ind_left' [THEN allE])
  prefer 2
  apply assumption
  apply (simp only: assoc [THEN sym])
  apply (subst (asm) expand_fun_eq [THEN sym])
  apply (erule ssubst)
  apply (rule allI)
  apply (subst unfRightStar) back back
  apply simp
  apply (rule ileq_plusI)
  by auto


(* while primitive and all that *)
syntax
  "_do_while" :: "['a T, pttrn, bool T, 'a T] \<Rightarrow> 'a T"  ("dowhile {_, (_), _, _}")

-- "b - continuation condition"
-- "x - variable, providing an interface, between the neighbor steps of the loop"
-- "p - initial computation passed to the loop trought x"
-- "q - the loop's body"  
translations
  "dowhile {p, x, b, q}"  => "(p \<guillemotright>= ((%x. (test b) \<guillemotright> q)^[*]) \<guillemotright>= (%x. test (mnot b) \<guillemotright> ret x))"

lemma whileUnit: "dowhile {p, x, b x, q x} = do {x \<leftarrow> p; dowhile {ret x, x, b x, q x}}"
 by simp
(* apply (simp only: assoc [THEN sym]) *)

lemma whileUnf: "dowhile {p, x, b x, q x} = do {x \<leftarrow> p; if{b x, dowhile {q x, x, b x, q x}, ret x}}"
  apply (simp only: assoc)
  apply (rule_tac f="%x. p \<guillemotright>= x" in arg_cong)
  apply (subst unfRightStar)
  apply (simp only: dist1)
  apply (unfold mif_def)
  apply (subst comm)
  by (simp add: testProp [THEN sym])

lemma whileInd: "(\<forall>x. if {b x, do {x \<leftarrow> q x; t x}, r x} \<preceq> t x) \<Longrightarrow> (\<forall>x. do{x \<leftarrow> dowhile {ret x, x, b x, q x}; r x} \<preceq> t x)"
  apply (unfold mif_def)
  apply (subst (asm) comm)
  apply (simp only: delBind [THEN sym] assoc [THEN sym])
  apply (simp only: delBind)
  apply (drule indLeftAlt)
  by simp

lemma whileEq: "do{x \<leftarrow> s; z \<leftarrow> a x; ret (x, z)} = do{x \<leftarrow> r; z \<leftarrow> b x; ret (x, z)} \<and> 
                (\<forall>x . do {test(a x); x \<leftarrow> p x; z \<leftarrow> a x; ret (x, z)} = 
                        do {test(a x); x \<leftarrow> q x; z \<leftarrow> b x; ret (x, z)}) \<Longrightarrow> 
                (dowhile {s, x, a x, p x} = dowhile {r, x, b x, q x})"
  apply (subst unfRightStar) back

  apply (simp only: dist1 dist2)
  apply (subst do_assoc2)
  apply (subgoal_tac "do {x\<leftarrow>r; test (b x); q x \<guillemotright>= (\<lambda>x. do {test (b x); q x})^[*]} = 
                      do {x\<leftarrow>s; test (a x); q x \<guillemotright>= (\<lambda>x. do {test (b x); q x})^[*]}")
  apply (erule ssubst)
  apply (subst do_assoc2 [THEN sym])
 
  apply (subgoal_tac "do {x \<leftarrow> s; do {test (a x); q x} \<guillemotright>= (\<lambda>x. do {test (b x); q x})^[*]} = 
                      do {x \<leftarrow> s; x \<leftarrow> ((\<lambda>x. do {test (a x); p x})^[*]) x; test (a x); q x}")
  apply (erule ssubst)
  apply simp
  apply (subgoal_tac "do {x\<leftarrow>r; test (mnot (b x)); ret x} = do {x\<leftarrow>s; test (mnot (a x)); ret x}")
  apply (erule ssubst)
  apply (subgoal_tac "do {x\<leftarrow>s; x\<leftarrow>((\<lambda>x. do {test (a x); p x})^[*]) x; test (a x); x\<leftarrow>q x; test (mnot (b x)); ret x} = 
                      do {x\<leftarrow>s; x\<leftarrow>((\<lambda>x. do {test (a x); p x})^[*]) x; test (a x); x\<leftarrow>p x; test (mnot (a x)); ret x}")
  apply (erule ssubst)
  apply (subst unfLeftStar)
  apply simp

  apply (rule_tac f="%u. do{x \<leftarrow>s; x\<leftarrow>((\<lambda>x. do {test (a x); p x})^[*]) x; u x}" in arg_cong)
  apply (rule sym)
  apply (subst expand_fun_eq)
  apply (drule conjunct2)
  apply (rule allI)
  apply (drule_tac x=x in spec)+
  apply (drule_tac f="%p. do {(x, z) \<leftarrow> p; test(ret(\<not>z)); ret x}" in arg_cong)
  apply (simp add: mnot_def)
  apply (rule sym)
  apply (drule conjunct1)
  apply (drule_tac f="%p. do {(x, z) \<leftarrow> p; test(ret(\<not>z)); ret x}" in arg_cong)
  apply (simp add: mnot_def)
  apply (rule_tac f="%p. do {x \<leftarrow> s; p x}" in arg_cong)
  apply (rule sym)
  apply (subst expand_fun_eq)

  apply (rule starEq)
  apply (drule conjunct2)
  apply (rule allI)
  apply (drule_tac x=x in spec)+
  apply (drule_tac f="%p. do {(x, z) \<leftarrow> p; test(ret z); q x}" in arg_cong)
  apply (simp add: test_def)
  apply (rule sym)
  apply (drule conjunct1)
  apply (drule_tac f="%p. do {(x, z) \<leftarrow> p; test(ret z); x \<leftarrow> q x; ((\<lambda>x. do {test (b x); q x})^[*]) x}" in arg_cong)
  by (simp add: test_def)

lemma addLoopVarRight: "do{z \<leftarrow> ((\<lambda>(x,y). do {x \<leftarrow> a x; ret (x, y)})^[*]) (p, q); ret (fst z)} = ((a^[*]) p)"
  apply (subst fst_conv [THEN sym, of p q]) back
  apply (subst lunit [THEN sym, of "(a^[*])"])
  apply (rule starEq [THEN allE])
  prefer 2
  apply assumption
  by simp

lemma addLoopVarLeft: "do{z \<leftarrow> ((\<lambda>(x,y). do {y \<leftarrow> a y; ret (x, y)})^[*]) (p, q); ret (snd z)} = ((a^[*]) q)"
  apply (subst snd_conv [THEN sym, of q p]) back
  apply (subst lunit [THEN sym, of "(a^[*])"])
  apply (rule starEq [THEN allE])
  prefer 2
  apply assumption
  by simp

lemma addLoopVarLeft1: "((\<lambda>(x,y). do {y \<leftarrow> a y; ret (x, y)})^[*]) (p, q) = do {y \<leftarrow> ((a^[*]) q); ret (p, y)}"
  apply (subst lunit [THEN sym, of "((\<lambda>(x, y). do {y\<leftarrow>a y; ret (x, y)})^[*])"])
  apply (rule sym)
  apply (rule starEq [THEN allE])
  prefer 2
  apply assumption
  by simp

constdefs
  "cp23 == \<lambda>(x, y, z). (x, y, y)"

lemma loopDia: "do {u \<leftarrow> ((\<lambda>(x, y, z). do {x \<leftarrow> a x y; ret (x, y, z)})^[*]) u; ret (cp23 u)} = 
                do {u \<leftarrow> ret (cp23 u); ((\<lambda>(x, y, z). do {x \<leftarrow> a x z; ret (x, y, z)})^[*]) u}"
  apply (rule starEq [THEN allE])
  prefer 2
  apply (erule subst) back back
  apply simp
  apply (unfold cp23_def)
  by simp

lemma loopConst: "do{(x,y) \<leftarrow> ((\<lambda>(x, y). do {y \<leftarrow> a p y; ret (x, y)})^[*])(p, q); ret (p, y)} = 
                  ((\<lambda>(x, y). do {y \<leftarrow> a x y; ret (x, y)})^[*])(p, q)"
  apply (subst lunit [THEN sym, of "((\<lambda>(x, y). do {y \<leftarrow> a x y; ret (x, y)})^[*])"])
  apply (rule starEq [THEN allE])
  prefer 2
  apply (erule ssubst)
  by simp+

lemma loopConst1: "do{(x,y) \<leftarrow> ((\<lambda>(x, y). do {y \<leftarrow> a p y; ret (p, y)})^[*])(p, q); ret (p, y)} = 
                   ((\<lambda>(x, y). do {y \<leftarrow> a x y; ret (x, y)})^[*])(p, q)"
  apply (subst lunit [THEN sym, of "((\<lambda>(x, y). do {y \<leftarrow> a x y; ret (x, y)})^[*])"])
  apply (rule starEq [THEN allE])
  prefer 2
  apply (erule ssubst)
  by simp+

lemma addLoopConst: "do {y \<leftarrow> ((a p)^[*]) q; ret (p, y)} = ((\<lambda>(x, y). do {y \<leftarrow> a x y; ret (x, y)})^[*])(p, q)"
  apply (subst addLoopVarLeft [THEN sym, of _ _ p])
  apply simp
  apply (subst lunit [THEN sym, of "((\<lambda>(x, y). do {y \<leftarrow> a x y; ret (x, y)})^[*])"])
  apply (rule starEq [THEN allE])
  prefer 2
  apply (erule ssubst)
  by simp+

lemma whileLVarIntro: "do {y \<leftarrow> dowhile {s, x, a x, p x}; ret (c, y)} = 
                       dowhile {do{x \<leftarrow> s; ret (c, x)}, z, a (snd z), do{y \<leftarrow> p (snd z); ret ((fst z), y)}}"
  apply simp
  apply (subgoal_tac "do{x \<leftarrow> s; ((\<lambda>z. do {test (a (snd z)); y\<leftarrow>p (snd z); ret (fst z, y)})^[*]) (c, x)} = 
                      do{x \<leftarrow> s; x \<leftarrow> ((\<lambda>x. do {test (a x); p x})^[*]) x; ret (c, x)}")
  apply (drule_tac f="%u. do {(x, y) \<leftarrow> u; test (mnot (a y)); ret (c, y)}" in arg_cong)
  apply simp
  apply (erule subst)
  apply (rule_tac f="%u. do {x \<leftarrow> s; u x}" in arg_cong)
  apply (subst expand_fun_eq)
  apply (rule allI)
  apply (subgoal_tac "((\<lambda>z. do {test (a (snd z)); y \<leftarrow>p (snd z); ret (fst z, y)})^[*]) (c, x) = 
                      ((\<lambda>(x, y). do {y \<leftarrow> do{test (a y); p y}; ret (x, y)})^[*]) (c, x)")
  apply (erule ssubst)

  apply (subst loopConst [THEN sym]) back
  apply simp+
  apply (subst split_beta)

  apply simp
  apply (rule_tac f="%u. ((\<lambda>(x, y). do {test (a y); y\<leftarrow>p y; ret (x, y)})^[*]) (c, x) \<guillemotright>= u" in arg_cong)

  apply (rule ext)
  apply(simp add: split_def)
  
  apply(simp add: split_def)

  apply (rule_tac f="%u. do {x \<leftarrow> s; u x}" in arg_cong)
  apply (rule ext)
  
  apply (subst addLoopVarLeft1 [THEN sym])
  apply (rule_tac f="%u. (u^[*]) (c, x)" in arg_cong)
  apply (rule ext)
  by(simp add: split_def)
 
lemma whileLVarIntro1: "dowhile {s, x, a x, p x} = 
                        do {(x, y) \<leftarrow> dowhile {do{x \<leftarrow> s; ret (c, x)}, z, a (snd z), do{y \<leftarrow> p (snd z); ret ((fst z), y)}}; ret y}"
  apply (insert whileLVarIntro [of s a p c])
  apply (drule_tac f="%u. do {(x, y) \<leftarrow> u; ret y}" in arg_cong)
  by simp

lemma addWhileConst: "do{y \<leftarrow> dowhile {s, y, a c y, p c y}; ret (c, y)} = 
                      dowhile {do{y \<leftarrow> s; ret (c, y)}, z, a (fst z) (snd z), do {y \<leftarrow> p (fst z) (snd z); ret (fst z, y)}}" 

  apply (insert addLoopConst [of "\<lambda>x. \<lambda>y. do {test (a x y); y \<leftarrow> p x y; ret y}" c])
  apply (drule ext)
  apply (drule_tac f="%u. do {y \<leftarrow> s; z \<leftarrow> u y; test (mnot (a (fst z) (snd z))); ret z}" in arg_cong)
  apply (simp)
  by (simp add: split_def)

lemma addWhileConst1: "dowhile {s, y, a c y, p c y} = 
                       do {(x, y) \<leftarrow> dowhile {do{y \<leftarrow> s; ret (c, y)}, z, a (fst z) (snd z), do {y \<leftarrow> p (fst z) (snd z); ret (fst z, y)}}; ret y}" 
  apply (insert addWhileConst [of s a c p])
  apply (drule_tac f="%u. do {(x, y) \<leftarrow> u; ret y}" in arg_cong)
  by simp

(*
lemma splitComm "(\<forall>x y. do {x' \<leftarrow> a x; y' \<leftarrow> b y; ret (x', y')} = do {y' \<leftarrow> b y; x' \<leftarrow> a x; ret (x', y')}) \<Longrightarrow>
                 ((\<lambda>(x,y). do {x' \<leftarrow> a x; y' \<leftarrow> b y; ret (x', y')})^[*]) (p, q) = do {x \<leftarrow> (a^[*]) p; y \<leftarrow> (b^[*]) q; ret (x, y)}"

*)

lemma starRegroup: "do {x \<leftarrow> a x; ((\<lambda>x. do {x \<leftarrow> b x; a x})^[*]) x} = do {x \<leftarrow> ((\<lambda>x. do {x \<leftarrow> a x; b x})^[*]) x; a x}"
  apply (rule sym)  
  apply (rule starEq [THEN allE])
  prefer 2
  apply assumption
  by simp


*)






end


