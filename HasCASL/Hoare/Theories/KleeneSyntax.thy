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
  ustar :: "('a \<Rightarrow> 'a T) \<Rightarrow> ('a \<Rightarrow> 'a T)" ("_^[*]" [1000] 999)
  "(ustar f) == \<lambda>x. (ret x) \<oplus> (f^[+]) x"

axioms
 -- "quick and dirty solution. fix it!"
 ind_left':   "(\<forall> x. (p x \<guillemotright>= q) \<preceq> (q x)) \<Longrightarrow> (\<forall>x. ((p^[*]) x \<guillemotright>= q) \<preceq> (q x))"
 ind_right':  "(\<forall> x. (p x \<guillemotright>= q) \<preceq> (p x)) \<Longrightarrow> (\<forall>x. (p x \<guillemotright>= (q^[*])) \<preceq> (p x))"

  
syntax
  "_monstar"  :: "[pttrn, 'a T, monseq]\<Rightarrow> monseq"  ("((_\<leftarrow>\<^sup>*(_));/ _)" [110,6,5]5)

translations
  "_monseq(_monstar x p q)"    => "(_monseq q) \<oplus> ((((%x. p)^[+]) x) \<guillemotright>= (%x. (_monseq q)))"
  "_monseq(_monstar x p q)"    <= "_monseq (_monstar x p (_monseq q))"


lemma unfRightStar: "(p^[*]) = (\<lambda>x. (ret x) \<oplus> (p x \<guillemotright>= (p^[*])))"
  apply (unfold ustar_def)
  apply (rule_tac f="%z. \<lambda>x. (ret x) \<oplus> z x" in arg_cong)
  apply (simp only: dist2 runit)
  apply (subst unf_right)
  by auto
  
lemma unfLeftStar: "(p^[*]) = (\<lambda>x. (ret x) \<oplus> ((p^[*]) x \<guillemotright>= p))"
  sorry  

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
done

-- "TODO: convert to the concrete synax, once it is decided"
lemma indLeftAlt: "(\<forall>x. (t x \<oplus> (p x \<guillemotright>= q)) \<preceq> q x) \<Longrightarrow> (\<forall>x. ((p^[*]) x \<guillemotright>= t) \<preceq> q x)"
sorry

-- "TODO: convert to the concrete synax, once it is decided"
lemma indRightAlt: "(\<forall>x. (t x \<oplus> (p x \<guillemotright>= q)) \<preceq> p x) \<Longrightarrow> (\<forall>x. (t x \<guillemotright>= (q^[*])) \<preceq> p x)"
sorry

lemma testTrue [simp]: 
 "test (ret \<top>) = ret ()"
  apply (unfold test_def)
  by simp

lemma testFalse [simp]: 
 "test (ret \<bottom>) = \<delta>"
  apply (unfold test_def)
  by simp

lemma mnotTrue [simp]: 
 "mnot (ret \<top>) = ret (\<bottom>)"
 apply (unfold mnot_def)
 by simp

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









end


