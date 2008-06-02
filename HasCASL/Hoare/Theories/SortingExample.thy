theory SortingExample imports KleeneSyntax begin

text {* This is a demonstration example tailored in order to expose 
Kleene Monad functionality. Here we introduce two different variants
of the BubbleSort algorithm and show their equivalence. *}   

syntax
  "_do_while" :: "['a T, pttrn, bool T, 'a T] \<Rightarrow> 'a T"  ("dowhile {_, _, _, _}")


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

-- "example-specific definitions"
consts
  "try_next" :: "bool T"
  "try_swap" :: "bool T"
  "go_home"  :: "unit T"
  "try_goto" :: "nat \<Rightarrow> bool T" 

axioms

  goto_next:  "do{try_goto n; try_next} = try_goto (n + 1)"
  goto_dup:   "do{try_goto n; test(try_next); x \<leftarrow> try_swap; r x} = do{try_goto n; test(try_next); x \<leftarrow> try_swap; try_goto (n+1); r x}"
  test_goto:  "test(try_goto (Succ n)) = do{test (try_goto n); test try_next}"
  test_goto1: "test(nmot(try_goto (Succ n))) = do{test (try_goto n); test(mnot try_next)}"

constdefs
  "bubble_sort  == dowhile {ret \<top>, b, ret b,
                            dowhile {do{go_home; ret \<bottom>}, b, try_next, do {x \<leftarrow> try_swap; ret (b \<or> x)}}}"

  "bubble_sort' == dowhile {ret 0, n, try_goto n,
                            do{ dowhile {ret (), x, try_next, do{try_swap; ret ()}}; ret (n + 1)}}"

  "sort_once n == do{try_goto n; dowhile {ret \<bottom>, b, try_next, do {x \<leftarrow> try_swap; ret (b \<or> x)}}}"
  "so x == dowhile {ret x, b, try_next, do {x \<leftarrow> try_swap; ret (b \<or> x)}}"
  "son x n == if {try_goto n, so x, ret \<bottom>}"
(*
  "full_sort n == dowhile {ret(), x, ret \<top>, sort_once n}"
*)
lemma while_eq: "[| do {z \<leftarrow> a m z; z \<leftarrow> r z; a z z} = do {z \<leftarrow> a m z; z \<leftarrow> r z; a m z} |] ==> 
                 ((\<lambda>z. do {z \<leftarrow> a z z; r z})^[*]) n = ((\<lambda>z. do {z \<leftarrow> a n z; r z})^[*]) n"
sorry

lemma while_eq': "[| do {a z; y \<leftarrow> r z; a y} = do {a z; y \<leftarrow> r z; a z} |] ==> 
                      ((\<lambda>z. do {a z; r z})^[*]) n = ((\<lambda>z. do {a n; r z})^[*]) n"
  apply (rule ileq_asym)
  sorry  

lemma soUnf: "so x = if{try_next, do{b \<leftarrow> try_swap; so (x \<or> b)}, ret x}"
  apply (subst lunit [THEN sym])
  back back back back back back back 
  back back back back back back back 
  back back back
  apply (unfold so_def)
  apply (subst whileUnit) back
  apply (subst whileUnf)
  by simp 

lemma soGuard: "do{test(try_goto n); so x} = if{try_goto (n + 1), do {b \<leftarrow> try_swap; so (x \<or> b)}, ret x}"
  apply (subst soUnf)
  apply (unfold mif_def)
  apply simp
  apply (subst test_goto) back back back back back
  apply simp
  apply (subst test_goto1) back back back back back back back back back back back back back
  by simp

lemma tryGoto: "try_goto (n+1) = if{try_goto n, try_next, ret \<bottom>}"
  sorry

lemma testPlus [simp]: "test(a \<oplus> b) = (test(a) \<oplus> test(b))"
  sorry

lemma testBind [simp]: "test(do {x \<leftarrow> p; q}) = do{x \<leftarrow> p; test(q)}"
  sorry

lemma testBind1 [simp]: 
  "test (do{p; q}) = do{p; test(q)}"
  sorry

lemma soGt: "test (son \<bottom> n) = do{test(son \<bottom> n); test(try_goto (n + 1))}"
  sorry

lemma tsMain1: "test (so \<bottom>) = do{ test (ts \<bottom>); test(try_goto n)}"
  sorry

lemma tsMain2: "do{test (so \<bottom>); test(try_goto n); test(try_swap)} = \<delta>"
  sorry

lemma tsMain3: "do{test(son \<bottom> n); test(son \<bottom> n)} = do{test(son \<bottom> n); test(son \<bottom> (n+1))}"
  apply (subst soGt)
  apply simp
  apply (subst son_def) back
  apply (subst soUnf)
  

lemma soSort: "test(son \<bottom> n) = do{test(try_goto(n+1)); test(try_swap); test(son \<bottom> (n + 1))}"
  apply (subst soGt)
  apply (unfold son_def)
  apply (unfold mif_def)
  apply simp
  apply(insert testBind1[of "test (try_goto n)"])
  apply (subst testBind1)
  apply simp
  apply (subst soUnf)
  apply (unfold mif_def)
  apply simp
  
  apply (subst tryGoto)
  apply (unfold mif_def)
  sorry

lemma soFalse: "(so x) = do {b \<leftarrow> (so \<bottom>); ret (x \<or> b)}"
  sorry


lemma testSeq: "do{test a; test b} = test (do{x \<leftarrow> a; y \<leftarrow> b; ret (x \<and> y)})"
  sorry 

(*
lemma nestIf: "if{b, if{c, p, q}, do{c; q}} = if{do{x\<leftarrow>b; y\<leftarrow>c; ret (x\<and>y)}, p, q}"
  apply (unfold mif_def)
  apply (subst testSeq [THEN sym])
  apply simp
  apply (unfold mnot_def)
  apply simp
*)

(*
lemma soTwice: "son n = if{try_goto (n+1), do{b \<leftarrow> try_swap; x \<leftarrow> son (n + 1); ret (a \<or> x)}, ret \<bottom>}"
  apply (subst son_def)
  apply (subst soUnf)
  apply (unfold mif_def)
  apply (subst test_goto)
  apply simp
  apply (subst son_def)
  apply (subst testSeq)
  apply (rule_tac f="%x. %y. (x \<oplus> y)" in arg_cong2)
  apply (subst soUnf)
  apply simp
  apply (simp only: delBind [THEN sym])
  apply (subst dist2 [THEN sym])
  apply (simp only: delBind)
  apply (mif_def [THEN sym])
*)

lemma eq1: "((\<lambda>m. do{test(sort_once m); ret (m + 1)})^[*]) n = 
            ((\<lambda>m. do{test(sort_once n); ret (m + 1)})^[*]) n"
  apply (rule while_eq')
  apply simp


lemma full_sort_unf_aux: "do {x \<leftarrow> ret n; ((\<lambda>m. do{sort_once n; ret (m + 1)})^[*]) x} = 
                          do {x \<leftarrow> ret n; ((\<lambda>m. do{sort_once m; ret (m + 1)})^[*]) x}"
(*  apply (subst lunit [THEN sym]) back back back back back back back back back back back back back back back back back back back back
*)
  apply (rule while_eq)
  apply simp
  apply (subst sort_once_def)
  back
  apply simp
  apply simp

lemma full_sort_unf: "((\<lambda>x. sort_once n)^[*])() \<preceq> do{((\<lambda>n. do{sort_once n; ret (n + 1)})^[*]) n; ret ()}"
  apply (subst unfRightStar)
  apply (rule ileq_plus_cong1)
  apply (subst unfRightStar)
  apply simp
  apply (rule ileq_plusE)
  apply (rule ind_right')
  apply simp
  apply (unfold full_sort_def)
  apply simp

lemma bubble'_full: "\<forall>m. do{ dowhile {ret m, n, try_goto n,
                                  do{ dowhile {ret (), x, try_next, do{try_swap; ret ()}}; ret (n + 1)}}; ret ()} \<preceq>  
                          full_sort m"
  apply (subst delBind [THEN sym]) 
  back back back back back back
  apply (rule whileInd)
  apply (unfold mif_def)
  apply (rule allI)
  apply (rule ileq_plus_cong1)
  apply simp
  apply (subst full_sort_def) back
  apply simp
  apply (unfold sort_once_def)
  apply (subst whileUnit)
  apply simp














lemma Lbubble: "\<forall>x. do{dowhile {ret x, n, try_goto n,
                                        dowhile {ret (n+1), b, try_next, do {try_swap; ret b}}}; ret ()} \<preceq> 
                            do{dowhile {ret \<top>, b, ret b,
                                        dowhile {do{try_goto x; ret \<bottom>}, b, try_next, do {x \<leftarrow> try_swap; ret (b \<or> x)}}}; ret ()}"
  apply (subst delBind [THEN sym])
  back back back back back
  apply (rule whileInd)
  apply (rule allI)
  apply (unfold mif_def)
  apply (rule ileq_plus_cong1)
  apply (subst whileUnf)
  back back back back
  apply simp
  apply (unfold mif_def)
  apply simp
  apply (subst idmp [THEN sym])

lemma Rbubble: "do{bubble_sort; ret ()} \<preceq> do {bubble_sort'; ret ()}"

-- "proof of this theorem will call for some lemmas about @{const dowhile}"   
theorem "do{bubble_sort; ret ()} = do {bubble_sort'; ret ()}"
  sorry
			      
end
