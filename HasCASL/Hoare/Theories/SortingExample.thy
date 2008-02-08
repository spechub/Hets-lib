theory SortExample imports KleeneSyntax begin

text {* This is a demonstration example tailored in order to expose 
Kleene Monad functionality. Here we introduce two different variants
of the BubbleSort algorithm and show their equivalence. *}   

syntax
  "_do_while" :: "[bool T, pttrn, 'a T, 'a T] \<Rightarrow> 'a T"  ("dowhile {_, _, _, _}")


-- "b - continuation condition"
-- "x - variable, providing an interface, between the neighbor steps of the loop"
-- "p - initial computation passed to the loop trought x"
-- "q - the loop's body"  
translations
  "dowhile {b, x, p, q}"  => "(q \<guillemotright>= ((%x. (test b) \<guillemotright> p)^[*]) \<guillemotright>= (test' (mnot b)))"

lemma whileUnf "dowhile {b, x, p, q} = dowhile {b, x, p, do {x \<leftarrow> q; if\<^isub>T b then p else \<delta> }}"


-- "example specific definitions"
consts
  "try_next" :: "bool T"
  "try_swap" :: "bool T"
  "go_home"  :: "unit T"
  "try_goto" :: "nat \<Rightarrow> bool T" 

constdefs
  "bubble_sort  == dowhile {ret b, b, 
                            dowhile {try_next, b, do {x \<leftarrow> try_swap; ret (b \<or> x)}, 
                                     do{go_home; ret \<bottom>}}, ret \<top>}"
  "bubble_sort' == dowhile {try_goto n, n, 
                            dowhile {try_next, b, do {try_swap; ret b}, 
                                     ret (n+1)}, ret 0}"


-- "proof of this theorem will call for some lemmas about @{const dowhile}"   
theorem "do{bubble_sort; ret ()} = do {bubble_sort'; ret ()}"
  sorry
			      
end
