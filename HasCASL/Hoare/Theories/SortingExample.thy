theory SortExample imports KleeneSyntax begin
  
syntax
  "_do_while" :: "[bool T, pttrn, 'a T, 'a T] \<Rightarrow> 'a T"  ("dowhile {_, _, _, _}")
  
translations
  "dowhile {b, x, p, q}"  => "(q \<guillemotright>= ((%x. (test b) \<guillemotright> p)^[*]))"

-- "example specific definitions"
consts
  "try_next" :: "bool T"
  "try_swap" :: "bool T"
  "go_home"  :: "unit T"
  "try_goto" :: "nat \<Rightarrow> bool T" 

(*  "p == dowhile {ret b, b, ret b, ret True}" *)

constdefs
  "bubble_sort  == dowhile {ret b, b, dowhile {try_next, b, do {x \<leftarrow> try_swap; ret (b \<or> x)}, do{go_home; ret \<bottom>}}, ret \<top>}"
  "bubble_sort' == dowhile {try_goto n, n, dowhile {try_next, b, do {try_swap; ret b}, ret (n+1)}, ret 0}"
   
theorem "do{bubble_sort; ret ()} = do {bubble_sort'; ret ()}"
  sorry
			      
end
