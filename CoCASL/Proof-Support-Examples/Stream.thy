theory Stream = Main:

use tactics

ML"fun step1_fun thm = let val thms = (REPEAT (rtac disjI2 1) THEN (instantiate_tac [(\"R\" , \"Rcs union (Trans ?R)\" )])) thm in \
                            thms end" 

ML"fun step2_fun thm = let val thms = (REPEAT (rtac disjI2 1) THEN (instantiate_tac [(\"R\" , \"Rm union (Trans ?R)\" )])) thm in \
                            thms end" 

ML"fun step3_fun thm = let val thms = (REPEAT (rtac disjI2 1) THEN (instantiate_tac [(\"R\" , \"R0 union (Trans ?R)\" )])) thm in \
                            thms end" 

ML"fun close_or_step_fun thm = let val thms = ((close_fun) ORELSE ((solve_fun 1) THEN ((close_fun) ORELSE ((step_fun) THEN TRY (solve_fun 1) THEN TRY (rtac disjI2 1) THEN TRY (solve_fun 1) THEN TRY (xy_exI_fun) THEN (solve_fun 1) THEN TRY (close_fun)) THEN TRY(REPEAT(rtac disjI1 1) THEN (blast_tac (claset ()) 1 ) THEN (close_fun))))) thm in \
                           thms end"

ML"fun close_or_step2_fun thm = let val thms = ((close_fun) ORELSE ((solve_fun 1) THEN ((close_fun) ORELSE ((step2_fun) THEN TRY (solve_fun 1) THEN TRY (rtac disjI2 1) THEN TRY (solve_fun 1) THEN TRY (xy_exI_fun) THEN (solve_fun 1) THEN TRY (close_fun))) THEN TRY(REPEAT(rtac disjI1 1) THEN (blast_tac (claset ()) 1 ) THEN (close_fun)))) thm in \
                           thms end"

ML"fun close_or_step3_fun thm = let val thms = ((close_fun) ORELSE ((solve_fun 1) THEN ((close_fun) ORELSE ((step3_fun) THEN TRY (solve_fun 1) THEN TRY (rtac disjI2 1) THEN TRY (solve_fun 1) THEN TRY (xy_exI_fun) THEN (solve_fun 1) THEN TRY (close_fun))) THEN TRY(REPEAT(rtac disjI1 1) THEN (blast_tac (claset ()) 1 ) THEN (close_fun)))) thm in \
                           thms end"

ML"fun coinduction_fun1 thm= let val thms = 
                  ((SUBGOAL (fn (sub,_) => res_inst_tac [(\"R\",\"?Rzero\")] ((fn (x,_,_) => x) (get_cogeneration_axiom sub)) 1) 1) \ 
                  THEN (instantiate_Rzero_fun) \
                  THEN (step1_fun)) thm in \
                             thms end"

ML"fun coinduction_fun2 thm= let val thms = 
                  ((SUBGOAL (fn (sub,_) => res_inst_tac [(\"R\",\"?Rzero\")] ((fn (x,_,_) => x) (get_cogeneration_axiom sub)) 1) 1) \ 
                  THEN (instantiate_Rzero_fun) \
                  THEN (step2_fun)) thm in \
                             thms end"

ML"fun coinduction_fun3 thm= let val thms = 
                  ((SUBGOAL (fn (sub,_) => res_inst_tac [(\"R\",\"?Rzero\")] ((fn (x,_,_) => x) (get_cogeneration_axiom sub)) 1) 1) \ 
                  THEN (instantiate_Rzero_fun) \
                  THEN (step3_fun)) thm in \
                             thms end"

method_setup init = "build_tactic (init_fun)" "(simp|(solve,blast))?,init2_fun?"
method_setup solve= "build_tactic (solve_fun 1)" "((exE|conjE|conjI)+)?,(simp)?,((exE|conjE|conjI)+)?,(simp)?"
method_setup close= "build_tactic (close_fun)" "((disjI1|disjI2)+)?,((exE|conjE)+)?,force_solve|solve,disji1+,blast"
method_setup finish = "build_tactic (finish_fun)" "inst r false,solve1"
method_setup breakup = "build_tactic (breakup_fun)" "simp,((exE|conjE)+)?,disjE"
method_setup close_or_step= "build_tactic (close_or_step_fun)" "close|(solve,(close|(step,solve?,disjI2?,solve?,xy_exi?,solve,close?),((disjI1+)?,blast,close)?))"
method_setup close_or_step2= "build_tactic (close_or_step2_fun)" "close|(solve,(close|(step2,solve?,disjI2?,solve?,xy_exi?,solve,close?),((disjI1+)?,blast,close)?))"
method_setup close_or_step3= "build_tactic (close_or_step3_fun)" "close|(solve,(close|(step3,solve?,disjI2?,solve?,xy_exi?,solve,close?),((disjI1+)?,blast,close)?))"
method_setup step = "build_tactic (step_fun)" "((disjI2)+)?,inst r (rcs union (trans r))"
method_setup step1 = "build_tactic (step1_fun)" "((disjI2)+)?,inst r (rcs union (trans r))"
method_setup step2 = "build_tactic (step2_fun)" "((disjI2)+)?,inst r (rcs union (trans r))"
method_setup step3 = "build_tactic (step3_fun)" "((disjI2)+)?,inst r (rcs union (trans r))"
method_setup coinduction = "build_tactic (coinduction_fun)" "rule_tac R=?Rzero in ga_cogenerated, instantiate_tac Rzero %s1.?R,step"
method_setup coinduction1 = "build_tactic (coinduction_fun1)" "rule_tac R=?Rzero in ga_cogenerated, instantiate_tac Rzero %s1.?R,step"
method_setup coinduction2 = "build_tactic (coinduction_fun2)" "rule_tac R=?Rzero in ga_cogenerated, instantiate_tac Rzero %s1.?R,step"
method_setup coinduction3 = "build_tactic (coinduction_fun3)" "rule_tac R=?Rzero in ga_cogenerated, instantiate_tac Rzero %s1.?R,step"

typedecl "Elem"
typedecl "Stream"
consts
"cons" :: "Elem => Stream => Stream"
"hd" :: "Stream => Elem"
"tl" :: "Stream => Stream"
"first" :: "Stream => Stream"
"second" :: "Stream => Stream"
"third" :: "Stream => Stream"
"tripplemerge" :: "Stream => Stream => Stream => Stream"
"even" :: "Stream => Stream"
"merge" :: "Stream => Stream => Stream"
"odd" :: "Stream => Stream"
"const" :: "Elem => Stream"
"swap" :: "Elem => Elem => Stream"

consts
  BinRelImage :: "('a => 'b) => ('a => 'a => bool) => ('b => 'b => bool)"
  Trans_Stream :: "('a => 'a => bool) => ('b => 'b => bool)"
  union :: "('a => 'a => bool)  => ('a => 'a => bool) => ('a => 'a => bool)" (infixl 20)
defs
  BinRelImage_def [simp] : "BinRelImage f R == %x y . EX u v . R u v & x = f u & y = f v"
  Trans_Stream_def [simp] : "Trans_Stream R == (BinRelImage tl R)"
  union_def [simp] : "R union S == % x y . R x y | S x y"

axioms
const_hd [simp] : "!! e :: Elem . (hd (const e)) = e"
const_tl [simp] : "!! e :: Elem . (tl (const e)) = const e"
swap_hd [simp] : "!! e1 :: Elem . !! e :: Elem . (hd (swap e1 e2)) = e1"
swap_tl [simp] : "!! e1 :: Elem . !! e :: Elem . (tl (swap e1 e2)) = (swap e2 e1)"
first_hd [simp]: "!! s :: Stream . (hd (first s)) = (hd s)"
first_tl [simp]: "!! s :: Stream . (tl (first s)) = first (tl (tl (tl s)))"
second_hd [simp]: "!! s :: Stream . (hd (second s)) = (hd (tl s))"
second_tl [simp]: "!! s :: Stream . (tl (second s)) = second (tl (tl (tl s)))"
third_hd [simp]: "!! s :: Stream . (hd (third s)) = (hd (tl (tl s)))"
third_tl [simp]: "!! s :: Stream . (tl (third s)) = third (tl (tl (tl s)))"
tripplemerge_hd [simp]: "!! s1 :: Stream . !! s2 :: Stream . !! s3 :: Stream . (hd (tripplemerge s1 s2 s3)) = (hd s1)"
tripplemerge_tl [simp]: "!! s1 :: Stream . !! s2 :: Stream . !! s3 :: Stream . (tl (tripplemerge s1 s2 s3)) = tripplemerge s2 s3 (tl s1)"
odd_hd [simp]: "!! s :: Stream . (hd (odd s)) = (hd s)"
odd_tl [simp]: "!! s :: Stream . (tl (odd s)) = odd (tl (tl s))"
even_hd [simp]: "!! s :: Stream . (hd (even s)) = (hd (tl s))"
even_tl [simp]: "!! s :: Stream . (tl (even s)) = even (tl (tl s))"
merge_hd [simp]: "!! s1 :: Stream . !! s2 :: Stream . (hd (merge s1 s2)) = (hd s1)"
merge_tl [simp]: "!! s1 :: Stream . !! s2 :: Stream . (tl (merge s1 s2)) = merge s2 (tl s1)"

ga_cogenerated_Stream: "!! R :: Stream => Stream => bool . !! u :: Stream . !! v :: Stream . ! x :: Stream . ! y :: Stream . ((R x) y) --> ((hd x) = (hd y) & ((R (tl x)) (tl y)))  ==> ((R u) v) ==> u = v"
ga_selector_hd: "! X1 :: Elem . ! X2 :: Stream . (hd (cons X1 X2)) = X1"
ga_selector_tl: "! X1 :: Elem . ! X2 :: Stream . (tl (cons X1 X2)) = X2"


consts Rcs :: "[Stream, Stream] => bool"
defs Rcs_def [simp] : "Rcs == % x y . (? a b .(x=(merge (const a) (const b)) & y=(swap a b) ))"

theorem Stream_Const_Swap: "!! a :: Elem . !! b :: Elem . (merge (const a) (const b)) = (swap a b)"
apply(coinduction)
apply(init)

apply(breakup)

apply(close_or_step)

apply(finish)

done


consts R0 :: "[Stream, Stream] => bool"
defs R0_def [simp] : "R0 == % x y . (? s . (x=(tripplemerge (first s) (second s)(third s)) & y=s))"

theorem X8: "!! s :: Stream . ((tripplemerge (first s) (second s)) (third s)) = s"
apply(coinduction3)
apply(init)

apply(breakup)

apply(close_or_step3)

apply(breakup)

apply(close_or_step3)
apply(rule disjI2)
apply(rule_tac x=u in exI)
apply(rule_tac x=v in exI)
apply(close_or_step3)
apply(close_or_step3)

apply(breakup)

apply(close_or_step3)

apply(finish)

done


consts Rm :: "[Stream, Stream] => bool"
defs Rm [simp] : "Rm == % x y . (? s . (x=merge (odd s) (even s) & y=s))"

theorem Stream_Merge: "!! s :: Stream . merge (odd s) (even s) = s"
apply(coinduction2)
apply(init)

apply(breakup)

apply(close_or_step2)

apply(breakup)

apply(close_or_step2)

apply(finish)

done

end
