theory BitStream = Main:

use tactics

ML"fun step_fun thm = let val thms = (REPEAT (rtac disjI2 1) THEN (instantiate_tac [(\"R\" , \"R0 union (Trans ?R)\" )])) thm in \
                            thms end" 

ML"fun close_or_step_fun thm = let val thms = ((close_fun) ORELSE ((solve_fun 1) THEN ((close_fun) ORELSE ((step_fun) THEN TRY (solve_fun 1) THEN TRY (rtac disjI2 1) THEN TRY (solve_fun 1) THEN TRY (xy_exI_fun) THEN (solve_fun 1) THEN TRY (close_fun)) THEN TRY(REPEAT(rtac disjI1 1) THEN (blast_tac (claset ()) 1 ) THEN (close_fun))))) thm in \
                           thms end"

ML"fun finish_fun thm = let val thms = ((instantiate_tac [(\"R\" , \"(BinRelImage tl (%x y. False))\" )]) THEN (solve_fun 1) THEN TRY(close_fun)) thm in \
                            thms end" 

ML"fun coinduction_fun thm= let val thms = 
                  ((SUBGOAL (fn (sub,_) => res_inst_tac [(\"R\",\"?Rzero\")] (get_cogeneration_axiom sub) 1) 1) \ 
                  THEN (instantiate_Rzero_fun) \
                  THEN (step_fun)) thm in \
                             thms end"

method_setup init = "build_tactic (init_fun)" "(simp|(solve,blast))?,init2_fun?"
method_setup breakup = "build_tactic (breakup_fun)" "simp,((exE|conjE)+)?,disjE"
method_setup solve= "build_tactic (solve_fun 1)" "((exE|conjE|conjI)+)?,(simp)?,((exE|conjE|conjI)+)?,(simp)?"
method_setup close= "build_tactic (close_fun)" "((disjI1|disjI2)+)?,((exE|conjE)+)?,force_solve"
method_setup finish = "build_tactic (finish_fun)" "inst r false,solve1"
method_setup close_or_step= "build_tactic (close_or_step_fun)" "close|(solve,(close|(step,solve?,disjI2?,solve?,xy_exi?,solve,close?),((disjI1+)?,blast,close)?))"
method_setup step = "build_tactic (step_fun)" "((disjI2)+)?,inst r (rcs union (trans r))"
method_setup coinduction = "build_tactic (coinduction_fun)" "rule_tac R=?Rzero in ga_cogenerated, instantiate_tac Rzero %s1.?R,step"

typedecl "BitStream"
datatype Bit = X0 | X1
consts
"flip" :: "BitStream => BitStream"
"hd" :: "BitStream => Bit"
"tl" :: "BitStream => BitStream"

consts
  BinRelImage :: "('a => 'b) => ('a => 'a => bool) => ('b => 'b => bool)"
  Trans :: "('a => 'a => bool) => ('b => 'b => bool)"
  union :: "('a => 'a => bool)  => ('a => 'a => bool) => ('a => 'a => bool)" (infixl 20)
defs
  BinRelImage_def [simp] : "BinRelImage f R == %x y . EX u v . R u v & x = f u & y = f v"
  Trans_def [simp] : "Trans R == (BinRelImage tl R)"
  union_def [simp] : "R union S == % x y . R x y | S x y"

axioms
ga_generated_Bit: "True"
ga_disjoint_0_1: "(Not (X0 = X1))"
flip_hd_a [simp]: "!! b :: BitStream . (hd b) = X1 ==> (hd (flip b)) = X0"
flip_hd_b [simp]: "!! b :: BitStream . (hd b) = X0 ==> (hd (flip b)) = X1"
flip_tl [simp]: "!! b :: BitStream . (tl (flip b)) = (flip (tl b))"
ga_cogenerated_BitStream: "!! R :: BitStream => BitStream => bool . !! u :: BitStream . !! v :: BitStream . ! x :: BitStream . ! y :: BitStream . ((R x) y) --> ((hd x) = (hd y) & ((R (tl x)) (tl y)))  ==> ((R u) v) ==> u = v"


consts R0 :: "[BitStream, BitStream] => bool"
defs R0_def [simp] : "R0 == % x y . (? b . (x=(flip (flip b)) & y=b))"

theorem X3: "!! b :: BitStream . (flip (flip b)) = b"
apply(coinduction)
apply(init)

apply(breakup)

apply(solve)
apply(case_tac "hd y")
apply(close)
apply(close)
apply(close)

apply(finish)

done
