theory BinTrees = Main:

use tactics

ML"fun step_fun thm = let val thms = (REPEAT (rtac disjI2 1) THEN (instantiate_tac [(\"R\" , \"Rm union (Trans ?R)\" )])) thm in \
                            thms end" 

ML"fun close_or_step_fun thm = let val thms = ((close_fun) ORELSE ((solve_fun 1) THEN ((close_fun) ORELSE ((step_fun) THEN TRY (solve_fun 1) THEN TRY (rtac disjI2 1) THEN TRY (solve_fun 1) THEN TRY (xy_exI_fun) THEN (solve_fun 1) THEN TRY (close_fun)) THEN TRY(REPEAT(rtac disjI1 1) THEN (blast_tac (claset ()) 1 ) THEN (close_fun))))) thm in \
                           thms end"

ML"fun coinduction_fun thm= let val thms = 
                  ((SUBGOAL (fn (sub,_) => res_inst_tac [(\"R\",\"?Rzero\")] (get_cogeneration_axiom sub) 1) 1) \ 
                  THEN (instantiate_Rzero_fun) \
                  THEN (step_fun)) thm in \
                             thms end"

method_setup init = "build_tactic (init_fun)" "(simp|(solve,blast))?,init2_fun?"
method_setup solve= "build_tactic (solve_fun 1)" "((exE|conjE|conjI)+)?,(simp)?,((exE|conjE|conjI)+)?,(simp)?"
method_setup close= "build_tactic (close_fun)" "((disjI1|disjI2)+)?,((exE|conjE)+)?,force_solve"
method_setup breakup = "build_tactic (breakup_fun)" "simp,((exE|conjE)+)?,disjE"
method_setup xy_exI = "build_tactic (xy_exI_fun)" "rule_tac x=x in exI, rule_tac x=y n exI"
method_setup finish = "build_tactic (finish_fun)" "inst r false,solve1"
method_setup close_or_step= "build_tactic (close_or_step_fun)" "close|(solve,(close|(step,solve?,disjI2?,solve?,xy_exi?,solve,close?)))"
method_setup step = "build_tactic (step_fun)" "((disjI2)+)?,inst r (rcs union (trans r))"
method_setup coinduction = "build_tactic (coinduction_fun)" "rule_tac R=?Rzero in ga_cogenerated, instantiate_tac Rzero %s1.?R,step"

typedecl "BinTree"
typedecl "Elem"
consts
"cons" :: "BinTree => Elem => BinTree => BinTree"
"left" :: "BinTree => BinTree"
"mirror" :: "BinTree => BinTree"
"node" :: "BinTree => Elem"
"right" :: "BinTree => BinTree"

consts
  BinRelImage :: "('a => 'b) => ('a => 'a => bool) => ('b => 'b => bool)"
  Trans :: "('a => 'a => bool) => ('b => 'b => bool)"
  union :: "('a => 'a => bool)  => ('a => 'a => bool) => ('a => 'a => bool)" (infixl 20)
defs
  BinRelImage_def [simp] : "BinRelImage f R == %x y . EX u v . R u v & x = f u & y = f v"
  Trans_def [simp] : "Trans R == (BinRelImage left R) union (BinRelImage right R)"
  union_def [simp] : "R union S == % x y . R x y | S x y"

axioms
mirror_left [simp]: "!! bt1 :: BinTree . (left (mirror bt1)) = (mirror (right bt1))"
mirror_node [simp]: "!! bt1 :: BinTree . (node (mirror bt1)) = (node bt1)"
mirror_right [simp]: "!! bt1 :: BinTree . (right (mirror bt1)) = (mirror (left bt1))"
ga_cogenerated_BinTree: "!! R :: BinTree => BinTree => bool . !! u :: BinTree .
!! v :: BinTree . ! x :: BinTree . ! y :: BinTree . ((R x) y) --> (((R (left x))
 (left y)) & (node x) = (node y) & ((R (right x)) (right y))) ==> ((R u) v) ==>
u = v"
ga_selector_left: "!! X1 :: BinTree . !! X2 :: Elem . !! X3 :: BinTree . (left ((cons X1 X2) X3)) = X1"
ga_selector_node: "!! X1 :: BinTree . !! X2 :: Elem . !! X3 :: BinTree . (node ((cons X1 X2) X3)) = X2"
ga_selector_right: "!! X1 :: BinTree . !! X2 :: Elem . !! X3 :: BinTree . (right ((cons X1 X2) X3)) = X3"


consts Rm :: "[BinTree, BinTree] => bool"
defs Rm_def [simp] : "Rm == % x y . (? t . (x=(mirror (mirror t)) & y=t))"

theorem BinTree_Mirror: "!! bt :: BinTree . (mirror (mirror bt)) = bt"
apply(coinduction)
apply(init)

apply(breakup)

apply(close_or_step)

apply(finish)
done



