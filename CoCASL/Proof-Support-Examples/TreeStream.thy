theory TreeStream = Main:

use tactics

method_setup circular_coinduction = "build_tactic (circular_coinduction_fun)" "all"
method_setup coinduction = "build_tactic (coinduction_fun)" "rule_tac R=?Rzero in ga_cogenerated, instantiate_tac Rzero %s1.?R,step"
method_setup coinduction_test = "build_tactic (coinduction_test_fun)" "rule_tac R=?Rzero in ga_cogenerated, instantiate_tac Rzero %s1.?R,step"
method_setup init = "build_tactic (init_fun)" "(simp|(solve,blast))?,init2_fun?"
method_setup breakup = "build_tactic (breakup_fun)" "simp,((exE|conjE)+)?,disjE"
method_setup solve= "build_tactic (solve_fun 1)" "((exE|conjE|conjI)+)?,(simp)?,((exE|conjE|conjI)+)?,(simp)?"
method_setup step = "build_tactic (step_fun)" "((disjI2)+)?,inst r (rcs union (trans r))"
method_setup close= "build_tactic (close_fun)" "((disjI1|disjI2)+)?,((exE|conjE)+)?,force_solve|solve,disji1+,blast"
method_setup close_or_step= "build_tactic (close_or_step_fun)" ""
method_setup force_finish = "build_tactic (force_finish_fun)" "force: inst r false,solve1"

typedecl "BinTree"
typedecl "Elem"
typedecl "Stream"
consts
"tree" :: "BinTree => Elem => BinTree => BinTree"
"left" :: "BinTree => BinTree"
"mirror" :: "BinTree => BinTree"
"node" :: "BinTree => Elem"
"right" :: "BinTree => BinTree"
"cons" :: "BinTree => Stream => Stream"
"hd" :: "Stream => BinTree"
"tl" :: "Stream => Stream"
"const" :: "BinTree => Stream"
"swap" :: "BinTree => BinTree => Stream"

consts
  BinRelImage :: "('a => 'b) => ('a => 'a => bool) => ('b => 'b => bool)"
  Trans_BinTree :: "('a => 'a => bool) => ('b => 'b => bool)"
  Trans_Stream :: "('a => 'a => bool) => ('b => 'b => bool)"
  union :: "('a => 'a => bool)  => ('a => 'a => bool) => ('a => 'a => bool)" (infixl 20)
defs
  BinRelImage_def [simp] : "BinRelImage f R == %x y . EX u v . R u v & x = f u & y = f v"
  Trans_BinTree_def [simp] : "Trans_BinTree R == (BinRelImage left R) union (BinRelImage right R)"
  Trans_Stream_def [simp] : "Trans_Stream R == (BinRelImage tl R)"
  union_def [simp] : "R union S == % x y . R x y | S x y"

axioms
  mirror_left [simp]: "!! bt1 :: BinTree . (left (mirror bt1)) = (mirror (right bt1))"
  mirror_node [simp]: "!! bt1 :: BinTree . (node (mirror bt1)) = (node bt1)"
  mirror_right [simp]: "!! bt1 :: BinTree . (right (mirror bt1)) = (mirror (left bt1))"
  const_hd [simp] : "!! bt :: BinTree . (hd (const bt)) = bt"
  const_tl [simp] : "!! bt :: BinTree . (tl (const bt)) = const bt"
  swap_hd [simp] : "!! bt1 :: BinTree . !! bt2 :: BinTree . (hd (swap bt1 bt2)) = bt1"
  swap_tl [simp] : "!! bt1 :: BinTree . !! bt2 :: BinTree . (tl (swap bt1 bt2)) = (swap bt2 bt1)"
  ga_cogenerated_BinTree: "!! R :: BinTree => BinTree => bool . !! u :: BinTree .  !! v :: BinTree . ! x :: BinTree . ! y :: BinTree .
                           ((R x) y) --> (((R (left x)) (left y)) & (node x) = (node y) & ((R (right x)) (right y))) ==> ((R u) v) ==> u = v"
  ga_selector_left: "!! X1 :: BinTree . !! X2 :: Elem . !! X3 :: BinTree . (left ((tree X1 X2) X3)) = X1"
  ga_selector_node: "!! X1 :: BinTree . !! X2 :: Elem . !! X3 :: BinTree . (node ((tree X1 X2) X3)) = X2"
  ga_selector_right: "!! X1 :: BinTree . !! X2 :: Elem . !! X3 :: BinTree . (right ((tree X1 X2) X3)) = X3"
  ga_cogenerated_Stream: "!! R :: Stream => Stream => bool . !! u :: Stream . !! v :: Stream . ! x :: Stream . ! y :: Stream .
                          ((R x) y) --> ((hd x) = (hd y) & ((R (tl x)) (tl y)))  ==> ((R u) v) ==> u = v"
  ga_selector_hd: "! X1 :: BinTree . ! X2 :: Stream . (hd (cons X1 X2)) = X1"
  ga_selector_tl: "! X1 :: BinTree . ! X2 :: Stream . (tl (cons X1 X2)) = X2"

(*
theorem Tree_mirror: "!! b :: BinTree . mirror(mirror b) = b"
apply(circular_coinduction)
done

declare Tree_mirror [simp]*)


theorem TreeStream_swapmirror_const: "!! b :: BinTree . (swap (mirror(mirror b)) b = const b)"
(*apply(circular_coinduction)*)

apply(coinduction)
apply(init)
apply(breakup)
apply(solve)

(* second coinduction would start here (does not work yet)*)
apply(coinduction_test)


apply(init)


apply(step)
apply(solve)

apply(rule_tac x=x in exI)
apply(rule_tac x=y in exI)

apply(solve)
apply(close)
apply(close)

apply(breakup)

apply(solve)
apply(rule disjI1)
apply(blast)

apply(force_finish)
done

end
 
