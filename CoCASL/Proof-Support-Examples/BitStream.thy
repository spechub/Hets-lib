theory BitStream = Main:

use tactics

method_setup circular_coinduction = "build_tactic (circular_coinduction_fun)" "all"
method_setup coinduction = "build_tactic (coinduction_fun)" "rule_tac R=?Rzero in ga_cogenerated, instantiate_tac Rzero %s1.?R,step"
method_setup init = "build_tactic (init_fun)" "(simp|(solve,blast))?,init2_fun?"
method_setup breakup = "build_tactic (breakup_fun)" "simp,((exE|conjE)+)?,disjE"
method_setup solve= "build_tactic (solve_fun 1)" "((exE|conjE|conjI)+)?,(simp)?,((exE|conjE|conjI)+)?,(simp)?"
method_setup step = "build_tactic (step_fun)" "((disjI2)+)?,inst r (rcs union (trans r))"
method_setup close= "build_tactic (close_fun)" "((disjI1|disjI2)+)?,((exE|conjE)+)?,force_solve|solve,disji1+,blast"
method_setup close_or_step= "build_tactic (close_or_step_fun)" "close|(solve,(close|(step,solve?,disjI2?,solve?,xy_exi?,solve,close?),((disjI1+)?,blast,close)?))"
method_setup force_finish = "build_tactic (force_finish_fun)" "inst r false,solve1"

typedecl "BitStream"
datatype Bit = X0 | X1
consts
"flip" :: "BitStream => BitStream"
"flop" :: "Bit => Bit"
"tick" :: "BitStream"
"tock" :: "BitStream"
"hd" :: "BitStream => Bit"
"tl" :: "BitStream => BitStream"
"map" :: "(Bit => Bit) => BitStream => BitStream"

consts
  BinRelImage :: "('a => 'b) => ('a => 'a => bool) => ('b => 'b => bool)"
  Trans_BitStream :: "('a => 'a => bool) => ('b => 'b => bool)"
  union :: "('a => 'a => bool)  => ('a => 'a => bool) => ('a => 'a => bool)" (infixl 20)
defs
  BinRelImage_def [simp] : "BinRelImage f R == %x y . EX u v . R u v & x = f u & y = f v"
  Trans_BitStream_def [simp] : "Trans_BitStream R == (BinRelImage tl R)"
  union_def [simp] : "R union S == % x y . R x y | S x y"

axioms

map_hd [simp]: "!! f :: Bit => Bit . !! s :: BitStream . (hd (map f s)) = (f (hd s))"
map_tl [simp]: "!! f :: Bit => Bit . !! s :: BitStream . (tl (map f s)) = (map f (tl s))"

ga_generated_Bit: "True"
ga_disjoint_0_1: "(Not (X0 = X1))"
flip_hd_a [simp]: "!! b :: BitStream . (hd b) = X1 ==> (hd (flip b)) = X0"
flip_hd_b [simp]: "!! b :: BitStream . (hd b) = X0 ==> (hd (flip b)) = X1"
flip_tl [simp]: "!! b :: BitStream . (tl (flip b)) = (flip (tl b))"
flop_1 [simp]: "!! b :: Bit . (b = X0) ==> (flop b) = X1"
flop_2 [simp]: "!! b :: Bit . (b = X1) ==> (flop b) = X0"
tick_hd [simp]: "hd tick = X1"
tick_tl [simp]: "tl tick = tock"
tock_hd [simp]: "hd tock = X0"
tock_tl [simp]: "tl tock = tick"

ga_cogenerated_BitStream: "!! R :: BitStream => BitStream => bool . !! u :: BitStream . !! v :: BitStream . ! x :: BitStream . ! y :: BitStream . ((R x) y) --> ((hd x) = (hd y) & ((R (tl x)) (tl y)))  ==> ((R u) v) ==> u = v"

theorem ticktock: "tick = map flop tock"
apply(circular_coinduction)
done

theorem ticktock: "!! b :: BitStream . map flop (map flop b) = b"
apply(coinduction)
apply(init)
apply(breakup)
apply(solve)
apply(case_tac "hd y")
apply(close)
apply(close)
apply(close)
apply(force_finish)

done

theorem flipflip: "!! b :: BitStream . (flip (flip b)) = b"

apply(coinduction)
apply(init)

apply(breakup)

apply(solve)
apply(case_tac "hd y")
apply(close)
apply(close)
apply(close)

apply(force_finish)

done
