theory VendingMachine = Main:

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

typedecl "VendingMachine"
datatype Nat = zero | succ "Nat"
consts

"initial" :: "VendingMachine"
"quarter" :: "VendingMachine => VendingMachine"
"dollar" :: "VendingMachine => VendingMachine"
"tea" :: "VendingMachine => VendingMachine"
"coffee" :: "VendingMachine => VendingMachine"
"get_current" :: "VendingMachine => Nat"
"zero" :: "Nat"
"succ" :: "Nat => Nat"
"add" :: "Nat => Nat => Nat"


consts
  BinRelImage :: "('a => 'b) => ('a => 'a => bool) => ('b => 'b => bool)"
  Trans_VendingMachine :: "('a => 'a => bool) => ('b => 'b => bool)"
  union :: "('a => 'a => bool)  => ('a => 'a => bool) => ('a => 'a => bool)" (infixl 20)
defs
  BinRelImage_def [simp] : "BinRelImage f R == %x y . EX u v . R u v & x = f u & y = f v"
  Trans_VendingMachine_def [simp] : "Trans_VendingMachine R == (BinRelImage quarter R) union
                                                               (BinRelImage dollar R) union
                                                               (BinRelImage tea R) union 
                                                               (BinRelImage coffee R)"
  union_def [simp] : "R union S == % x y . R x y | S x y"

axioms
ga_generated_Nat: "True"

initial_def [simp] : "get_current initial = zero" 
quarter_gc [simp] : "!! v :: VendingMachine . get_current (quarter v) = succ (get_current v)"
dollar_gc [simp] : "!! v :: VendingMachine . get_current (dollar v) = succ (succ (succ (succ (get_current v))))"
tea_gc [simp] : "!! n :: Nat . !! v :: VendingMachine . get_current v = succ (succ (succ (succ n))) ==> get_current (tea v) = n"
tea_q1 [simp] : "!! v :: VendingMachine . tea (quarter (quarter (quarter (quarter v)))) = v"
tea_q2 [simp] : "!! v :: VendingMachine . tea (dollar v) = v"
coffee_gc [simp] : "!! n :: Nat . !! v :: VendingMachine . get_current v = succ (succ (succ (succ (succ (succ n))))) ==> get_current (coffee v) = n"
coffee_q1 [simp] : "!! v :: VendingMachine . coffee (quarter (quarter (quarter (quarter (quarter (quarter v)))))) = v"
coffee_q2 [simp] : "!! v :: VendingMachine . coffee (quarter (quarter (dollar v))) = v"
coffee_q3 [simp] : "!! v :: VendingMachine . coffee (dollar (dollar v)) = quarter (quarter v)"

Nat1 [simp] : "!! n1 :: Nat . add zero n1 = n1"
Nat2 [simp]: "!! n1 :: Nat . !! n2 :: Nat . add (succ n1) n2 = (succ (add n1 n2))"
NatCom [simp]: "!! n1 :: Nat . !! n2 :: Nat . add n1 n2 = add n2 n1"
double1 [simp] : "double zero = zero"
double2 [simp] : "!! n1 :: Nat . double (succ n1) = (add (succ n1) (succ n1))"
AddDouble [simp]: "!! n1 :: Nat . (add n1 n1) = (double n1) "

ga_cogenerated_VendingMachine: "!! R :: VendingMachine => VendingMachine => bool . !! u :: VendingMachine . !! v :: VendingMachine . ! x :: VendingMachine . ! y :: VendingMachine . ((R x) y) --> ((get_current x) = (get_current y) & ((R (quarter x)) (quarter y)) & ((R (dollar x)) (dollar y)) & ((R (tea x)) (tea y)) & ((R (coffee x)) (coffee y)))  ==> ((R u) v) ==> u = v"



theorem qqqqd: "!! v :: VendingMachine .  quarter (quarter (quarter (quarter v))) = dollar v"
apply(coinduction)
apply(init)
apply(breakup)

apply(rule conjI)
apply(erule exE)
apply(simp only: quarter_gc)
apply(simp only: dollar_gc)

apply(rule conjI)
apply(rule disjI1)
apply(erule exE)
apply(rule_tac x="quarter v" in exI)
apply(simp)

apply(rule conjI)
apply(rule disjI1)
apply(erule exE)
apply(rule_tac x="dollar v" in exI)
apply(simp)

apply(rule conjI)
apply(rule disjI1)
apply(erule exE)
apply(rule_tac x="tea v" in exI)
apply(simp)
apply(rule conjI)


