theory NatStream = Main:

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

typedecl "NatStream"
datatype Nat = zero | succ "Nat"
consts

"zero" :: "Nat"
"succ" :: "Nat => Nat"
"cons" :: "Nat => NatStream => NatStream"
"even" :: "NatStream => NatStream"
"hd" :: "NatStream => Nat"
"merge" :: "NatStream => NatStream => NatStream"
"odd" :: "NatStream => NatStream"
"tl" :: "NatStream => NatStream"
"add" :: "Nat => Nat => Nat" 
"stradd" :: "NatStream => NatStream => NatStream"
"map" :: "(Nat => Nat) => NatStream => NatStream"
"double" :: "Nat => Nat"
"const" :: "Nat => NatStream"
"swap" :: "Nat => Nat => NatStream"

consts
  BinRelImage :: "('a => 'b) => ('a => 'a => bool) => ('b => 'b => bool)"
  Trans_NatStream :: "('a => 'a => bool) => ('b => 'b => bool)"
  union :: "('a => 'a => bool)  => ('a => 'a => bool) => ('a => 'a => bool)" (infixl 20)
defs
  BinRelImage_def [simp] : "BinRelImage f R == %x y . EX u v . R u v & x = f u & y = f v"
  Trans_NatStream_def [simp] : "Trans_NatStream R == (BinRelImage tl R)"
  union_def [simp] : "R union S == % x y . R x y | S x y"

axioms
ga_generated_Nat: "True"

Nat1 [simp] : "!! n1 :: Nat . add zero n1 = n1"
Nat2 [simp]: "!! n1 :: Nat . !! n2 :: Nat . add (succ n1) n2 = (succ (add n1 n2))"
NatCom [simp]: "!! n1 :: Nat . !! n2 :: Nat . add n1 n2 = add n2 n1"
double1 [simp] : "double zero = zero"
double2 [simp] : "!! n1 :: Nat . double (succ n1) = (add (succ n1) (succ n1))"
AddDouble [simp]: "!! n1 :: Nat . (add n1 n1) = (double n1) "

const_hd [simp] : "!! n1 :: Nat . (hd (const n1)) = n1"
const_tl [simp] : "!! n1 :: Nat . (tl (const n1)) = const n1"
swap_hd [simp] : "!! n1 :: Nat . !! n2 :: Nat . (hd (swap n1 n2)) = n1"
swap_tl [simp] : "!! n1 :: Nat . !! n2 :: Nat . (tl (swap n1 n2)) = (swap n2 n1)"
odd_hd [simp]: "!! s :: NatStream . (hd (odd s)) = (hd s)"
odd_tl [simp]: "!! s :: NatStream . (tl (odd s)) = odd (tl (tl s))"
even_hd [simp]: "!! s :: NatStream . (hd (even s)) = (hd (tl s))"
even_tl [simp]: "!! s :: NatStream . (tl (even s)) = even (tl (tl s))"
merge_hd [simp]: "!! s1 :: NatStream . !! s2 :: NatStream . (hd (merge s1 s2)) = (hd s1)"
merge_tl [simp]: "!! s1 :: NatStream . !! s2 :: NatStream . (tl (merge s1 s2)) = merge s2 (tl s1)"
stradd_hd [simp]: "!! s1 :: NatStream . !! s2 :: NatStream . (hd (stradd s1 s2)) = (add (hd s1) (hd s2)) "
stradd_tl [simp]: "!! s1 :: NatStream . !! s2 :: NatStream . (tl (stradd s1 s2)) = (stradd (tl s1) (tl s2))"
map_hd [simp]: "!! f :: Nat => Nat . !! s :: NatStream . (hd (map f s)) = (f (hd s))"
map_tl [simp]: "!! f :: Nat => Nat . !! s :: NatStream . (tl (map f s)) = (map f (tl s))"

ga_cogenerated_NatStream: "!! R :: NatStream => NatStream => bool . !! u :: NatStream . !! v :: NatStream . ! x :: NatStream . ! y :: NatStream . ((R x) y) --> ((hd x) = (hd y) & ((R (tl x)) (tl y)))  ==> ((R u) v) ==> u = v"
ga_selector_hd: "!! X1 :: Nat . !! X2 :: NatStream . (hd (cons X1 X2)) = X1"
ga_selector_tl: "!! X1 :: Nat . !! X2 :: NatStream . (tl (cons X1 X2)) = X2"

theorem Stream_Const_Swap: "!! a :: Nat . !! b :: Nat . (merge (const a) (const b)) = (swap a b)"
apply(circular_coinduction)
(*
apply(coinduction)
apply(init)
(*
apply(rule_tac R="?Rs" in ga_cogenerated_NatStream)
apply(tactic "instantiate_tac [(\"Rs\" , \"% s1 s2. Rcs union (Trans ?R)\" )]")
defer
apply(solve)
apply(blast)
apply(init2)
*)
apply(breakup)

apply(close_or_step)

apply(finish)

(*apply(rule disjI1)
apply(blast)
apply(close)

(*
apply(solve1)
apply(step)
apply(solve1)
apply(xy_exI)
apply(solve1)
apply(rule disjI1)
apply(blast)
apply(simp)
*)

apply(breakup)

apply(solve)
apply(rule disjI1)
apply(blast)

apply(finish)
*)*)
done

theorem NatStream_Map_Double: "!! l :: NatStream . (stradd l l) = (map double l)"
apply(circular_coinduction)
(*
apply(coinduction4)
apply(init)

(*
apply(rule_tac R="?Rs" in ga_cogenerated_NatStream)
apply(tactic "instantiate_tac [(\"Rs\" , \"% s. Rd union (Trans ?R)\" )]")
defer
apply(solve)
apply(rule disjI1)
apply(blast)
apply(init2)
*)

apply(breakup)

apply(solve)
apply(simp add: AddDouble)
apply(close_or_step4)

apply(finish)
*)
done

theorem Stream_StrAdd: "!! s1 :: NatStream . !! s2 :: NatStream . (stradd s1 s2) = (stradd s2 s1)"
apply(circular_coinduction)
(*
apply(coinduction2)
apply(init)

(*
apply(rule_tac R="?Rs" in ga_cogenerated_NatStream)
apply(tactic "instantiate_tac [(\"Rs\" , \"% s t. Rsa union (Trans ?R)\" )]")
defer
apply(solve)
apply(rule disjI1)
apply(blast)
apply(init2)
*)

apply(breakup)

apply(solve)
apply(simp add: NatCom)
apply(close_or_step2)

(*
apply(rule disjI1)
apply(rule_tac x="tl s1" in exI)
apply(rule_tac x="tl s2" in exI)
apply(close)
*)

apply(finish)
*)
done

theorem NatStream_Merge: "!! s :: NatStream . merge (odd s) (even s) = s"
apply(circular_coinduction)
(*
apply(coinduction3)
apply(init)
(*
apply(rule_tac R="?Rzero" in ga_cogenerated_NatStream)
apply(tactic "instantiate_tac [(\"Rzero\" , \"% s.  Rm union (Trans ?R)\" )]")
defer
apply(init)
*)

apply(breakup)

apply(close_or_step3)

(*
apply(solve1)
apply(step3)
apply(solve1)
apply(xy_exI)
apply(solve1)
apply(simp)
*)

apply(breakup)

apply(close_or_step3)

apply(finish)
*)
done

end

