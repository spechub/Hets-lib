theory RCCVerification_RCC_FO_in_MetricSpace_T
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"Field_unary_minus_idef\", \"refl\", \"trans\", \"antisym\",
     \"dichotomy_TotalOrder\", \"FWO_plus_left\", \"FWO_times_left\",
     \"FWO_plus_right\", \"FWO_times_right\", \"FWO_plus\",
     \"geq_def_ExtPartialOrder\", \"less_def_ExtPartialOrder\",
     \"greater_def_ExtPartialOrder\", \"ga_comm_inf\", \"ga_comm_sup\",
     \"inf_def_ExtPartialOrder\", \"sup_def_ExtPartialOrder\",
     \"ga_comm_min\", \"ga_comm_max\", \"ga_assoc_min\",
     \"ga_assoc_max\", \"ga_left_comm_min\", \"ga_left_comm_max\",
     \"min_def_ExtTotalOrder\", \"max_def_ExtTotalOrder\",
     \"min_inf_relation\", \"max_sup_relation\", \"Real_ub_def\",
     \"Real_lb_def\", \"Real_inf_def\", \"Real_sup_def\",
     \"Real_isBounded_def\", \"completeness\", \"Real_inj_0\",
     \"Real_inj_suc\", \"Real_archimedian\", \"Real_abs_def\",
     \"Real_sqr_def\", \"Real_sqrt_dom\", \"Real_sqrt_idef\",
     \"Real_2_def\", \"Real_minus_def\", \"Real_divide_dom\",
     \"Real_divide_idef\", \"Real_half_idef\", \"one_greater_zero\",
     \"zero_leq_one\", \"half_gt_zero\", \"half_plus_minus\",
     \"add_monotone\", \"sub_leq\", \"half_leq\", \"half_leq_zero\",
     \"comm_add\", \"Real_half_plus\", \"Real_half_minus\",
     \"Real_minus_half\", \"Real_half_monot\", \"MS_pos_definite\",
     \"MS_symm\", \"MS_triangle\", \"MS_pos\", \"MS_zero\",
     \"EMSCB_rep_pos\", \"EMSCB_rep_0\", \"EMSCB_rep_inj\", \"Ax4\",
     \"EMSCB_center\", \"EMSCB_closed\", \"Ax1\", \"C_def\",
     \"C_non_null\", \"C_sym\", \"C_id\", \"C_non_triv\"]"

typedecl ClosedBall
typedecl Real
typedecl S

datatype X_Nat = X0X1 ("0''") | X_suc "X_Nat" ("suc/'(_')" [3] 999)

consts
X0X2 :: "Real" ("0''''")
X1 :: "Real" ("1''")
X2 :: "Real" ("2''")
XMinus__X :: "Real => Real" ("(-''/ _)" [56] 56)
XVBar__XVBar :: "Real => Real" ("(|/ _/ |)" [10] 999)
X__C__X :: "ClosedBall => ClosedBall => bool" ("(_/ C/ _)" [44,44] 42)
X__XGtXEq__X :: "Real => Real => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XGt__X :: "Real => Real => bool" ("(_/ >''/ _)" [44,44] 42)
X__XLtXEq__XX1 :: "Real => Real => bool" ("(_/ <=''/ _)" [44,44] 42)
X__XLtXEq__XX2 :: "Real => (Real => bool) => bool" ("(_/ <=''''/ _)" [44,44] 42)
X__XLtXEq__XX3 :: "(Real => bool) => Real => bool" ("(_/ <='_3/ _)" [44,44] 42)
X__XLt__X :: "Real => Real => bool" ("(_/ <''/ _)" [44,44] 42)
X__XMinus__X :: "Real => Real => Real" ("(_/ -''/ _)" [54,54] 52)
X__XPlus__X :: "Real => Real => Real" ("(_/ +''/ _)" [54,54] 52)
X__XSlash__X :: "Real => Real => Real partial" ("(_/ '/''/ _)" [54,54] 52)
X__Xx__X :: "Real => Real => Real" ("(_/ *''/ _)" [54,54] 52)
X_closedBall :: "S => Real => ClosedBall" ("closedBall/'(_,/ _')" [3,3] 999)
X_d :: "S => S => Real" ("d/'(_,/ _')" [3,3] 999)
X_half :: "Real => Real" ("half/'(_')" [3] 999)
X_inj :: "X_Nat => Real" ("inj''/'(_')" [3] 999)
X_isBounded :: "(Real => bool) => bool" ("isBounded/'(_')" [3] 999)
X_max :: "Real => Real => Real" ("max''/'(_,/ _')" [3,3] 999)
X_min :: "Real => Real => Real" ("min''/'(_,/ _')" [3,3] 999)
X_nonempty :: "ClosedBall => bool" ("nonempty/'(_')" [3] 999)
infX1 :: "Real => Real => Real partial" ("inf''/'(_,/ _')" [3,3] 999)
infX2 :: "(Real => bool) => Real partial" ("inf''''/'(_')" [3] 999)
rep :: "ClosedBall => S => bool"
sqr__X :: "Real => Real" ("(sqr/ _)" [56] 56)
sqrt__X :: "Real => Real partial" ("(sqrt/ _)" [56] 56)
supX1 :: "Real => Real => Real partial" ("sup''/'(_,/ _')" [3,3] 999)
supX2 :: "(Real => bool) => Real partial" ("sup''''/'(_')" [3] 999)

axioms
Field_unary_minus_idef [rule_format] :
"ALL (x :: Real). -' (x :: Real) +' (x :: Real) = 0''"

refl [rule_format] : "ALL (x :: Real). (x :: Real) <=' (x :: Real)"

trans [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real).
 (x :: Real) <=' (y :: Real) & (y :: Real) <=' (z :: Real) -->
 (x :: Real) <=' (z :: Real)"

antisym [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 (x :: Real) <=' (y :: Real) & (y :: Real) <=' (x :: Real) -->
 (x :: Real) = (y :: Real)"

dichotomy_TotalOrder [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 (x :: Real) <=' (y :: Real) | (y :: Real) <=' (x :: Real)"

FWO_plus_left [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real).
 (a :: Real) <=' (b :: Real) -->
 (a :: Real) +' (c :: Real) <=' (b :: Real) +' (c :: Real)"

FWO_times_left [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real).
 (a :: Real) <=' (b :: Real) & 0'' <=' (c :: Real) -->
 (a :: Real) *' (c :: Real) <=' (b :: Real) *' (c :: Real)"

FWO_plus_right [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real).
 (b :: Real) <=' (c :: Real) -->
 (a :: Real) +' (b :: Real) <=' (a :: Real) +' (c :: Real)"

FWO_times_right [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real).
 (b :: Real) <=' (c :: Real) & 0'' <=' (a :: Real) -->
 (a :: Real) *' (b :: Real) <=' (a :: Real) *' (c :: Real)"

FWO_plus [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real).
 ALL (X_d :: Real).
 (a :: Real) <=' (c :: Real) & (b :: Real) <=' (X_d :: Real) -->
 (a :: Real) +' (b :: Real) <=' (c :: Real) +' (X_d :: Real)"

geq_def_ExtPartialOrder [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ((x :: Real) >=' (y :: Real)) = ((y :: Real) <=' (x :: Real))"

less_def_ExtPartialOrder [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ((x :: Real) <' (y :: Real)) =
 ((x :: Real) <=' (y :: Real) & ~ (x :: Real) = (y :: Real))"

greater_def_ExtPartialOrder [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ((x :: Real) >' (y :: Real)) = ((y :: Real) <' (x :: Real))"

ga_comm_inf [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 inf'((x :: Real), (y :: Real)) = inf'((y :: Real), (x :: Real))"

ga_comm_sup [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 sup'((x :: Real), (y :: Real)) = sup'((y :: Real), (x :: Real))"

inf_def_ExtPartialOrder [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real).
 inf'((x :: Real), (y :: Real)) = makePartial (z :: Real) =
 ((z :: Real) <=' (x :: Real) &
  (z :: Real) <=' (y :: Real) &
  (ALL (t :: Real).
   (t :: Real) <=' (x :: Real) & (t :: Real) <=' (y :: Real) -->
   (t :: Real) <=' (z :: Real)))"

sup_def_ExtPartialOrder [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real).
 sup'((x :: Real), (y :: Real)) = makePartial (z :: Real) =
 ((x :: Real) <=' (z :: Real) &
  (y :: Real) <=' (z :: Real) &
  (ALL (t :: Real).
   (x :: Real) <=' (t :: Real) & (y :: Real) <=' (t :: Real) -->
   (z :: Real) <=' (t :: Real)))"

ga_comm_min [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 min'((x :: Real), (y :: Real)) = min'((y :: Real), (x :: Real))"

ga_comm_max [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 max'((x :: Real), (y :: Real)) = max'((y :: Real), (x :: Real))"

ga_assoc_min [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real).
 min'(min'((x :: Real), (y :: Real)), (z :: Real)) =
 min'((x :: Real), min'((y :: Real), (z :: Real)))"

ga_assoc_max [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real).
 max'(max'((x :: Real), (y :: Real)), (z :: Real)) =
 max'((x :: Real), max'((y :: Real), (z :: Real)))"

ga_left_comm_min [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real).
 min'((x :: Real), min'((y :: Real), (z :: Real))) =
 min'((y :: Real), min'((x :: Real), (z :: Real)))"

ga_left_comm_max [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real).
 max'((x :: Real), max'((y :: Real), (z :: Real))) =
 max'((y :: Real), max'((x :: Real), (z :: Real)))"

min_def_ExtTotalOrder [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 min'((x :: Real), (y :: Real)) =
 (if (x :: Real) <=' (y :: Real) then (x :: Real) else (y :: Real))"

max_def_ExtTotalOrder [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 max'((x :: Real), (y :: Real)) =
 (if (x :: Real) <=' (y :: Real) then (y :: Real) else (x :: Real))"

min_inf_relation [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 makePartial (min'((x :: Real), (y :: Real))) =
 inf'((x :: Real), (y :: Real))"

max_sup_relation [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 makePartial (max'((x :: Real), (y :: Real))) =
 sup'((x :: Real), (y :: Real))"

Real_ub_def [rule_format] :
"ALL (M :: Real => bool).
 ALL (r :: Real).
 ((M :: Real => bool) <=_3 (r :: Real)) =
 (ALL (s :: Real).
  (M :: Real => bool) (s :: Real) --> (s :: Real) <=' (r :: Real))"

Real_lb_def [rule_format] :
"ALL (M :: Real => bool).
 ALL (r :: Real).
 ((r :: Real) <='' (M :: Real => bool)) =
 (ALL (s :: Real).
  (M :: Real => bool) (s :: Real) --> (r :: Real) <=' (s :: Real))"

Real_inf_def [rule_format] :
"ALL (M :: Real => bool).
 ALL (r :: Real).
 inf''((M :: Real => bool)) = makePartial (r :: Real) =
 ((r :: Real) <='' (M :: Real => bool) &
  (ALL (s :: Real).
   (s :: Real) <='' (M :: Real => bool) -->
   (s :: Real) <=' (r :: Real)))"

Real_sup_def [rule_format] :
"ALL (M :: Real => bool).
 ALL (r :: Real).
 sup''((M :: Real => bool)) = makePartial (r :: Real) =
 ((M :: Real => bool) <=_3 (r :: Real) &
  (ALL (s :: Real).
   (M :: Real => bool) <=_3 (s :: Real) -->
   (r :: Real) <=' (s :: Real)))"

Real_isBounded_def [rule_format] :
"ALL (M :: Real => bool).
 isBounded((M :: Real => bool)) =
 (EX (ub :: Real).
  EX (lb :: Real).
  (lb :: Real) <='' (M :: Real => bool) &
  (M :: Real => bool) <=_3 (ub :: Real))"

completeness [rule_format] :
"ALL (M :: Real => bool).
 isBounded((M :: Real => bool)) -->
 defOp (inf''((M :: Real => bool))) &
 defOp (sup''((M :: Real => bool)))"

Real_inj_0 [rule_format] : "inj'(0') = 0''"

Real_inj_suc [rule_format] :
"ALL (X_n :: X_Nat).
 inj'(suc((X_n :: X_Nat))) = 1' +' inj'((X_n :: X_Nat))"

Real_archimedian [rule_format] :
"ALL (r :: Real).
 EX (X_n :: X_Nat). (r :: Real) <=' inj'((X_n :: X_Nat))"

Real_abs_def [rule_format] :
"ALL (r :: Real).
 | (r :: Real) | = max'((r :: Real), -' (r :: Real))"

Real_sqr_def [rule_format] :
"ALL (r :: Real). sqr (r :: Real) = (r :: Real) *' (r :: Real)"

Real_sqrt_dom [rule_format] :
"ALL (r :: Real). defOp (sqrt (r :: Real)) = ((r :: Real) >=' 0'')"

Real_sqrt_idef [rule_format] :
"ALL (r :: Real).
 sqrt sqr (r :: Real) = makePartial ( | (r :: Real) | )"

Real_2_def [rule_format] : "2' = 1' +' 1'"

Real_minus_def [rule_format] :
"ALL (r :: Real).
 ALL (r' :: Real).
 (r :: Real) -' (r' :: Real) = (r :: Real) +' -' (r' :: Real)"

Real_divide_dom [rule_format] :
"ALL (r :: Real). ~ defOp ((r :: Real) /' 0'')"

Real_divide_idef [rule_format] :
"ALL (r :: Real).
 ALL (r' :: Real).
 ALL (r'' :: Real).
 (~ (r' :: Real) = 0'' -->
  (r :: Real) /' (r' :: Real) = makePartial (r'' :: Real)) =
 ((r'' :: Real) *' (r' :: Real) = (r :: Real))"

Real_half_idef [rule_format] :
"ALL (r :: Real). 2' *' half((r :: Real)) = (r :: Real)"

one_greater_zero [rule_format] : "1' >' 0''"

zero_leq_one [rule_format] : "0'' <=' 1'"

half_gt_zero [rule_format] :
"ALL (r :: Real). (r :: Real) >' 0'' --> half((r :: Real)) >' 0''"

half_plus_minus [rule_format] :
"ALL (r :: Real).
 ALL (s :: Real).
 (r :: Real) <=' (s :: Real) -->
 (s :: Real) +' half((r :: Real) -' (s :: Real)) <=' (s :: Real)"

add_monotone [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real).
 ALL (e :: Real).
 (a :: Real) <=' (b :: Real) & (c :: Real) <=' (e :: Real) -->
 (a :: Real) +' (c :: Real) <=' (b :: Real) +' (e :: Real)"

sub_leq [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ~ (a :: Real) <=' (b :: Real) -->
 (a :: Real) -' (b :: Real) >' 0''"

half_leq [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 (a :: Real) <=' half((a :: Real) -' (b :: Real)) +' (b :: Real) -->
 (a :: Real) <=' (b :: Real)"

half_leq_zero [rule_format] :
"ALL (r :: Real).
 0'' <=' (r :: Real) --> 0'' <=' half((r :: Real))"

comm_add [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 (a :: Real) +' (b :: Real) = (b :: Real) +' (a :: Real)"

Real_half_plus [rule_format] :
"ALL (r :: Real).
 ALL (s :: Real).
 half((r :: Real) +' (s :: Real)) =
 half((r :: Real)) +' half((s :: Real))"

Real_half_minus [rule_format] :
"ALL (r :: Real).
 ALL (s :: Real).
 half((r :: Real) -' (s :: Real)) =
 half((r :: Real)) -' half((s :: Real))"

Real_minus_half [rule_format] :
"ALL (r :: Real).
 (r :: Real) -' half((r :: Real)) = half((r :: Real))"

Real_half_monot [rule_format] :
"ALL (r :: Real).
 ALL (s :: Real).
 (half((r :: Real)) <=' half((s :: Real))) =
 ((r :: Real) <=' (s :: Real))"

MS_pos_definite [rule_format] :
"ALL (x :: S).
 ALL (y :: S). d((x :: S), (y :: S)) = 0'' = ((x :: S) = (y :: S))"

MS_symm [rule_format] :
"ALL (x :: S).
 ALL (y :: S). d((x :: S), (y :: S)) = d((y :: S), (x :: S))"

MS_triangle [rule_format] :
"ALL (x :: S).
 ALL (y :: S).
 ALL (z :: S).
 d((x :: S), (z :: S)) <='
 d((x :: S), (y :: S)) +' d((y :: S), (z :: S))"

MS_pos [rule_format] :
"ALL (x :: S). ALL (y :: S). 0'' <=' d((x :: S), (y :: S))"

MS_zero [rule_format] : "ALL (x :: S). d((x :: S), (x :: S)) = 0''"

EMSCB_rep_pos [rule_format] :
"ALL (r :: Real).
 ALL (x :: S).
 ALL (y :: S).
 (r :: Real) >' 0'' -->
 rep (closedBall((x :: S), (r :: Real))) (y :: S) =
 (d((x :: S), (y :: S)) <=' (r :: Real))"

EMSCB_rep_0 [rule_format] :
"ALL (r :: Real).
 ALL (x :: S).
 ALL (y :: S).
 ~ (r :: Real) >' 0'' -->
 ~ rep (closedBall((x :: S), (r :: Real))) (y :: S)"

EMSCB_rep_inj [rule_format] :
"ALL (a :: ClosedBall).
 ALL (b :: ClosedBall).
 rep (a :: ClosedBall) = rep (b :: ClosedBall) -->
 (a :: ClosedBall) = (b :: ClosedBall)"

Ax4 [rule_format] :
"ALL (a :: ClosedBall).
 EX (z :: S).
 EX (t :: Real).
 (a :: ClosedBall) = closedBall((z :: S), (t :: Real))"

EMSCB_center [rule_format] :
"ALL (r :: Real).
 ALL (x :: S).
 (r :: Real) >' 0'' -->
 rep (closedBall((x :: S), (r :: Real))) (x :: S)"

EMSCB_closed [rule_format] :
"ALL (a :: ClosedBall).
 ALL (x :: S).
 ~ rep (a :: ClosedBall) (x :: S) -->
 (EX (r :: Real).
  ALL (y :: S).
  ~
  (rep (closedBall((x :: S), (r :: Real))) (y :: S) &
   ~ rep (a :: ClosedBall) (y :: S)))"

Ax1 [rule_format] :
"ALL (x :: ClosedBall).
 nonempty((x :: ClosedBall)) =
 ((x :: ClosedBall) C (x :: ClosedBall))"

C_def [rule_format] :
"ALL (x :: ClosedBall).
 ALL (y :: ClosedBall).
 ((x :: ClosedBall) C (y :: ClosedBall)) =
 (EX (s :: S).
  rep (x :: ClosedBall) (s :: S) & rep (y :: ClosedBall) (s :: S))"

declare Field_unary_minus_idef [simp]
declare refl [simp]
declare FWO_plus_left [simp]
declare FWO_plus_right [simp]
declare ga_comm_inf [simp]
declare ga_comm_sup [simp]
declare ga_comm_min [simp]
declare ga_comm_max [simp]
declare ga_assoc_min [simp]
declare ga_assoc_max [simp]
declare ga_left_comm_min [simp]
declare ga_left_comm_max [simp]
declare min_inf_relation [simp]
declare max_sup_relation [simp]
declare completeness [simp]
declare Real_inj_0 [simp]
declare Real_divide_dom [simp]
declare Real_half_idef [simp]
declare one_greater_zero [simp]
declare zero_leq_one [simp]
declare half_plus_minus [simp]
declare sub_leq [simp]
declare half_leq_zero [simp]
declare Real_minus_half [simp]
declare Real_half_monot [simp]
declare MS_triangle [simp]
declare MS_pos [simp]
declare MS_pos_definite [simp]
declare MS_zero [simp]
declare EMSCB_rep_pos [simp]
declare EMSCB_rep_0 [simp]
declare EMSCB_center [simp]

theorem C_non_null :
"ALL (x :: ClosedBall).
 ALL (y :: ClosedBall).
 (x :: ClosedBall) C (y :: ClosedBall) -->
 (x :: ClosedBall) C (x :: ClosedBall)"
using C_def by auto

ML "Header.record \"C_non_null\""

theorem C_sym :
"ALL (x :: ClosedBall).
 ALL (y :: ClosedBall).
 (x :: ClosedBall) C (y :: ClosedBall) -->
 (y :: ClosedBall) C (x :: ClosedBall)"
using C_def by auto

ML "Header.record \"C_sym\""

lemma swap : "A --> B=D ==> B ==> A-->D"
by auto

lemma impLemma : "[| A; A==>B; B-->D|] ==> D"
by auto

lemma reflLemma : "x=y ==> x <=' y"
using refl by auto

lemma MS_triangle_rev :
"d(x, z) <=' (d(x, y) +' d(z, y))"
by (simp add: MS_symm)

lemma C_id_lemma : "!!x y xa.
       ALL z. (EX s. rep z s & rep x s) = (EX s. rep z s & rep y s)
       ==> rep x xa ==> rep y xa"
apply (erule contrapos_pp)
apply (subst not_all)
thm Ax4 [THEN allI, of "%x. x"]
apply (insert Ax4 [THEN allI, of "%x. x"])
apply (frule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (erule exE)
apply (erule exE)
apply (erule exE)
apply (erule exE)
apply (subst not_iff)
apply (case_tac "ta >' 0''")
apply (rule_tac x="closedBall(xa, half (d(za, xa) -' ta))" in exI)
apply(auto)
apply((drule EMSCB_rep_pos [COMP impI, THEN swap]))+
apply(rule_tac P="d(za, xa) <=' ta" in notE)
apply(assumption)
apply(rule half_leq)
apply(rule trans)
apply(rule conjI)
defer
apply(rule add_monotone)
apply(rule conjI)
apply(erule mp)
back
apply(insert sub_leq)
apply(rule half_gt_zero)
apply(rule sub_leq)
apply(assumption+)

apply(rule_tac x="xa" in exI)
apply simp
apply(rule EMSCB_rep_pos [THEN iffD2])
apply(rule half_gt_zero)
apply(rule sub_leq)
apply(assumption)
apply simp
apply(rule half_leq_zero)
apply(drule sub_leq)
apply(simp add: greater_def_ExtPartialOrder
                less_def_ExtPartialOrder)
apply(rule trans)
apply(rule conjI)
defer
apply(rule MS_triangle_rev)
apply(rule reflLemma)
apply(rule MS_symm)
done

theorem C_id :
"ALL (x :: ClosedBall).
 ALL (y :: ClosedBall).
 (ALL (z :: ClosedBall).
  ((z :: ClosedBall) C (x :: ClosedBall)) =
  ((z :: ClosedBall) C (y :: ClosedBall))) -->
 (x :: ClosedBall) = (y :: ClosedBall)"
apply (auto simp add: C_def)
apply (rule EMSCB_rep_inj)
apply (rule ext)
apply (auto)
apply (rule_tac x="x" in C_id_lemma)
apply(auto)
apply (rule_tac x="y" in C_id_lemma)
apply(auto)
done

ML "Header.record \"C_id\""

theorem C_non_triv :
"EX (x :: ClosedBall). (x :: ClosedBall) C (x :: ClosedBall)"
apply (simp add: C_def)
apply (rule exI)
apply (rule exI)
apply (rule EMSCB_rep_pos [THEN iffD2])
apply(rule one_greater_zero)
apply(rule iffD2)
apply(rule arg_cong)
back
back
defer
apply(rule zero_leq_one)
apply auto
done

ML "Header.record \"C_non_triv\""

end
