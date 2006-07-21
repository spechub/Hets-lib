theory RCCDagstuhl2_NN_T
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize 
    [\"C_non_null\", \"C_sym\", \"C_id\", \"C_non_triv\", 
     \"def_nonempty\", \"C_def\", \"MS_pos\", \"MS_zero\", 
     \"MS_pos_definite\", \"MS_symm\", \"MS_triangle\", 
     \"one_greater_zero\", \"zero_leq_one\", \"half_gt_zero\", 
     \"half_plus_minus\", \"add_monotone\", \"sub_leq\", \"half_leq\", 
     \"half_leq_zero\", \"comm_add\", \"Real_half_plus\", 
     \"Real_half_minus\", \"Real_minus_half\", \"Real_half_monot\", 
     \"Real_abs_def\", \"Real_sqr_def\", \"Real_sqrt_dom\", 
     \"Real_sqrt_idef\", \"Real_2_def\", \"Real_minus_def\", 
     \"Real_divide_dom\", \"Real_divide_idef\", \"Real_half_idef\", 
     \"ga_Nat\", \"Real_ub_def\", \"Real_lb_def\", \"Real_inf_def\", 
     \"Real_sup_def\", \"Real_isBounded_defCBrX\", \"Real_inj_0\", 
     \"Real_inj_suc\", \"Real_archimedian\", \"FWO_plus_right\", 
     \"FWO_times_right\", \"FWO_plus\", \"FWO_plus_left\", 
     \"FWO_times_left\", \"Field_unary_minus_idef\", 
     \"dichotomy_TotalOrder\", \"antisym\", \"trans\", \"refl\", 
     \"min_inf_relation\", \"max_sup_relation\", \"ga_comm_min\", 
     \"ga_comm_max\", \"ga_assoc_min\", \"ga_assoc_max\", 
     \"min_def_ExtTotalOrder\", \"max_def_ExtTotalOrder\", 
     \"ga_comm_inf\", \"ga_comm_sup\", \"inf_def_ExtPartialOrder\", 
     \"sup_def_ExtPartialOrder\", \"geq_def_ExtPartialOrder\", 
     \"less_def_ExtPartialOrder\", \"greater_def_ExtPartialOrder\", 
     \"EMSCB_center\", \"EMSCB_closed\", \"EMSCB_rep_pos\", 
     \"EMSCB_rep_0\", \"EMSCB_rep_inj\", \"Ax4\", \"ga_Nat_1\"]"

typedecl ClosedBall
typedecl Real
typedecl S

datatype Nat = X0_1 | suc "Nat"

consts
MinusXXX :: "Real => Real"
VBarX__VBarX :: "Real => Real"
X0_2 :: "Real"
X1 :: "Real"
X2 :: "Real"
XXCXX :: "ClosedBall * ClosedBall => bool"
XXGtXEqXXX :: "Real * Real => bool"
XXGtXXX :: "Real * Real => bool"
XXLtXEqXXX_1 :: "(Real => bool) * Real => bool"
XXLtXEqXXX_2 :: "Real * (Real => bool) => bool"
XXLtXEqXXX_3 :: "Real * Real => bool"
XXLtXXX :: "Real * Real => bool"
XXMinusXXX :: "Real * Real => Real"
XXPlusXXX :: "Real * Real => Real"
XXSlashXXX :: "Real * Real => Real option"
XXxXXX :: "Real * Real => Real"
closedBall :: "S * Real => ClosedBall"
d :: "S * S => Real"
half :: "Real => Real"
inf_1 :: "(Real => bool) => Real option"
inf_2 :: "Real * Real => Real option"
injX :: "Nat => Real"
isBounded :: "(Real => bool) => bool"
maxX :: "Real * Real => Real"
minX :: "Real * Real => Real"
nonempty :: "ClosedBall => bool"
rep :: "ClosedBall => S => bool"
sqrXX :: "Real => Real"
sqrtXX :: "Real => Real option"
sup_1 :: "(Real => bool) => Real option"
sup_2 :: "Real * Real => Real option"

lemma case_Nat_SomeProm [simp]:" (case caseVar of X0_1 => Some (x)
   | suc nat => Some (s nat)
) =
Some (case caseVar of X0_1 => x
   | suc nat => s nat
)"
apply (case_tac caseVar)
apply (auto)
done


instance ClosedBall:: type
by intro_classes
instance Real:: type
by intro_classes
instance S:: type
by intro_classes

axioms
def_nonempty : "ALL x. nonempty x = XXCXX (x, x)"

C_def : "XXCXX (x, y) = (EX s. rep x s & rep y s)"

MS_pos : "XXLtXEqXXX_3 (X0_2, d (x, y))"

MS_zero : "d (x, x) = X0_2"

MS_pos_definite : "d (x, y) = X0_2 = (x = y)"

MS_symm : "d (x, y) = d (y, x)"

MS_triangle : 
"XXLtXEqXXX_3 (d (x, z), XXPlusXXX (d (x, y), d (y, z)))"

one_greater_zero : "XXGtXXX (X1, X0_2)"

zero_leq_one : "XXLtXEqXXX_3 (X0_2, X1)"

half_gt_zero : "XXGtXXX (r, X0_2) --> XXGtXXX (half r, X0_2)"

half_plus_minus : 
"XXLtXEqXXX_3 (r, s) --> 
 XXLtXEqXXX_3 (XXPlusXXX (s, half (XXMinusXXX (r, s))), s)"

add_monotone : 
"XXLtXEqXXX_3 (a, b) & XXLtXEqXXX_3 (c, e) --> 
 XXLtXEqXXX_3 (XXPlusXXX (a, c), XXPlusXXX (b, e))"

sub_leq : 
"~ XXLtXEqXXX_3 (a, b) --> XXGtXXX (XXMinusXXX (a, b), X0_2)"

half_leq : 
"XXLtXEqXXX_3 (a, XXPlusXXX (half (XXMinusXXX (a, b)), b)) --> 
 XXLtXEqXXX_3 (a, b)"

half_leq_zero : 
"XXLtXEqXXX_3 (X0_2, r) --> XXLtXEqXXX_3 (X0_2, half r)"

comm_add : "XXPlusXXX (a, b) = XXPlusXXX (b, a)"

Real_half_plus : 
"half (XXPlusXXX (r, s)) = XXPlusXXX (half r, half s)"

Real_half_minus : 
"half (XXMinusXXX (r, s)) = XXMinusXXX (half r, half s)"

Real_minus_half : "XXMinusXXX (r, half r) = half r"

Real_half_monot : 
"XXLtXEqXXX_3 (half r, half s) = XXLtXEqXXX_3 (r, s)"

Real_abs_def : "VBarX__VBarX r = maxX (r, MinusXXX r)"

Real_sqr_def : "sqrXX r = XXxXXX (r, r)"

Real_sqrt_dom : "defOp (sqrtXX r) = XXGtXEqXXX (r, X0_2)"

Real_sqrt_idef [simp] : "sqrtXX (sqrXX r) = Some (VBarX__VBarX r)"

Real_2_def : "X2 = XXPlusXXX (X1, X1)"

Real_minus_def : "XXMinusXXX (r, r') = XXPlusXXX (r, MinusXXX r')"

Real_divide_dom : "~ defOp (XXSlashXXX (r, X0_2))"

Real_divide_idef : 
"XXSlashXXX (r, r') = Some r'' = (XXxXXX (r'', r') = r)"

Real_half_idef : "XXxXXX (X2, half r) = r"

ga_Nat [simp] : "True"

Real_ub_def : 
"XXLtXEqXXX_1 (M, r) = (ALL s. M s --> XXLtXEqXXX_3 (s, r))"

Real_lb_def : 
"XXLtXEqXXX_2 (r, M) = (ALL s. M s --> XXLtXEqXXX_3 (r, s))"

Real_inf_def : 
"inf_1 M = Some r = 
 (XXLtXEqXXX_2 (r, M) & 
  (ALL s. XXLtXEqXXX_2 (s, M) --> XXLtXEqXXX_3 (s, r)))"

Real_sup_def : 
"sup_1 M = Some r = 
 (XXLtXEqXXX_1 (M, r) & 
  (ALL s. XXLtXEqXXX_1 (M, s) --> XXLtXEqXXX_3 (r, s)))"

Real_isBounded_defCBrX : 
"isBounded M = 
 (EX ub. EX lb. XXLtXEqXXX_2 (lb, M) & XXLtXEqXXX_1 (M, ub))"

Real_inj_0 [simp] : "injX X0_1 = X0_2"

Real_inj_suc [simp] : "injX (suc nX) = XXPlusXXX (X1, injX nX)"

Real_archimedian : "EX nX. XXLtXEqXXX_3 (r, injX nX)"

FWO_plus_right : 
"ALL a. 
 ALL b. 
 ALL c. 
 XXLtXEqXXX_3 (b, c) --> 
 XXLtXEqXXX_3 (XXPlusXXX (a, b), XXPlusXXX (a, c))"

FWO_times_right : 
"ALL a. 
 ALL b. 
 ALL c. 
 XXLtXEqXXX_3 (b, c) & XXLtXEqXXX_3 (X0_2, a) --> 
 XXLtXEqXXX_3 (XXxXXX (a, b), XXxXXX (a, c))"

FWO_plus : 
"ALL a. 
 ALL b. 
 ALL c. 
 ALL d. 
 XXLtXEqXXX_3 (a, c) & XXLtXEqXXX_3 (b, d) --> 
 XXLtXEqXXX_3 (XXPlusXXX (a, b), XXPlusXXX (c, d))"

FWO_plus_left : 
"ALL a. 
 ALL b. 
 ALL c. 
 XXLtXEqXXX_3 (a, b) --> 
 XXLtXEqXXX_3 (XXPlusXXX (a, c), XXPlusXXX (b, c))"

FWO_times_left : 
"ALL a. 
 ALL b. 
 ALL c. 
 XXLtXEqXXX_3 (a, b) & XXLtXEqXXX_3 (X0_2, c) --> 
 XXLtXEqXXX_3 (XXxXXX (a, c), XXxXXX (b, c))"

Field_unary_minus_idef : "ALL x. XXPlusXXX (MinusXXX x, x) = X0_2"

dichotomy_TotalOrder : 
"ALL x. ALL y. XXLtXEqXXX_3 (x, y) | XXLtXEqXXX_3 (y, x)"

antisym : 
"ALL x. ALL y. XXLtXEqXXX_3 (x, y) & XXLtXEqXXX_3 (y, x) --> x = y"

trans : 
"ALL x. 
 ALL y. 
 ALL z. 
 XXLtXEqXXX_3 (x, y) & XXLtXEqXXX_3 (y, z) --> XXLtXEqXXX_3 (x, z)"

refl : "ALL x. XXLtXEqXXX_3 (x, x)"

min_inf_relation : 
"ALL x. ALL y. Some (minX (x, y)) = inf_2 (x, y)"

max_sup_relation : 
"ALL x. ALL y. Some (maxX (x, y)) = sup_2 (x, y)"

ga_comm_min : "ALL x. ALL y. minX (x, y) = minX (y, x)"

ga_comm_max : "ALL x. ALL y. maxX (x, y) = maxX (y, x)"

ga_assoc_min : 
"ALL x. 
 ALL y. ALL z. minX (x, minX (y, z)) = minX (minX (x, y), z)"

ga_assoc_max : 
"ALL x. 
 ALL y. ALL z. maxX (x, maxX (y, z)) = maxX (maxX (x, y), z)"

min_def_ExtTotalOrder : 
"ALL x. 
 ALL y. minX (x, y) = (if XXLtXEqXXX_3 (x, y) then x else y)"

max_def_ExtTotalOrder : 
"ALL x. 
 ALL y. maxX (x, y) = (if XXLtXEqXXX_3 (x, y) then y else x)"

ga_comm_inf : "ALL x. ALL y. inf_2 (x, y) = inf_2 (y, x)"

ga_comm_sup : "ALL x. ALL y. sup_2 (x, y) = sup_2 (y, x)"

inf_def_ExtPartialOrder : 
"ALL x. 
 ALL y. 
 ALL z. 
 inf_2 (x, y) = Some z = 
 (XXLtXEqXXX_3 (z, x) & 
  XXLtXEqXXX_3 (z, y) & 
  (ALL t. 
   XXLtXEqXXX_3 (t, x) & XXLtXEqXXX_3 (t, y) --> 
   XXLtXEqXXX_3 (t, z)))"

sup_def_ExtPartialOrder : 
"ALL x. 
 ALL y. 
 ALL z. 
 sup_2 (x, y) = Some z = 
 (XXLtXEqXXX_3 (x, z) & 
  XXLtXEqXXX_3 (y, z) & 
  (ALL t. 
   XXLtXEqXXX_3 (x, t) & XXLtXEqXXX_3 (y, t) --> 
   XXLtXEqXXX_3 (z, t)))"

geq_def_ExtPartialOrder : 
"ALL x. ALL y. XXGtXEqXXX (x, y) = XXLtXEqXXX_3 (y, x)"

less_def_ExtPartialOrder : 
"ALL x. ALL y. XXLtXXX (x, y) = (XXLtXEqXXX_3 (x, y) & ~ x = y)"

greater_def_ExtPartialOrder : 
"ALL x. ALL y. XXGtXXX (x, y) = XXLtXXX (y, x)"

EMSCB_center [simp] : "XXGtXXX (r, X0_2) --> rep (closedBall (x, r)) x"

EMSCB_closed : 
"~ rep a x --> 
 (EX r. ALL y. ~ (rep (closedBall (x, r)) y & ~ rep a y))"

EMSCB_rep_pos [simp] : 
"XXGtXXX (r, X0_2) --> 
 rep (closedBall (x, r)) y = XXLtXEqXXX_3 (d (x, y), r)"

EMSCB_rep_0 [simp] : "~ XXGtXXX (r, X0_2) --> ~ rep (closedBall (x, r)) y"

EMSCB_rep_inj : "rep a = rep b --> a = b"

Ax4 : "EX z. EX t. a = closedBall (z, t)"

ga_Nat_1 [simp] : "True"

theorem C_non_null : "ALL x. ALL y. XXCXX (x, y) --> XXCXX (x, x)"
using C_def by auto

ML "Header.record \"C_non_null\""

theorem C_sym : "ALL x. ALL y. XXCXX (x, y) --> XXCXX (y, x)"
using C_def by auto

ML "Header.record \"C_sym\""

lemma swap : "A --> B=C ==> B ==> A-->C"
by auto

lemma impLemma : "[| A; A==>B; B-->C|] ==> C"
by auto

lemma reflLemma : "x=y ==> XXLtXEqXXX_3 (x,y)"
using refl by auto

lemma MS_triangle_rev :
"XXLtXEqXXX_3 (d (x, z), XXPlusXXX (d (x, y), d (z, y)))"
by (simp add: MS_triangle MS_symm)

lemma C_id_lemma : "!!x y xa. \ 
       ALL z. (EX s. rep z s & rep x s) = (EX s. rep z s & rep y s) \
       ==> rep x xa ==> rep y xa"
apply (erule contrapos_pp)
apply (subst not_all)
apply (insert Ax4 [THEN allI, of "%x. x"])
apply (frule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (erule exE)
apply (erule exE)
apply (erule exE)
apply (erule exE)
apply (subst not_iff)
apply (case_tac "XXGtXXX (ta,X0_2)")
apply (rule_tac x="closedBall(xa,half (XXMinusXXX (d(za,xa),ta)))" in exI)
apply(auto)
apply((drule EMSCB_rep_pos [THEN swap])+)
apply(rule_tac P="XXLtXEqXXX_3 (d (za, xa), ta)" in notE)
apply(assumption)
apply(rule half_leq [THEN mp])
apply(rule trans [THEN spec, THEN spec, THEN spec, THEN mp])
apply(rule conjI)
defer
apply(rule add_monotone [THEN mp])
apply(rule conjI)
apply(erule mp)
back
apply(insert sub_leq [THEN mp])
apply(rule half_gt_zero [THEN mp])
apply(rule sub_leq [THEN mp])
apply(assumption+)

apply(rule_tac x="xa" in exI)
apply(simp)
apply(rule EMSCB_rep_pos [THEN mp, THEN iffD2])
apply(rule half_gt_zero [THEN mp])
apply(rule sub_leq [THEN mp])
apply(assumption)
apply(simp add: MS_zero)
apply(rule half_leq_zero [THEN mp])
apply(drule sub_leq [THEN mp])
apply(simp add: greater_def_ExtPartialOrder
                less_def_ExtPartialOrder)
apply(rule trans [THEN spec, THEN spec, THEN spec, THEN mp])
apply(rule conjI)
defer
apply(rule MS_triangle_rev)
apply(rule reflLemma)
apply(rule MS_symm)
done

theorem C_id : 
"ALL x. ALL y. (ALL z. XXCXX (z, x) = XXCXX (z, y)) --> x = y"
apply (auto simp add: C_def)
apply (rule EMSCB_rep_inj [THEN mp])
apply (rule ext)
apply (auto)
apply (rule_tac x="x" in C_id_lemma)
apply(auto)
apply (rule_tac x="y" in C_id_lemma)
apply(auto)
done

ML "Header.record \"C_id\""

theorem C_non_triv : "EX x. XXCXX (x, x)"
apply (simp add: C_def)
apply (rule exI)
apply (rule exI)
apply (rule EMSCB_rep_pos [THEN mp, THEN iffD2])
apply(rule one_greater_zero)
apply(rule iffD2)
apply(rule arg_cong)
back
defer
apply(rule zero_leq_one) 
using MS_pos_definite apply simp
done

ML "Header.record \"C_non_triv\""

end
