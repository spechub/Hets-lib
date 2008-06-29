theory RCCDagstuhl2_NN_T
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"C_non_null\", \"C_sym\", \"C_id\", \"C_non_triv\", \"refl\",
     \"trans\", \"antisym\", \"geq_def_ExtPartialOrder\",
     \"less_def_ExtPartialOrder\", \"greater_def_ExtPartialOrder\",
     \"ga_comm_inf\", \"ga_comm_sup\", \"inf_def_ExtPartialOrder\",
     \"sup_def_ExtPartialOrder\", \"dichotomy_TotalOrder\",
     \"ga_comm_min\", \"ga_comm_max\", \"ga_assoc_min\",
     \"ga_assoc_max\", \"min_def_ExtTotalOrder\",
     \"max_def_ExtTotalOrder\", \"min_inf_relation\",
     \"max_sup_relation\", \"Field_unary_minus_idef\",
     \"FWO_plus_left\", \"FWO_times_left\", \"FWO_plus_right\",
     \"FWO_times_right\", \"FWO_plus\", \"ga_Nat\", \"Real_ub_def\",
     \"Real_lb_def\", \"Real_inf_def\", \"Real_sup_def\",
     \"Real_isBounded_defXCBr\", \"Real_inj_0\", \"Real_inj_suc\",
     \"Real_archimedian\", \"Real_abs_def\", \"Real_sqr_def\",
     \"Real_sqrt_dom\", \"Real_sqrt_idef\", \"Real_2_def\",
     \"Real_minus_def\", \"Real_divide_dom\", \"Real_divide_idef\",
     \"Real_half_idef\", \"one_greater_zero\", \"zero_leq_one\",
     \"half_gt_zero\", \"half_plus_minus\", \"add_monotone\",
     \"sub_leq\", \"half_leq\", \"half_leq_zero\", \"comm_add\",
     \"Real_half_plus\", \"Real_half_minus\", \"Real_minus_half\",
     \"Real_half_monot\", \"MS_pos_definite\", \"MS_symm\",
     \"MS_triangle\", \"MS_pos\", \"MS_zero\", \"EMSCB_rep_pos\",
     \"EMSCB_rep_0\", \"EMSCB_rep_inj\", \"Ax4\", \"EMSCB_center\",
     \"EMSCB_closed\", \"def_nonempty\", \"C_def\"]"

typedecl ClosedBall
typedecl Real
typedecl S

datatype Nat = X0X1 ("0''") | X_suc "Nat" ("suc/'(_')" [10] 999)

consts
X0X2 :: "Real" ("0''''")
X1 :: "Real" ("1''")
X2 :: "Real" ("2")
XMinus__X :: "Real => Real" ("(-''/ _)" [56] 56)
XVBar__XVBar :: "Real => Real" ("(|/ _/ |)" [10] 999)
X__C__X :: "ClosedBall => ClosedBall => bool" ("(_/ C/ _)" [44,44] 42)
X__XGtXEq__X :: "Real => Real => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XGt__X :: "Real => Real => bool" ("(_/ >''/ _)" [44,44] 42)
X__XLtXEq__XX1 :: "(Real => bool) => Real => bool" ("(_/ <=''/ _)" [44,44] 42)
X__XLtXEq__XX2 :: "Real => (Real => bool) => bool" ("(_/ <=''''/ _)" [44,44] 42)
X__XLtXEq__XX3 :: "Real => Real => bool" ("(_/ <='_3/ _)" [44,44] 42)
X__XLt__X :: "Real => Real => bool" ("(_/ <''/ _)" [44,44] 42)
X__XMinus__X :: "Real => Real => Real" ("(_/ -''/ _)" [54,54] 52)
X__XPlus__X :: "Real => Real => Real" ("(_/ +''/ _)" [54,54] 52)
X__XSlash__X :: "Real => Real => Real option" ("(_/ '/''/ _)" [54,54] 52)
X__Xx__X :: "Real => Real => Real" ("(_/ *''/ _)" [54,54] 52)
X_closedBall :: "S => Real => ClosedBall" ("closedBall/'(_,/ _')" [10,10] 999)
X_d :: "S => S => Real" ("d/'(_,/ _')" [10,10] 999)
X_half :: "Real => Real" ("half/'(_')" [10] 999)
X_inj :: "Nat => Real" ("inj''/'(_')" [10] 999)
X_isBounded :: "(Real => bool) => bool" ("isBounded/'(_')" [10] 999)
X_max :: "Real => Real => Real" ("max''/'(_,/ _')" [10,10] 999)
X_min :: "Real => Real => Real" ("min''/'(_,/ _')" [10,10] 999)
X_nonempty :: "ClosedBall => bool" ("nonempty/'(_')" [10] 999)
infX1 :: "(Real => bool) => Real option" ("inf/'(_')" [10] 999)
infX2 :: "Real => Real => Real option" ("inf''/'(_,/ _')" [10,10] 999)
rep :: "ClosedBall => S => bool"
sqr__X :: "Real => Real" ("(sqr/ _)" [56] 56)
sqrt__X :: "Real => Real option" ("(sqrt/ _)" [56] 56)
supX1 :: "(Real => bool) => Real option" ("sup/'(_')" [10] 999)
supX2 :: "Real => Real => Real option" ("sup''/'(_,/ _')" [10,10] 999)

instance ClosedBall:: type
by intro_classes
instance Nat:: type
by intro_classes
instance Real:: type
by intro_classes
instance S:: type
by intro_classes

axioms
refl [simp] : "ALL x. x <=_3 x"

trans : "ALL x. ALL y. ALL z. x <=_3 y & y <=_3 z --> x <=_3 z"

antisym : "ALL x. ALL y. x <=_3 y & y <=_3 x --> x = y"

geq_def_ExtPartialOrder : "ALL x. ALL y. (x >=' y) = (y <=_3 x)"

less_def_ExtPartialOrder :
"ALL x. ALL y. (x <' y) = (x <=_3 y & ~ x = y)"

greater_def_ExtPartialOrder : "ALL x. ALL y. (x >' y) = (y <' x)"

ga_comm_inf : "ALL x. ALL y. inf'(x, y) = inf'(y, x)"

ga_comm_sup : "ALL x. ALL y. sup'(x, y) = sup'(y, x)"

inf_def_ExtPartialOrder :
"ALL x.
 ALL y.
 ALL z.
 inf'(x, y) = Some z =
 (z <=_3 x & z <=_3 y & (ALL t. t <=_3 x & t <=_3 y --> t <=_3 z))"

sup_def_ExtPartialOrder :
"ALL x.
 ALL y.
 ALL z.
 sup'(x, y) = Some z =
 (x <=_3 z & y <=_3 z & (ALL t. x <=_3 t & y <=_3 t --> z <=_3 t))"

dichotomy_TotalOrder [simp] : "ALL x. ALL y. x <=_3 y | y <=_3 x"

ga_comm_min : "ALL x. ALL y. min'(x, y) = min'(y, x)"

ga_comm_max : "ALL x. ALL y. max'(x, y) = max'(y, x)"

ga_assoc_min :
"ALL x. ALL y. ALL z. min'(x, min'(y, z)) = min'(min'(x, y), z)"

ga_assoc_max :
"ALL x. ALL y. ALL z. max'(x, max'(y, z)) = max'(max'(x, y), z)"

min_def_ExtTotalOrder :
"ALL x. ALL y. min'(x, y) = (if x <=_3 y then x else y)"

max_def_ExtTotalOrder :
"ALL x. ALL y. max'(x, y) = (if x <=_3 y then y else x)"

min_inf_relation [simp] :
"ALL x. ALL y. Some (min'(x, y)) = inf'(x, y)"

max_sup_relation [simp] :
"ALL x. ALL y. Some (max'(x, y)) = sup'(x, y)"

Field_unary_minus_idef [simp] : "ALL x. -' x +' x = 0''"

FWO_plus_left [simp] :
"ALL a. ALL b. ALL c. a <=_3 b --> a +' c <=_3 b +' c"

FWO_times_left :
"ALL a. ALL b. ALL c. a <=_3 b & 0'' <=_3 c --> a *' c <=_3 b *' c"

FWO_plus_right [simp] :
"ALL a. ALL b. ALL c. b <=_3 c --> a +' b <=_3 a +' c"

FWO_times_right :
"ALL a. ALL b. ALL c. b <=_3 c & 0'' <=_3 a --> a *' b <=_3 a *' c"

FWO_plus :
"ALL a.
 ALL b.
 ALL c. ALL X_d. a <=_3 c & b <=_3 X_d --> a +' b <=_3 c +' X_d"

ga_Nat [simp] : "True"

Real_ub_def : "(M <=' r) = (ALL s. M s --> s <=_3 r)"

Real_lb_def : "(r <='' M) = (ALL s. M s --> r <=_3 s)"

Real_inf_def :
"inf(M) = Some r = (r <='' M & (ALL s. s <='' M --> s <=_3 r))"

Real_sup_def :
"sup(M) = Some r = (M <=' r & (ALL s. M <=' s --> r <=_3 s))"

Real_isBounded_defXCBr :
"isBounded(M) = (EX ub. EX lb. lb <='' M & M <=' ub)"

Real_inj_0 [simp] : "inj'(0') = 0''"

Real_inj_suc : "inj'(suc(X_n)) = 1' +' inj'(X_n)"

Real_archimedian : "EX X_n. r <=_3 inj'(X_n)"

Real_abs_def : "| r | = max'(r, -' r)"

Real_sqr_def : "sqr r = r *' r"

Real_sqrt_dom : "defOp (sqrt r) = (r >=' 0'')"

Real_sqrt_idef : "sqrt sqr r = Some ( | r | )"

Real_2_def : "2 = 1' +' 1'"

Real_minus_def : "r -' r' = r +' -' r'"

Real_divide_dom [simp] : "~ defOp (r /' 0'')"

Real_divide_idef [simp] : "r /' r' = Some r'' = (r'' *' r' = r)"

Real_half_idef [simp] : "2 *' half(r) = r"

one_greater_zero [simp] : "1' >' 0''"

zero_leq_one [simp] : "0'' <=_3 1'"

half_gt_zero : "r >' 0'' --> half(r) >' 0''"

half_plus_minus [simp] : "r <=_3 s --> s +' half(r -' s) <=_3 s"

add_monotone : "a <=_3 b & c <=_3 e --> a +' c <=_3 b +' e"

sub_leq [simp] : "~ a <=_3 b --> a -' b >' 0''"

half_leq : "a <=_3 half(a -' b) +' b --> a <=_3 b"

half_leq_zero [simp] : "0'' <=_3 r --> 0'' <=_3 half(r)"

comm_add : "a +' b = b +' a"

Real_half_plus : "half(r +' s) = half(r) +' half(s)"

Real_half_minus : "half(r -' s) = half(r) -' half(s)"

Real_minus_half [simp] : "r -' half(r) = half(r)"

Real_half_monot [simp] : "(half(r) <=_3 half(s)) = (r <=_3 s)"

MS_pos_definite [simp] : "d(x, y) = 0'' = (x = y)"

MS_symm : "d(x, y) = d(y, x)"

MS_triangle [simp] : "d(x, z) <=_3 d(x, y) +' d(y, z)"

MS_pos [simp] : "0'' <=_3 d(x, y)"

MS_zero [simp] : "d(x, x) = 0''"

EMSCB_rep_pos [simp] :
"r >' 0'' --> rep (closedBall(x, r)) y = (d(x, y) <=_3 r)"

EMSCB_rep_0 [simp] : "~ r >' 0'' --> ~ rep (closedBall(x, r)) y"

EMSCB_rep_inj : "rep a = rep b --> a = b"

Ax4 : "EX z. EX t. a = closedBall(z, t)"

EMSCB_center [simp] : "r >' 0'' --> rep (closedBall(x, r)) x"

EMSCB_closed [simp] :
"~ rep a x -->
 (EX r. ALL y. ~ (rep (closedBall(x, r)) y & ~ rep a y))"

def_nonempty : "ALL x. nonempty(x) = (x C x)"

C_def : "(x C y) = (EX s. rep x s & rep y s)"

theorem C_non_null : "ALL x. ALL y. x C y --> x C x"
using C_def by auto

ML "Header.record \"C_non_null\""

theorem C_sym : "ALL x. ALL y. x C y --> y C x"
using C_def by auto

ML "Header.record \"C_sym\""

lemma swap : "A --> B=D ==> B ==> A-->D"
by auto

lemma impLemma : "[| A; A==>B; B-->D|] ==> D"
by auto

lemma reflLemma : "x=y ==> x <=_3 y"
using refl by auto

lemma MS_triangle_rev :
"d(x, z) <=_3 (d(x, y) +' d(z, y))"
by (simp add: MS_symm)

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
apply (case_tac "ta >' 0''")
apply (rule_tac x="closedBall(xa, half (d(za, xa) -' ta))" in exI)
apply(auto)
apply((drule EMSCB_rep_pos [THEN swap])+)
apply(rule_tac P="d(za, xa) <=_3 ta" in notE)
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
apply simp
apply(rule EMSCB_rep_pos [THEN mp, THEN iffD2])
apply(rule half_gt_zero [THEN mp])
apply(rule sub_leq [THEN mp])
apply(assumption)
apply simp
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

theorem C_id : "ALL x. ALL y. (ALL z. (z C x) = (z C y)) --> x = y"
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

theorem C_non_triv : "EX x. x C x"
apply (simp add: C_def)
apply (rule exI)
apply (rule exI)
apply (rule EMSCB_rep_pos [THEN mp, THEN iffD2])
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
