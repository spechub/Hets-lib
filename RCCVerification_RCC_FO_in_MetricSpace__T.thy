theory RCCVerification_RCC_FO_in_MetricSpace__T
imports "$HETS_ISABELLE_LIB/MainHC"
uses "$HETS_ISABELLE_LIB/prelude.ML"
begin

setup "Header.initialize
       [\"Ax1\", \"C_def\", \"EMSCB_center\", \"EMSCB_closed\",
        \"EMSCB_rep_pos\", \"EMSCB_rep_0\", \"EMSCB_rep_inj\", \"Ax4\",
        \"MS_pos\", \"MS_zero\", \"MS_pos_definite\", \"MS_symm\",
        \"MS_triangle\", \"one_greater_zero\", \"zero_leq_one\",
        \"half_gt_zero\", \"half_plus_minus\", \"add_monotone\",
        \"sub_leq\", \"half_leq\", \"half_leq_zero\", \"comm_add\",
        \"Real_half_plus\", \"Real_half_minus\", \"Real_minus_half\",
        \"Real_half_monot\", \"Real_abs_def\", \"Real_sqr_def\",
        \"Real_sqrt_dom\", \"Real_sqrt_idef\", \"Real_2_def\",
        \"Real_minus_def\", \"Real_divide_dom\", \"Real_divide_idef\",
        \"Real_half_idef\", \"Real_ub_def\", \"Real_lb_def\",
        \"Real_inf_def\", \"Real_sup_def\", \"Real_isBounded_def\",
        \"completeness\", \"Real_inj_0\", \"Real_inj_suc\",
        \"Real_archimedian\", \"FWO_plus_right\", \"FWO_times_right\",
        \"FWO_plus\", \"FWO_plus_left\", \"FWO_times_left\",
        \"dichotomy_TotalOrder\", \"antisym\", \"trans\", \"refl\",
        \"Field_unary_minus_idef\", \"min_inf_relation\",
        \"max_sup_relation\", \"ga_comm_min\", \"ga_comm_max\",
        \"ga_assoc_min\", \"ga_assoc_max\", \"ga_left_comm_min\",
        \"ga_left_comm_max\", \"min_def_ExtTotalOrder\",
        \"max_def_ExtTotalOrder\", \"ga_comm_inf\", \"ga_comm_sup\",
        \"inf_def_ExtPartialOrder\", \"sup_def_ExtPartialOrder\",
        \"geq_def_ExtPartialOrder\", \"less_def_ExtPartialOrder\",
        \"greater_def_ExtPartialOrder\", \"C_non_null\", \"C_sym\",
        \"C_id\", \"C_non_triv\"]"

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

axiomatization
where
Ax1 [rule_format] : "ALL (x :: ClosedBall). nonempty(x) = (x C x)"
and
C_def [rule_format] :
"ALL (x :: ClosedBall).
 ALL (y :: ClosedBall). (x C y) = (EX (s :: S). rep x s & rep y s)"
and
EMSCB_center [rule_format] :
"ALL (r :: Real).
 ALL (x :: S). r >' 0'' --> rep (closedBall(x, r)) x"
and
EMSCB_closed [rule_format] :
"ALL (a :: ClosedBall).
 ALL (x :: S).
 ~ rep a x -->
 (EX (r :: Real).
  ALL (y :: S). ~ (rep (closedBall(x, r)) y & ~ rep a y))"
and
EMSCB_rep_pos [rule_format] :
"ALL (r :: Real).
 ALL (x :: S).
 ALL (y :: S).
 r >' 0'' --> rep (closedBall(x, r)) y = (d(x, y) <=' r)"
and
EMSCB_rep_0 [rule_format] :
"ALL (r :: Real).
 ALL (x :: S).
 ALL (y :: S). ~ r >' 0'' --> ~ rep (closedBall(x, r)) y"
and
EMSCB_rep_inj [rule_format] :
"ALL (a :: ClosedBall).
 ALL (b :: ClosedBall). rep a = rep b --> a = b"
and
Ax4 [rule_format] :
"ALL (a :: ClosedBall).
 EX (z :: S). EX (t :: Real). a = closedBall(z, t)"
and
MS_pos [rule_format] :
"ALL (x :: S). ALL (y :: S). 0'' <=' d(x, y)"
and
MS_zero [rule_format] : "ALL (x :: S). d(x, x) = 0''"
and
MS_pos_definite [rule_format] :
"ALL (x :: S). ALL (y :: S). d(x, y) = 0'' = (x = y)"
and
MS_symm [rule_format] :
"ALL (x :: S). ALL (y :: S). d(x, y) = d(y, x)"
and
MS_triangle [rule_format] :
"ALL (x :: S).
 ALL (y :: S). ALL (z :: S). d(x, z) <=' d(x, y) +' d(y, z)"
and
one_greater_zero [rule_format] : "1' >' 0''"
and
zero_leq_one [rule_format] : "0'' <=' 1'"
and
half_gt_zero [rule_format] :
"ALL (r :: Real). r >' 0'' --> half(r) >' 0''"
and
half_plus_minus [rule_format] :
"ALL (r :: Real).
 ALL (s :: Real). r <=' s --> s +' half(r -' s) <=' s"
and
add_monotone [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real).
 ALL (e :: Real). a <=' b & c <=' e --> a +' c <=' b +' e"
and
sub_leq [rule_format] :
"ALL (a :: Real). ALL (b :: Real). ~ a <=' b --> a -' b >' 0''"
and
half_leq [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real). a <=' half(a -' b) +' b --> a <=' b"
and
half_leq_zero [rule_format] :
"ALL (r :: Real). 0'' <=' r --> 0'' <=' half(r)"
and
comm_add [rule_format] :
"ALL (a :: Real). ALL (b :: Real). a +' b = b +' a"
and
Real_half_plus [rule_format] :
"ALL (r :: Real).
 ALL (s :: Real). half(r +' s) = half(r) +' half(s)"
and
Real_half_minus [rule_format] :
"ALL (r :: Real).
 ALL (s :: Real). half(r -' s) = half(r) -' half(s)"
and
Real_minus_half [rule_format] :
"ALL (r :: Real). r -' half(r) = half(r)"
and
Real_half_monot [rule_format] :
"ALL (r :: Real).
 ALL (s :: Real). (half(r) <=' half(s)) = (r <=' s)"
and
Real_abs_def [rule_format] :
"ALL (r :: Real). | r | = max'(r, -' r)"
and
Real_sqr_def [rule_format] : "ALL (r :: Real). sqr r = r *' r"
and
Real_sqrt_dom [rule_format] :
"ALL (r :: Real). defOp (sqrt r) = (r >=' 0'')"
and
Real_sqrt_idef [rule_format] :
"ALL (r :: Real). sqrt sqr r = makePartial ( | r | )"
and
Real_2_def [rule_format] : "2' = 1' +' 1'"
and
Real_minus_def [rule_format] :
"ALL (r :: Real). ALL (r' :: Real). r -' r' = r +' -' r'"
and
Real_divide_dom [rule_format] :
"ALL (r :: Real). ~ defOp (r /' 0'')"
and
Real_divide_idef [rule_format] :
"ALL (r :: Real).
 ALL (r' :: Real).
 ALL (r'' :: Real).
 (~ r' = 0'' --> r /' r' = makePartial r'') = (r'' *' r' = r)"
and
Real_half_idef [rule_format] : "ALL (r :: Real). 2' *' half(r) = r"
and
Real_ub_def [rule_format] :
"ALL (M :: Real => bool).
 ALL (r :: Real). (M <=_3 r) = (ALL (s :: Real). M s --> s <=' r)"
and
Real_lb_def [rule_format] :
"ALL (M :: Real => bool).
 ALL (r :: Real). (r <='' M) = (ALL (s :: Real). M s --> r <=' s)"
and
Real_inf_def [rule_format] :
"ALL (M :: Real => bool).
 ALL (r :: Real).
 inf''(M) = makePartial r =
 (r <='' M & (ALL (s :: Real). s <='' M --> s <=' r))"
and
Real_sup_def [rule_format] :
"ALL (M :: Real => bool).
 ALL (r :: Real).
 sup''(M) = makePartial r =
 (M <=_3 r & (ALL (s :: Real). M <=_3 s --> r <=' s))"
and
Real_isBounded_def [rule_format] :
"ALL (M :: Real => bool).
 isBounded(M) =
 (EX (ub :: Real). EX (lb :: Real). lb <='' M & M <=_3 ub)"
and
completeness [rule_format] :
"ALL (M :: Real => bool).
 isBounded(M) --> defOp (inf''(M)) & defOp (sup''(M))"
and
Real_inj_0 [rule_format] : "inj'(0') = 0''"
and
Real_inj_suc [rule_format] :
"ALL (X_n :: X_Nat). inj'(suc(X_n)) = 1' +' inj'(X_n)"
and
Real_archimedian [rule_format] :
"ALL (r :: Real). EX (X_n :: X_Nat). r <=' inj'(X_n)"
and
FWO_plus_right [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real). ALL (c :: Real). b <=' c --> a +' b <=' a +' c"
and
FWO_times_right [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real). b <=' c & 0'' <=' a --> a *' b <=' a *' c"
and
FWO_plus [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real).
 ALL (X_d :: Real). a <=' c & b <=' X_d --> a +' b <=' c +' X_d"
and
FWO_plus_left [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real). ALL (c :: Real). a <=' b --> a +' c <=' b +' c"
and
FWO_times_left [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real). a <=' b & 0'' <=' c --> a *' c <=' b *' c"
and
dichotomy_TotalOrder [rule_format] :
"ALL (x :: Real). ALL (y :: Real). x <=' y | y <=' x"
and
antisym [rule_format] :
"ALL (x :: Real). ALL (y :: Real). x <=' y & y <=' x --> x = y"
and
trans [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real). ALL (z :: Real). x <=' y & y <=' z --> x <=' z"
and
refl [rule_format] : "ALL (x :: Real). x <=' x"
and
Field_unary_minus_idef [rule_format] :
"ALL (x :: Real). -' x +' x = 0''"
and
min_inf_relation [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real). makePartial (min'(x, y)) = inf'(x, y)"
and
max_sup_relation [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real). makePartial (max'(x, y)) = sup'(x, y)"
and
ga_comm_min [rule_format] :
"ALL (x :: Real). ALL (y :: Real). min'(x, y) = min'(y, x)"
and
ga_comm_max [rule_format] :
"ALL (x :: Real). ALL (y :: Real). max'(x, y) = max'(y, x)"
and
ga_assoc_min [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real). min'(min'(x, y), z) = min'(x, min'(y, z))"
and
ga_assoc_max [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real). max'(max'(x, y), z) = max'(x, max'(y, z))"
and
ga_left_comm_min [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real). min'(x, min'(y, z)) = min'(y, min'(x, z))"
and
ga_left_comm_max [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real). max'(x, max'(y, z)) = max'(y, max'(x, z))"
and
min_def_ExtTotalOrder [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real). min'(x, y) = (if x <=' y then x else y)"
and
max_def_ExtTotalOrder [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real). max'(x, y) = (if x <=' y then y else x)"
and
ga_comm_inf [rule_format] :
"ALL (x :: Real). ALL (y :: Real). inf'(x, y) = inf'(y, x)"
and
ga_comm_sup [rule_format] :
"ALL (x :: Real). ALL (y :: Real). sup'(x, y) = sup'(y, x)"
and
inf_def_ExtPartialOrder [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real).
 inf'(x, y) = makePartial z =
 (z <=' x &
  z <=' y & (ALL (t :: Real). t <=' x & t <=' y --> t <=' z))"
and
sup_def_ExtPartialOrder [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real).
 sup'(x, y) = makePartial z =
 (x <=' z &
  y <=' z & (ALL (t :: Real). x <=' t & y <=' t --> z <=' t))"
and
geq_def_ExtPartialOrder [rule_format] :
"ALL (x :: Real). ALL (y :: Real). (x >=' y) = (y <=' x)"
and
less_def_ExtPartialOrder [rule_format] :
"ALL (x :: Real). ALL (y :: Real). (x <' y) = (x <=' y & ~ x = y)"
and
greater_def_ExtPartialOrder [rule_format] :
"ALL (x :: Real). ALL (y :: Real). (x >' y) = (y <' x)"

declare EMSCB_rep_pos [simp]
declare EMSCB_center [simp]
declare EMSCB_rep_0 [simp]
declare MS_pos [simp]
declare MS_zero [simp]
declare MS_triangle [simp]
declare MS_pos_definite [simp]
declare one_greater_zero [simp]
declare zero_leq_one [simp]
declare half_plus_minus [simp]
declare sub_leq [simp]
declare half_leq_zero [simp]
declare Real_minus_half [simp]
declare Real_half_monot [simp]
declare Real_divide_dom [simp]
declare Real_half_idef [simp]
declare completeness [simp]
declare Real_inj_0 [simp]
declare FWO_plus_right [simp]
declare FWO_plus_left [simp]
declare refl [simp]
declare Field_unary_minus_idef [simp]
declare min_inf_relation [simp]
declare max_sup_relation [simp]
declare ga_comm_min [simp]
declare ga_comm_max [simp]
declare ga_assoc_min [simp]
declare ga_assoc_max [simp]
declare ga_left_comm_min [simp]
declare ga_left_comm_max [simp]
declare ga_comm_inf [simp]
declare ga_comm_sup [simp]

theorem C_non_null :
"ALL (x :: ClosedBall). ALL (y :: ClosedBall). x C y --> x C x"
using Ax1 C_def Real_abs_def Real_sqr_def Real_sqrt_idef Real_2_def
      Real_minus_def Real_divide_idef Real_half_idef Real_ub_def
      Real_lb_def Real_inf_def Real_sup_def Real_isBounded_def
      Field_unary_minus_idef
by (auto)

setup "Header.record \"C_non_null\""

theorem C_sym :
"ALL (x :: ClosedBall). ALL (y :: ClosedBall). x C y --> y C x"
using Ax1 C_def Real_abs_def Real_sqr_def Real_sqrt_idef Real_2_def
      Real_minus_def Real_divide_idef Real_half_idef Real_ub_def
      Real_lb_def Real_inf_def Real_sup_def Real_isBounded_def
      Field_unary_minus_idef
by (auto)

setup "Header.record \"C_sym\""

lemma impLemma : "[| A; A==>B; B-->D|] ==> D"
by auto

lemma reflLemma : "x=y ==> x <=' y"
using refl by auto

lemma MS_triangle_rev :
"d(x, z) <=' (d(x, y) +' d(z, y))"
by (simp add: MS_symm)

lemma EMSCB_rep_pos1 : "rep (closedBall(x, r)) y \<Longrightarrow> r >' 0'' \<longrightarrow> d(x, y) <=' r"
by auto

lemma C_id_lemma : "!!x y xa.
       ALL z. (EX s. rep z s & rep x s) = (EX s. rep z s & rep y s)
       ==> rep x xa ==> rep y xa"
apply (erule contrapos_pp)
apply (subst not_all)
apply (insert Ax4 [THEN allI, of "%x. x"])
apply (frule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (erule exE)+
apply (subst not_iff)
apply (case_tac "ta >' 0''")
apply (rule_tac x="closedBall(xa, half (d(za, xa) -' ta))" in exI)
apply(auto)
apply(drule EMSCB_rep_pos1)+
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
 (ALL (z :: ClosedBall). (z C x) = (z C y)) --> x = y"
apply (auto simp add: C_def)
apply (rule EMSCB_rep_inj)
apply (rule ext)
apply (auto)
apply (rule_tac x="x" in C_id_lemma)
apply(auto)
apply (rule_tac x="y" in C_id_lemma)
apply(auto)
done

setup "Header.record \"C_id\""

theorem C_non_triv : "EX (x :: ClosedBall). x C x"
apply (simp add: C_def)
apply (rule exI)+
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

setup "Header.record \"C_non_triv\""

end
