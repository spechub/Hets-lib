theory LinearAlgebra_EuclideanVectorSpace_E1
imports "$HETS_LIB/Isabelle/MainHCPairs"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"subtype_def\", \"subtype_pred_def\",
     \"ga_assoc___Xx__\", \"ga_right_unit___Xx__\",
     \"ga_left_unit___Xx__\", \"inv_Group_2\", \"rinv_Group\",
     \"ga_comm___Xx__\", \"ga_assoc___Xx___1\",
     \"ga_right_unit___Xx___1\", \"ga_left_unit___Xx___1\",
     \"distr1_Ring\", \"distr2_Ring\", \"ga_comm___Xx___1\",
     \"noZeroDiv\", \"zeroNeqOne\", \"Ax1\", \"ga_assoc___Xx___2\",
     \"ga_right_unit___Xx___2\", \"ga_left_unit___Xx___2\",
     \"inv_Group_1\", \"rinv_Group_1\", \"binary_inverse\", \"Ax1_1\",
     \"refl\", \"trans\", \"antisym\", \"dichotomy_TotalOrder\",
     \"FWO_plus_left\", \"FWO_times_left\", \"FWO_plus_right\",
     \"FWO_times_right\", \"FWO_plus\", \"inf_def\",
     \"Real_completeness\", \"geq_def_ExtPartialOrder\",
     \"less_def_ExtPartialOrder\", \"greater_def_ExtPartialOrder\",
     \"ga_comm_inf\", \"ga_comm_sup\", \"inf_def_ExtPartialOrder\",
     \"sup_def_ExtPartialOrder\", \"ga_comm_min\", \"ga_comm_max\",
     \"ga_assoc_min\", \"ga_assoc_max\", \"ga_left_comm_min\",
     \"ga_left_comm_max\", \"min_def_ExtTotalOrder\",
     \"max_def_ExtTotalOrder\", \"min_inf_relation\",
     \"max_sup_relation\", \"RealNonNeg_pred_def\",
     \"RealPos_pred_def\", \"Ax3\", \"Ax4\", \"RealNonNeg_subtype\",
     \"RealPos_subtype\", \"abs_def\", \"ga_assoc___Xx___3\",
     \"ga_right_unit___Xx___3\", \"ga_left_unit___Xx___3\",
     \"inv_Group_3\", \"rinv_Group_2\", \"ga_comm___Xx___3\",
     \"binary_inverse_1\", \"unit\", \"mix_assoc\", \"distr_Field\",
     \"distr_Space\", \"zero_by_left_zero\", \"zero_by_right_zero\",
     \"inverse_by_XMinus1\", \"distributive\", \"homogeneous\",
     \"symmetric\", \"pos_definite\", \"right_distributive\",
     \"right_homogeneous\", \"non_degenerate\"]"

typedecl NonZero
typedecl Real
typedecl RealNonNeg
typedecl RealPos
typedecl Space

consts
X0X1 :: "Real" ("0''")
X0X2 :: "Space" ("0''''")
X1X1 :: "NonZero" ("1''")
X1X2 :: "Real" ("1''''")
XMinus__XX1 :: "Real => Real" ("(-''/ _)" [56] 56)
XMinus__XX2 :: "Space => Space" ("(-''''/ _)" [56] 56)
X_RealNonNeg_inj :: "RealNonNeg => Real" ("RealNonNeg'_inj/'(_')" [3] 999)
X_RealNonNeg_pred :: "Real => bool" ("RealNonNeg'_pred/'(_')" [3] 999)
X_RealNonNeg_proj :: "Real => RealNonNeg" ("RealNonNeg'_proj/'(_')" [3] 999)
X_RealPos_inj :: "RealPos => Real" ("RealPos'_inj/'(_')" [3] 999)
X_RealPos_pred :: "Real => bool" ("RealPos'_pred/'(_')" [3] 999)
X_RealPos_proj :: "Real => RealPos" ("RealPos'_proj/'(_')" [3] 999)
X__XGtXEq__X :: "Real => Real => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XGt__X :: "Real => Real => bool" ("(_/ >''/ _)" [44,44] 42)
X__XLtXEq__X :: "Real => Real => bool" ("(_/ <=''/ _)" [44,44] 42)
X__XLt__X :: "Real => Real => bool" ("(_/ <''/ _)" [44,44] 42)
X__XMinus__XX1 :: "Real => Real => Real" ("(_/ -''/ _)" [54,54] 52)
X__XMinus__XX2 :: "Space => Space => Space" ("(_/ -''''/ _)" [54,54] 52)
X__XPlus__XX1 :: "Real => Real => Real" ("(_/ +''/ _)" [54,54] 52)
X__XPlus__XX2 :: "Space => Space => Space" ("(_/ +''''/ _)" [54,54] 52)
X__XSlash__X :: "Real => NonZero => Real" ("(_/ '/''/ _)" [54,54] 52)
X__Xx__XX1 :: "NonZero => NonZero => NonZero" ("(_/ *''/ _)" [54,54] 52)
X__Xx__XX2 :: "Real => Real => Real" ("(_/ *''''/ _)" [54,54] 52)
X__Xx__XX3 :: "Real => Space => Space" ("(_/ *'_3/ _)" [54,54] 52)
X__Xx__XX4 :: "Space => Space => Real" ("(_/ *'_4/ _)" [54,54] 52)
X_abs :: "Real => RealNonNeg" ("abs''/'(_')" [3] 999)
X_gn_inj :: "'a => 'b" ("gn'_inj/'(_')" [3] 999)
X_gn_proj :: "'a => 'b partial" ("gn'_proj/'(_')" [3] 999)
X_inv :: "NonZero => NonZero" ("inv''/'(_')" [3] 999)
X_isSubtype :: "('s => 't) => ('t => 's) => bool" ("isSubtype/'(_,/ _')" [3,3] 999)
X_isSubtypeWithPred :: "('t => bool) => ('s => 't) => ('t => 's) => bool" ("isSubtypeWithPred/'(_,/ _,/ _')" [3,3,3] 999)
X_max :: "Real => Real => Real" ("max''/'(_,/ _')" [3,3] 999)
X_min :: "Real => Real => Real" ("min''/'(_,/ _')" [3,3] 999)
X_sup :: "Real => Real => Real partial" ("sup/'(_,/ _')" [3,3] 999)
infX1 :: "Real => Real => Real partial" ("inf''/'(_,/ _')" [3,3] 999)
infX2 :: "(Real => bool) => Real partial" ("inf''''/'(_')" [3] 999)

axioms
subtype_def [rule_format] :
"ALL injection.
 ALL projection.
 isSubtype(injection, projection) =
 (ALL x. x = projection (injection x))"

subtype_pred_def [rule_format] :
"ALL P.
 ALL injection.
 ALL projection.
 isSubtypeWithPred(P, injection, projection) =
 ((isSubtype(injection, projection) &
   (ALL x. P x --> x = injection (projection x))) &
  (ALL x. P (injection x)))"

ga_assoc___Xx__ [rule_format] :
"ALL x. ALL y. ALL z. (x +' y) +' z = x +' (y +' z)"

ga_right_unit___Xx__ [rule_format] : "ALL x. x +' 0' = x"

ga_left_unit___Xx__ [rule_format] : "ALL x. 0' +' x = x"

inv_Group_2 [rule_format] : "ALL x. -' x +' x = 0'"

rinv_Group [rule_format] : "ALL x. x +' -' x = 0'"

ga_comm___Xx__ [rule_format] : "ALL x. ALL y. x +' y = y +' x"

ga_assoc___Xx___1 [rule_format] :
"ALL x. ALL y. ALL z. (x *'' y) *'' z = x *'' (y *'' z)"

ga_right_unit___Xx___1 [rule_format] : "ALL x. x *'' 1'' = x"

ga_left_unit___Xx___1 [rule_format] : "ALL x. 1'' *'' x = x"

distr1_Ring [rule_format] :
"ALL x. ALL y. ALL z. (x +' y) *'' z = (x *'' z) +' (y *'' z)"

distr2_Ring [rule_format] :
"ALL x. ALL y. ALL z. z *'' (x +' y) = (z *'' x) +' (z *'' y)"

ga_comm___Xx___1 [rule_format] : "ALL x. ALL y. x *'' y = y *'' x"

noZeroDiv [rule_format] :
"ALL x. ALL y. x *'' y = 0' --> x = 0' | y = 0'"

zeroNeqOne [rule_format] : "~ 1'' = 0'"

Ax1 [rule_format] : "ALL x. defOp (gn_proj(x)) = (~ x = 0')"

ga_assoc___Xx___2 [rule_format] :
"ALL x. ALL y. ALL z. (x *' y) *' z = x *' (y *' z)"

ga_right_unit___Xx___2 [rule_format] : "ALL x. x *' 1' = x"

ga_left_unit___Xx___2 [rule_format] : "ALL x. 1' *' x = x"

inv_Group_1 [rule_format] : "ALL x. inv'(x) *' x = 1'"

rinv_Group_1 [rule_format] : "ALL x. x *' inv'(x) = 1'"

binary_inverse [rule_format] : "ALL x. ALL y. x -' y = x +' -' y"

Ax1_1 [rule_format] :
"ALL x. ALL y. x /' y = x *'' gn_inj(inv'(y))"

refl [rule_format] : "ALL x. x <=' x"

trans [rule_format] :
"ALL x. ALL y. ALL z. x <=' y & y <=' z --> x <=' z"

antisym [rule_format] : "ALL x. ALL y. x <=' y & y <=' x --> x = y"

dichotomy_TotalOrder [rule_format] :
"ALL x. ALL y. x <=' y | y <=' x"

FWO_plus_left [rule_format] :
"ALL a. ALL b. ALL c. a <=' b --> a +' c <=' b +' c"

FWO_times_left [rule_format] :
"ALL a. ALL b. ALL c. a <=' b & 0' <=' c --> a *'' c <=' b *'' c"

FWO_plus_right [rule_format] :
"ALL a. ALL b. ALL c. b <=' c --> a +' b <=' a +' c"

FWO_times_right [rule_format] :
"ALL a. ALL b. ALL c. b <=' c & 0' <=' a --> a *'' b <=' a *'' c"

FWO_plus [rule_format] :
"ALL a.
 ALL b. ALL c. ALL d. a <=' c & b <=' d --> a +' b <=' c +' d"

inf_def [rule_format] :
"ALL S.
 ALL m.
 inf''(S) = makePartial m =
 (ALL m2. (ALL x. S x --> x <=' m2) --> m <=' m2)"

Real_completeness [rule_format] :
"ALL S.
 (EX x. S x) & (EX B. ALL x. S x --> x <=' B) -->
 (EX m. makePartial m = inf''(S))"

geq_def_ExtPartialOrder [rule_format] :
"ALL x. ALL y. (x >=' y) = (y <=' x)"

less_def_ExtPartialOrder [rule_format] :
"ALL x. ALL y. (x <' y) = (x <=' y & ~ x = y)"

greater_def_ExtPartialOrder [rule_format] :
"ALL x. ALL y. (x >' y) = (y <' x)"

ga_comm_inf [rule_format] : "ALL x. ALL y. inf'(x, y) = inf'(y, x)"

ga_comm_sup [rule_format] : "ALL x. ALL y. sup(x, y) = sup(y, x)"

inf_def_ExtPartialOrder [rule_format] :
"ALL x.
 ALL y.
 ALL z.
 inf'(x, y) = makePartial z =
 (z <=' x & z <=' y & (ALL t. t <=' x & t <=' y --> t <=' z))"

sup_def_ExtPartialOrder [rule_format] :
"ALL x.
 ALL y.
 ALL z.
 sup(x, y) = makePartial z =
 (x <=' z & y <=' z & (ALL t. x <=' t & y <=' t --> z <=' t))"

ga_comm_min [rule_format] : "ALL x. ALL y. min'(x, y) = min'(y, x)"

ga_comm_max [rule_format] : "ALL x. ALL y. max'(x, y) = max'(y, x)"

ga_assoc_min [rule_format] :
"ALL x. ALL y. ALL z. min'(min'(x, y), z) = min'(x, min'(y, z))"

ga_assoc_max [rule_format] :
"ALL x. ALL y. ALL z. max'(max'(x, y), z) = max'(x, max'(y, z))"

ga_left_comm_min [rule_format] :
"ALL x. ALL y. ALL z. min'(x, min'(y, z)) = min'(y, min'(x, z))"

ga_left_comm_max [rule_format] :
"ALL x. ALL y. ALL z. max'(x, max'(y, z)) = max'(y, max'(x, z))"

min_def_ExtTotalOrder [rule_format] :
"ALL x. ALL y. min'(x, y) = (if x <=' y then x else y)"

max_def_ExtTotalOrder [rule_format] :
"ALL x. ALL y. max'(x, y) = (if x <=' y then y else x)"

min_inf_relation [rule_format] :
"ALL x. ALL y. makePartial (min'(x, y)) = inf'(x, y)"

max_sup_relation [rule_format] :
"ALL x. ALL y. makePartial (max'(x, y)) = sup(x, y)"

RealNonNeg_pred_def [rule_format] :
"ALL x. RealNonNeg_pred(x) = (x >=' 0')"

RealPos_pred_def [rule_format] :
"ALL x. RealPos_pred(x) = (x >' 0')"

Ax3 [rule_format] :
"ALL x. defOp (gn_proj(x)) = RealNonNeg_pred(x)"

Ax4 [rule_format] : "ALL x. defOp (gn_proj(x)) = RealPos_pred(x)"

RealNonNeg_subtype [rule_format] :
"isSubtypeWithPred(X_RealNonNeg_pred, X_RealNonNeg_inj,
 X_RealNonNeg_proj)"

RealPos_subtype [rule_format] :
"isSubtypeWithPred(X_RealPos_pred, X_RealPos_inj, X_RealPos_proj)"

abs_def [rule_format] :
"ALL x.
 makePartial (abs'(x)) =
 (if 0' <=' x then gn_proj(x) else gn_proj(-' x))"

ga_assoc___Xx___3 [rule_format] :
"ALL x. ALL y. ALL z. (x +'' y) +'' z = x +'' (y +'' z)"

ga_right_unit___Xx___3 [rule_format] : "ALL x. x +'' 0'' = x"

ga_left_unit___Xx___3 [rule_format] : "ALL x. 0'' +'' x = x"

inv_Group_3 [rule_format] : "ALL x. -'' x +'' x = 0''"

rinv_Group_2 [rule_format] : "ALL x. x +'' -'' x = 0''"

ga_comm___Xx___3 [rule_format] : "ALL x. ALL y. x +'' y = y +'' x"

binary_inverse_1 [rule_format] :
"ALL x. ALL y. x -'' y = x +'' -'' y"

unit [rule_format] : "ALL x. gn_inj(1') *_3 x = x"

mix_assoc [rule_format] :
"ALL r. ALL s. ALL x. (r *'' s) *_3 x = r *_3 (s *_3 x)"

distr_Field [rule_format] :
"ALL r. ALL s. ALL x. (r +' s) *_3 x = (r *_3 x) +'' (s *_3 x)"

distr_Space [rule_format] :
"ALL r. ALL x. ALL y. r *_3 (x +'' y) = (r *_3 x) +'' (r *_3 y)"

zero_by_left_zero [rule_format] : "ALL x. 0' *_3 x = 0''"

zero_by_right_zero [rule_format] : "ALL r. r *_3 0'' = 0''"

inverse_by_XMinus1 [rule_format] :
"ALL x. -' gn_inj(1') *_3 x = -'' x"

distributive [rule_format] :
"ALL v. ALL v'. ALL w. (v +'' v') *_4 w = (v *_4 w) +' (v' *_4 w)"

homogeneous [rule_format] :
"ALL a. ALL v. ALL w. (a *_3 v) *_4 w = a *'' (v *_4 w)"

symmetric [rule_format] : "ALL v. ALL w. v *_4 w = w *_4 v"

pos_definite [rule_format] : "ALL v. ~ v = 0'' --> v *_4 v >' 0'"

declare ga_assoc___Xx__ [simp]
declare ga_right_unit___Xx__ [simp]
declare ga_left_unit___Xx__ [simp]
declare inv_Group_2 [simp]
declare rinv_Group [simp]
declare ga_comm___Xx__ [simp]
declare ga_assoc___Xx___1 [simp]
declare ga_right_unit___Xx___1 [simp]
declare ga_left_unit___Xx___1 [simp]
declare ga_comm___Xx___1 [simp]
declare ga_assoc___Xx___2 [simp]
declare ga_right_unit___Xx___2 [simp]
declare ga_left_unit___Xx___2 [simp]
declare inv_Group_1 [simp]
declare rinv_Group_1 [simp]
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
declare Ax3 [simp]
declare Ax4 [simp]
declare RealNonNeg_subtype [simp]
declare RealPos_subtype [simp]
declare ga_assoc___Xx___3 [simp]
declare ga_right_unit___Xx___3 [simp]
declare ga_left_unit___Xx___3 [simp]
declare inv_Group_3 [simp]
declare rinv_Group_2 [simp]
declare ga_comm___Xx___3 [simp]
declare unit [simp]
declare zero_by_left_zero [simp]
declare zero_by_right_zero [simp]
declare inverse_by_XMinus1 [simp]

theorem right_distributive :
"ALL v. ALL v'. ALL w. w *_4 (v +'' v') = (w *_4 v) +' (w *_4 v')"
using subtype_def subtype_pred_def Ax1_1 inf_def
      RealNonNeg_pred_def RealPos_pred_def abs_def
by (auto)

ML "Header.record \"right_distributive\""

theorem right_homogeneous :
"ALL a. ALL v. ALL w. v *_4 (a *_3 w) = a *'' (v *_4 w)"
using subtype_def subtype_pred_def Ax1_1 inf_def
      RealNonNeg_pred_def RealPos_pred_def abs_def
by (auto)

ML "Header.record \"right_homogeneous\""

theorem non_degenerate : "ALL v. v *_4 v = 0' --> v = 0''"
using subtype_def subtype_pred_def Ax1_1 inf_def
      RealNonNeg_pred_def RealPos_pred_def abs_def
by (auto)

ML "Header.record \"non_degenerate\""

end
