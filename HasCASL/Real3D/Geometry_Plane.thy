theory Geometry_Plane
imports "$HETS_LIB/Isabelle/MainHCPairs"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"subtype_def\", \"subtype_pred_def\", \"ga_assoc___Xx__\",
     \"ga_right_unit___Xx__\", \"ga_left_unit___Xx__\", \"inv_Group\",
     \"rinv_Group\", \"ga_comm___Xx__\", \"ga_assoc___Xx___1\",
     \"ga_right_unit___Xx___1\", \"ga_left_unit___Xx___1\",
     \"distr1_Ring\", \"distr2_Ring\", \"left_zero\", \"right_zero\",
     \"ga_comm___Xx___1\", \"noZeroDiv\", \"zeroNeqOne\", \"Ax1\",
     \"ga_assoc___Xx___2\", \"ga_right_unit___Xx___2\",
     \"ga_left_unit___Xx___2\", \"inv_Group_1\", \"rinv_Group_1\",
     \"binary_inverse\", \"Ax1_1\", \"refl\", \"trans\", \"antisym\",
     \"dichotomy_TotalOrder\", \"FWO_plus_left\", \"FWO_times_left\",
     \"FWO_plus_right\", \"FWO_times_right\", \"FWO_plus\", \"inf_def\",
     \"Real_completeness\", \"geq_def_ExtPartialOrder\",
     \"less_def_ExtPartialOrder\", \"greater_def_ExtPartialOrder\",
     \"ga_comm_inf\", \"ga_comm_sup\", \"inf_def_ExtPartialOrder\",
     \"sup_def_ExtPartialOrder\", \"ga_comm_min\", \"ga_comm_max\",
     \"ga_assoc_min\", \"ga_assoc_max\", \"ga_left_comm_min\",
     \"ga_left_comm_max\", \"min_def_ExtTotalOrder\",
     \"max_def_ExtTotalOrder\", \"min_inf_relation\",
     \"max_sup_relation\", \"RealNonNeg_pred_def\",
     \"RealPos_pred_def\", \"Ax3\", \"Ax4\", \"RealNonNeg_subtype\",
     \"RealPos_subtype\", \"abs_def\",
     \"times_cancel_right_nonneg_leq\", \"times_leq_nonneg_cond\",
     \"sqr_def\", \"sqrt_def\", \"Pos_def\", \"X2_def_Real\",
     \"X3_def_Real\", \"X4_def_Real\", \"X5_def_Real\", \"X6_def_Real\",
     \"X7_def_Real\", \"X8_def_Real\", \"X9_def_Real\",
     \"ZeroToNine_type\", \"decimal_def\", \"ga_select_C1\",
     \"ga_select_C2\", \"ga_select_C3\", \"Zero_Point\",
     \"Point_choice\", \"ga_select_C1_1\", \"ga_select_C2_1\",
     \"ga_select_C3_1\", \"Zero_Vector\", \"VectorStar_pred_def\",
     \"Ax7\", \"VectorStar_subtype\", \"def_of_vector_addition\",
     \"def_of_minus_vector\", \"binary_inverse_1_1\",
     \"scalar_multiplication\", \"scalar_product\", \"vector_product\",
     \"ONB1\", \"ONB2\", \"ONB3\", \"cross_left_homogenity\",
     \"cross_product_antisymmetric\", \"ga_assoc___Xx___3_1\",
     \"ga_right_unit___Xx___3_1\", \"ga_left_unit___Xx___3_1\",
     \"inv_Group_2_1\", \"rinv_Group_2_1\", \"ga_comm___Xx___3\",
     \"unit\", \"mix_assoc\", \"distr_Field\", \"distr_Space\",
     \"zero_by_left_zero\", \"zero_by_right_zero\",
     \"inverse_by_XMinus1\", \"distributive\", \"homogeneous\",
     \"symmetric\", \"pos_definite\", \"right_distributive\",
     \"right_homogeneous\", \"non_degenerate\", \"lindep_def\",
     \"lindep_reflexivity\", \"lindep_symmetry\",
     \"simple_lindep_condition\", \"lindep_nonlindep_transitivity\",
     \"norm_from_inner_prod_def\", \"proj_def\", \"orthcomp_def\",
     \"orthogonal_def\", \"orth_symmetric\", \"lindep_orth_transitive\",
     \"orthogonal_existence_theorem\",
     \"orthogonal_on_zero_projection\",
     \"orthogonal_projection_theorem\",
     \"orthogonal_decomposition_theorem\",
     \"unique_orthogonal_decomposition\", \"cross_product_orthogonal\",
     \"cross_product_zero_iff_lindep\", \"e1e2_nonlindep\",
     \"point_vector_map\", \"plus_injective\", \"plus_surjective\",
     \"point_vector_plus_associative\", \"vec_def\",
     \"transitivity_of_vec_plus\", \"plus_vec_identity\",
     \"set_comprehension\", \"abbrev_of_set_comprehension\",
     \"function_image\", \"emptySet_empty\", \"allSet_contains_all\",
     \"def_of_isIn\", \"def_of_subset\", \"def_of_union\",
     \"def_of_bigunion\", \"def_of_intersection\",
     \"def_of_difference\", \"def_of_disjoint\", \"def_of_productset\",
     \"emptySet_union_right_unit\", \"function_image_structure\",
     \"def_of_interval\", \"abbrev_of_interval\",
     \"plus_PointSet_Vector\", \"plus_Point_VectorSet\",
     \"plus_PointSet_VectorSet\", \"def_of_Plane\",
     \"plane_condition_for_2_points\",
     \"plane_condition_for_point_and_vector\"]"

typedecl NonZero
typedecl PointSet
typedecl Real
typedecl RealNonNeg
typedecl RealPos
typedecl RealSet
typedecl ('a1) Set
typedecl VectorSet
typedecl VectorStar
typedecl ZeroToNine

datatype Point = X_P "Real" "Real" "Real" ("P/'(_,/ _,/ _')" [3,3,3] 999)
datatype Vector = X_V "Real" "Real" "Real" ("V/'(_,/ _,/ _')" [3,3,3] 999)

consts
C1X1 :: "Point => Real" ("C1''/'(_')" [3] 999)
C1X2 :: "Vector => Real" ("C1''''/'(_')" [3] 999)
C2X1 :: "Point => Real" ("C2''/'(_')" [3] 999)
C2X2 :: "Vector => Real" ("C2''''/'(_')" [3] 999)
C3X1 :: "Point => Real" ("C3''/'(_')" [3] 999)
C3X2 :: "Vector => Real" ("C3''''/'(_')" [3] 999)
Plane :: "Point * VectorStar => Point => bool"
X0X1 :: "Point" ("0''")
X0X2 :: "Real" ("0''''")
X0X3 :: "Vector" ("0'_3")
X1X1 :: "NonZero" ("1''")
X1X2 :: "Real" ("1''''")
X2 :: "Real" ("2''")
X3 :: "Real" ("3''")
X4 :: "Real" ("4''")
X5 :: "Real" ("5''")
X6 :: "Real" ("6''")
X7 :: "Real" ("7''")
X8 :: "Real" ("8''")
X9 :: "Real" ("9''")
XLBrace__XRBrace :: "('S => bool) => 'S => bool"
XMinus__XX1 :: "Real => Real" ("(-''/ _)" [56] 56)
XMinus__XX2 :: "Vector => Vector" ("(-''''/ _)" [56] 56)
XOSqBr__XPeriodXPeriodXPeriod__XCSqBr :: "Real * Real => Real => bool"
XVBarXVBar__XVBarXVBar :: "Vector => Real" ("(||/ _/ ||)" [10] 999)
X_Pos :: "Real => bool" ("Pos/'(_')" [3] 999)
X_RealNonNeg_inj :: "RealNonNeg => Real" ("RealNonNeg'_inj/'(_')" [3] 999)
X_RealNonNeg_pred :: "Real => bool" ("RealNonNeg'_pred/'(_')" [3] 999)
X_RealNonNeg_proj :: "Real => RealNonNeg" ("RealNonNeg'_proj/'(_')" [3] 999)
X_RealPos_inj :: "RealPos => Real" ("RealPos'_inj/'(_')" [3] 999)
X_RealPos_pred :: "Real => bool" ("RealPos'_pred/'(_')" [3] 999)
X_RealPos_proj :: "Real => RealPos" ("RealPos'_proj/'(_')" [3] 999)
X_VectorStar_inj :: "VectorStar => Vector" ("VectorStar'_inj/'(_')" [3] 999)
X_VectorStar_pred :: "Vector => bool" ("VectorStar'_pred/'(_')" [3] 999)
X_VectorStar_proj :: "Vector => VectorStar" ("VectorStar'_proj/'(_')" [3] 999)
X__XAtXAt__X :: "ZeroToNine => Real => Real" ("(_/ @@/ _)" [54,54] 52)
X__XBslashXBslash__X :: "('S => bool) * ('S => bool) => 'S => bool"
X__XGtXEq__X :: "Real => Real => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XGt__X :: "Real => Real => bool" ("(_/ >''/ _)" [44,44] 42)
X__XHash__X :: "Vector => Vector => Vector" ("(_/ #''/ _)" [54,54] 52)
X__XLtXEq__X :: "Real => Real => bool" ("(_/ <=''/ _)" [44,44] 42)
X__XLt__X :: "Real => Real => bool" ("(_/ <''/ _)" [44,44] 42)
X__XMinus__XX1 :: "Real => Real => Real" ("(_/ -''/ _)" [54,54] 52)
X__XMinus__XX2 :: "Vector => Vector => Vector" ("(_/ -''''/ _)" [54,54] 52)
X__XPlus__XX1 :: "Point => Vector => Point" ("(_/ +''/ _)" [54,54] 52)
X__XPlus__XX2 :: "Point * (Vector => bool) => Point => bool"
X__XPlus__XX3 :: "Real => Real => Real" ("(_/ +'_3/ _)" [54,54] 52)
X__XPlus__XX4 :: "Vector => Vector => Vector" ("(_/ +'_4/ _)" [54,54] 52)
X__XPlus__XX5 :: "(Point => bool) * Vector => Point => bool"
X__XPlus__XX6 :: "(Point => bool) * (Vector => bool) => Point => bool"
X__XSlash__X :: "Real => NonZero => Real" ("(_/ '/''/ _)" [54,54] 52)
X__Xx__XX1 :: "NonZero => NonZero => NonZero" ("(_/ *''/ _)" [54,54] 52)
X__Xx__XX2 :: "Real => Real => Real" ("(_/ *''''/ _)" [54,54] 52)
X__Xx__XX3 :: "Real => Vector => Vector" ("(_/ *'_3/ _)" [54,54] 52)
X__Xx__XX4 :: "Vector => Vector => Real" ("(_/ *'_4/ _)" [54,54] 52)
X__Xx__XX5 :: "('S => bool) * ('T => bool) => 'S * 'T => bool"
X__disjoint__X :: "('S => bool) => ('S => bool) => bool" ("(_/ disjoint/ _)" [44,44] 42)
X__intersection__X :: "('S => bool) * ('S => bool) => 'S => bool"
X__isIn__X :: "'S => ('S => bool) => bool" ("(_/ isIn/ _)" [44,44] 42)
X__subset__X :: "('S => bool) => ('S => bool) => bool" ("(_/ subset/ _)" [44,44] 42)
X__union__X :: "('S => bool) * ('S => bool) => 'S => bool"
X_abs :: "Real => RealNonNeg" ("abs''/'(_')" [3] 999)
X_allSet :: "'S => bool" ("allSet/'(_')" [3] 999)
X_choose :: "(Point => bool) => Point" ("choose''/'(_')" [3] 999)
X_emptySet :: "'S => bool" ("emptySet/'(_')" [3] 999)
X_gn_inj :: "'a => 'b" ("gn'_inj/'(_')" [3] 999)
X_gn_proj :: "'a => 'b partial" ("gn'_proj/'(_')" [3] 999)
X_image :: "('S => 'T) * ('S => bool) => 'T => bool"
X_inv :: "NonZero => NonZero" ("inv''/'(_')" [3] 999)
X_isSubtype :: "('s => 't) => ('t => 's) => bool" ("isSubtype/'(_,/ _')" [3,3] 999)
X_isSubtypeWithPred :: "('t => bool) => ('s => 't) => ('t => 's) => bool" ("isSubtypeWithPred/'(_,/ _,/ _')" [3,3,3] 999)
X_lindep :: "Vector => Vector => bool" ("lindep/'(_,/ _')" [3,3] 999)
X_max :: "Real => Real => Real" ("max''/'(_,/ _')" [3,3] 999)
X_min :: "Real => Real => Real" ("min''/'(_,/ _')" [3,3] 999)
X_orth :: "Vector => Vector => bool" ("orth/'(_,/ _')" [3,3] 999)
X_orthcomp :: "Vector => Vector => Vector" ("orthcomp/'(_,/ _')" [3,3] 999)
X_proj :: "Vector => Vector => Vector" ("proj/'(_,/ _')" [3,3] 999)
X_sqr :: "Real => RealNonNeg" ("sqr/'(_')" [3] 999)
X_sqrt :: "RealNonNeg => RealNonNeg" ("sqrt/'(_')" [3] 999)
X_sup :: "Real => Real => Real partial" ("sup/'(_,/ _')" [3,3] 999)
X_vec :: "Point => Point => Vector" ("vec/'(_,/ _')" [3,3] 999)
bigunion :: "(('S => bool) => bool) => 'S => bool"
closedinterval :: "Real * Real => Real => bool"
e1 :: "Vector"
e2 :: "Vector"
e3 :: "Vector"
infX1 :: "Real => Real => Real partial" ("inf''/'(_,/ _')" [3,3] 999)
infX2 :: "(Real => bool) => Real partial" ("inf''''/'(_')" [3] 999)
setFromProperty :: "('S => bool) => 'S => bool"

axioms
subtype_def [rule_format] :
"ALL injection.
 ALL projection.
 isSubtype(injection, projection) =
 (ALL x. x = projection (injection x))"

subtype_pred_def [rule_format] :
"ALL X_P.
 ALL injection.
 ALL projection.
 isSubtypeWithPred(X_P, injection, projection) =
 ((isSubtype(injection, projection) &
   (ALL x. X_P x --> x = injection (projection x))) &
  (ALL x. X_P (injection x)))"

ga_assoc___Xx__ [rule_format] :
"ALL x. ALL y. ALL z. (x +_3 y) +_3 z = x +_3 (y +_3 z)"

ga_right_unit___Xx__ [rule_format] : "ALL x. x +_3 0'' = x"

ga_left_unit___Xx__ [rule_format] : "ALL x. 0'' +_3 x = x"

inv_Group [rule_format] : "ALL x. -' x +_3 x = 0''"

rinv_Group [rule_format] : "ALL x. x +_3 -' x = 0''"

ga_comm___Xx__ [rule_format] : "ALL x. ALL y. x +_3 y = y +_3 x"

ga_assoc___Xx___1 [rule_format] :
"ALL x. ALL y. ALL z. (x *'' y) *'' z = x *'' (y *'' z)"

ga_right_unit___Xx___1 [rule_format] : "ALL x. x *'' 1'' = x"

ga_left_unit___Xx___1 [rule_format] : "ALL x. 1'' *'' x = x"

distr1_Ring [rule_format] :
"ALL x. ALL y. ALL z. (x +_3 y) *'' z = (x *'' z) +_3 (y *'' z)"

distr2_Ring [rule_format] :
"ALL x. ALL y. ALL z. z *'' (x +_3 y) = (z *'' x) +_3 (z *'' y)"

left_zero [rule_format] : "ALL x. 0'' *'' x = 0''"

right_zero [rule_format] : "ALL x. x *'' 0'' = 0''"

ga_comm___Xx___1 [rule_format] : "ALL x. ALL y. x *'' y = y *'' x"

noZeroDiv [rule_format] :
"ALL x. ALL y. x *'' y = 0'' --> x = 0'' | y = 0''"

zeroNeqOne [rule_format] : "~ 1'' = 0''"

Ax1 [rule_format] : "ALL x. defOp (gn_proj(x)) = (~ x = 0'')"

ga_assoc___Xx___2 [rule_format] :
"ALL x. ALL y. ALL z. (x *' y) *' z = x *' (y *' z)"

ga_right_unit___Xx___2 [rule_format] : "ALL x. x *' 1' = x"

ga_left_unit___Xx___2 [rule_format] : "ALL x. 1' *' x = x"

inv_Group_1 [rule_format] : "ALL x. inv'(x) *' x = 1'"

rinv_Group_1 [rule_format] : "ALL x. x *' inv'(x) = 1'"

binary_inverse [rule_format] : "ALL x. ALL y. x -' y = x +_3 -' y"

Ax1_1 [rule_format] :
"ALL x. ALL y. x /' y = x *'' gn_inj(inv'(y))"

refl [rule_format] : "ALL x. x <=' x"

trans [rule_format] :
"ALL x. ALL y. ALL z. x <=' y & y <=' z --> x <=' z"

antisym [rule_format] : "ALL x. ALL y. x <=' y & y <=' x --> x = y"

dichotomy_TotalOrder [rule_format] :
"ALL x. ALL y. x <=' y | y <=' x"

FWO_plus_left [rule_format] :
"ALL a. ALL b. ALL c. a <=' b --> a +_3 c <=' b +_3 c"

FWO_times_left [rule_format] :
"ALL a. ALL b. ALL c. a <=' b & 0'' <=' c --> a *'' c <=' b *'' c"

FWO_plus_right [rule_format] :
"ALL a. ALL b. ALL c. b <=' c --> a +_3 b <=' a +_3 c"

FWO_times_right [rule_format] :
"ALL a. ALL b. ALL c. b <=' c & 0'' <=' a --> a *'' b <=' a *'' c"

FWO_plus [rule_format] :
"ALL a.
 ALL b. ALL c. ALL d. a <=' c & b <=' d --> a +_3 b <=' c +_3 d"

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
"ALL x. RealNonNeg_pred(x) = (x >=' 0'')"

RealPos_pred_def [rule_format] :
"ALL x. RealPos_pred(x) = (x >' 0'')"

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
 (if 0'' <=' x then gn_proj(x) else gn_proj(-' x))"

times_cancel_right_nonneg_leq [rule_format] :
"ALL a. ALL b. ALL c. a *'' b <=' c *'' b & b >=' 0'' --> a <=' c"

times_leq_nonneg_cond [rule_format] :
"ALL a. ALL b. 0'' <=' a *'' b & b >=' 0'' --> 0'' <=' a"

sqr_def [rule_format] :
"ALL r. gn_inj(sqr(r)) = makePartial (r *'' r)"

sqrt_def [rule_format] : "ALL q. sqr(gn_inj(sqrt(q))) = q"

Pos_def [rule_format] : "ALL x. Pos(x) = (0'' <=' x)"

X2_def_Real [rule_format] : "2' = gn_inj(1') +_3 gn_inj(1')"

X3_def_Real [rule_format] : "3' = 2' +_3 gn_inj(1')"

X4_def_Real [rule_format] : "4' = 3' +_3 gn_inj(1')"

X5_def_Real [rule_format] : "5' = 4' +_3 gn_inj(1')"

X6_def_Real [rule_format] : "6' = 5' +_3 gn_inj(1')"

X7_def_Real [rule_format] : "7' = 6' +_3 gn_inj(1')"

X8_def_Real [rule_format] : "8' = 7' +_3 gn_inj(1')"

X9_def_Real [rule_format] : "9' = 8' +_3 gn_inj(1')"

ZeroToNine_type [rule_format] :
"ALL x.
 defOp (gn_proj(x)) =
 (((((((((x = 0'' | makePartial x = gn_inj(1')) | x = 2') |
        x = 3') |
       x = 4') |
      x = 5') |
     x = 6') |
    x = 7') |
   x = 8') |
  x = 9')"

decimal_def [rule_format] :
"ALL m.
 ALL X_n. m @@ X_n = (gn_inj(m) *'' (9' +_3 gn_inj(1'))) +_3 X_n"

ga_select_C1 [rule_format] :
"ALL x_1. ALL x_2. ALL x_3. C1'(P(x_1, x_2, x_3)) = x_1"

ga_select_C2 [rule_format] :
"ALL x_1. ALL x_2. ALL x_3. C2'(P(x_1, x_2, x_3)) = x_2"

ga_select_C3 [rule_format] :
"ALL x_1. ALL x_2. ALL x_3. C3'(P(x_1, x_2, x_3)) = x_3"

Zero_Point [rule_format] : "0' = P(0'', 0'', 0'')"

Point_choice [rule_format] :
"ALL X_P. (EX y. X_P y) --> X_P (choose'(X_P))"

ga_select_C1_1 [rule_format] :
"ALL x_1. ALL x_2. ALL x_3. C1''(V(x_1, x_2, x_3)) = x_1"

ga_select_C2_1 [rule_format] :
"ALL x_1. ALL x_2. ALL x_3. C2''(V(x_1, x_2, x_3)) = x_2"

ga_select_C3_1 [rule_format] :
"ALL x_1. ALL x_2. ALL x_3. C3''(V(x_1, x_2, x_3)) = x_3"

Zero_Vector [rule_format] : "0_3 = V(0'', 0'', 0'')"

VectorStar_pred_def [rule_format] :
"ALL x. VectorStar_pred(x) = (~ x = 0_3)"

Ax7 [rule_format] :
"ALL x. defOp (gn_proj(x)) = VectorStar_pred(x)"

VectorStar_subtype [rule_format] :
"isSubtypeWithPred(X_VectorStar_pred, X_VectorStar_inj,
 X_VectorStar_proj)"

def_of_vector_addition [rule_format] :
"ALL x.
 ALL y.
 x +_4 y =
 V(C1''(x) +_3 C1''(y), C2''(x) +_3 C2''(y), C3''(x) +_3 C3''(y))"

def_of_minus_vector [rule_format] :
"ALL x. -'' x = V(-' C1''(x), -' C2''(x), -' C3''(x))"

binary_inverse_1_1 [rule_format] :
"ALL x. ALL y. x -'' y = x +_4 -'' y"

scalar_multiplication [rule_format] :
"ALL x.
 ALL y. x *_3 y = V(x *'' C1''(y), x *'' C2''(y), x *'' C3''(y))"

scalar_product [rule_format] :
"ALL x.
 ALL y.
 x *_4 y =
 ((C1''(x) *'' C1''(y)) +_3 (C2''(x) *'' C2''(y))) +_3
 (C3''(x) *'' C3''(y))"

vector_product [rule_format] :
"ALL x.
 ALL y.
 x #' y =
 V((C2''(x) *'' C3''(y)) -' (C2''(y) *'' C3''(x)),
 (C3''(x) *'' C1''(y)) -' (C3''(y) *'' C1''(x)),
 (C1''(x) *'' C2''(y)) -' (C1''(y) *'' C2''(x)))"

ONB1 [rule_format] : "e1 = V(gn_inj(1'), 0'', 0'')"

ONB2 [rule_format] : "e2 = V(0'', gn_inj(1'), 0'')"

ONB3 [rule_format] : "e3 = V(0'', 0'', gn_inj(1'))"

cross_left_homogenity [rule_format] :
"ALL r. ALL x. ALL y. r *_3 (x #' y) = (r *_3 x) #' y"

cross_product_antisymmetric [rule_format] :
"ALL x. ALL y. x #' y = -'' (y #' x)"

ga_assoc___Xx___3_1 [rule_format] :
"ALL x. ALL y. ALL z. (x +_4 y) +_4 z = x +_4 (y +_4 z)"

ga_right_unit___Xx___3_1 [rule_format] : "ALL x. x +_4 0_3 = x"

ga_left_unit___Xx___3_1 [rule_format] : "ALL x. 0_3 +_4 x = x"

inv_Group_2_1 [rule_format] : "ALL x. -'' x +_4 x = 0_3"

rinv_Group_2_1 [rule_format] : "ALL x. x +_4 -'' x = 0_3"

ga_comm___Xx___3 [rule_format] : "ALL x. ALL y. x +_4 y = y +_4 x"

unit [rule_format] : "ALL x. gn_inj(1') *_3 x = x"

mix_assoc [rule_format] :
"ALL r. ALL s. ALL x. (r *'' s) *_3 x = r *_3 (s *_3 x)"

distr_Field [rule_format] :
"ALL r. ALL s. ALL x. (r +_3 s) *_3 x = (r *_3 x) +_4 (s *_3 x)"

distr_Space [rule_format] :
"ALL r. ALL x. ALL y. r *_3 (x +_4 y) = (r *_3 x) +_4 (r *_3 y)"

zero_by_left_zero [rule_format] : "ALL x. 0'' *_3 x = 0_3"

zero_by_right_zero [rule_format] : "ALL r. r *_3 0_3 = 0_3"

inverse_by_XMinus1 [rule_format] :
"ALL x. -' gn_inj(1') *_3 x = -'' x"

distributive [rule_format] :
"ALL v. ALL v'. ALL w. (v +_4 v') *_4 w = (v *_4 w) +_3 (v' *_4 w)"

homogeneous [rule_format] :
"ALL a. ALL v. ALL w. (a *_3 v) *_4 w = a *'' (v *_4 w)"

symmetric [rule_format] : "ALL v. ALL w. v *_4 w = w *_4 v"

pos_definite [rule_format] : "ALL v. ~ v = 0_3 --> v *_4 v >' 0''"

right_distributive [rule_format] :
"ALL v. ALL v'. ALL w. w *_4 (v +_4 v') = (w *_4 v) +_3 (w *_4 v')"

right_homogeneous [rule_format] :
"ALL a. ALL v. ALL w. v *_4 (a *_3 w) = a *'' (v *_4 w)"

non_degenerate [rule_format] : "ALL v. v *_4 v = 0'' --> v = 0_3"

lindep_def [rule_format] :
"ALL x. ALL y. lindep(x, y) = (y = 0_3 | (EX r. x = r *_3 y))"

lindep_reflexivity [rule_format] : "ALL x. lindep(x, x)"

lindep_symmetry [rule_format] :
"ALL x. ALL y. lindep(x, y) --> lindep(y, x)"

simple_lindep_condition [rule_format] :
"ALL r. ALL x. ALL y. x = r *_3 y --> lindep(x, y)"

lindep_nonlindep_transitivity [rule_format] :
"ALL x.
 ALL y.
 ALL z.
 (~ x = 0_3 & lindep(x, y)) & ~ lindep(y, z) --> ~ lindep(x, z)"

norm_from_inner_prod_def [rule_format] :
"ALL x.
 makePartial ( || x || ) =
 restrictOp (gn_proj(sqrt(makeTotal (gn_proj(x *_4 x)))))
 (defOp (gn_proj(x *_4 x)))"

proj_def [rule_format] :
"ALL v.
 ALL w.
 makePartial (proj(v, w)) =
 (if w = 0_3 then makePartial 0_3
     else restrictOp
          (makePartial (((v *_4 w) /' makeTotal (gn_proj(w *_4 w))) *_3 w))
          (defOp (gn_proj(w *_4 w))))"

orthcomp_def [rule_format] :
"ALL v. ALL w. orthcomp(v, w) = v -'' proj(v, w)"

orthogonal_def [rule_format] :
"ALL x. ALL y. orth(x, y) = (x *_4 y = 0'')"

orth_symmetric [rule_format] :
"ALL x. ALL y. orth(x, y) --> orth(y, x)"

lindep_orth_transitive [rule_format] :
"ALL x. ALL y. ALL z. lindep(x, y) & orth(y, z) --> orth(x, z)"

orthogonal_existence_theorem [rule_format] :
"ALL x.
 (EX a. EX b. ~ lindep(a, b)) --> (EX c. ~ c = 0_3 & orth(c, x))"

orthogonal_on_zero_projection [rule_format] :
"ALL x. ALL y. proj(x, y) = 0_3 --> orth(x, y)"

orthogonal_projection_theorem [rule_format] :
"ALL x. ALL y. orth(orthcomp(x, y), y)"

orthogonal_decomposition_theorem [rule_format] :
"ALL x. ALL y. proj(x, y) +_4 orthcomp(x, y) = x"

unique_orthogonal_decomposition [rule_format] :
"ALL v.
 ALL w.
 ALL x.
 ALL y.
 ALL z.
 ((((~ z = 0_3 & x +_4 y = v +_4 w) & lindep(x, z)) &
   lindep(v, z)) &
  orth(z, y)) &
 orth(z, w) -->
 x = v & y = w"

cross_product_orthogonal [rule_format] :
"ALL x. ALL y. orth(x, x #' y)"

cross_product_zero_iff_lindep [rule_format] :
"ALL x. ALL y. lindep(x, y) = (x #' y = 0_3)"

e1e2_nonlindep [rule_format] : "~ lindep(e1, e2)"

point_vector_map [rule_format] :
"ALL p.
 ALL v.
 p +' v =
 P(C1'(p) +_3 C1''(v), C2'(p) +_3 C2''(v), C3'(p) +_3 C3''(v))"

plus_injective [rule_format] :
"ALL p. ALL v. ALL w. p +' v = p +' w --> v = w"

plus_surjective [rule_format] : "ALL p. ALL q. EX y. p +' y = q"

point_vector_plus_associative [rule_format] :
"ALL p. ALL v. ALL w. p +' (v +_4 w) = (p +' v) +' w"

vec_def [rule_format] : "ALL p. ALL q. p +' vec(p, q) = q"

transitivity_of_vec_plus [rule_format] :
"ALL p. ALL q. ALL r. vec(p, q) +_4 vec(q, r) = vec(p, r)"

plus_vec_identity [rule_format] :
"ALL p. ALL q. ALL v. p +' v = q --> v = vec(p, q)"

set_comprehension [rule_format] : "ALL s. XLBrace__XRBrace s = s"

abbrev_of_set_comprehension [rule_format] :
"setFromProperty = XLBrace__XRBrace"

function_image [rule_format] :
"ALL XX. ALL f. X_image (f, XX) = (% x. EX y. y isIn XX & f y = x)"

emptySet_empty [rule_format] : "ALL x. ~ x isIn X_emptySet"

allSet_contains_all [rule_format] : "ALL x. x isIn X_allSet"

def_of_isIn [rule_format] : "ALL s. ALL x. (x isIn s) = s x"

def_of_subset [rule_format] :
"ALL s. ALL s'. (s subset s') = (ALL x. x isIn s --> x isIn s')"

def_of_union [rule_format] :
"ALL s.
 ALL s'.
 ALL x. (x isIn X__union__X (s, s')) = (x isIn s | x isIn s')"

def_of_bigunion [rule_format] :
"ALL XXXX.
 ALL x. (x isIn bigunion XXXX) = (EX XX. XX isIn XXXX & x isIn XX)"

def_of_intersection [rule_format] :
"ALL s.
 ALL s'.
 ALL x.
 (x isIn X__intersection__X (s, s')) = (x isIn s & x isIn s')"

def_of_difference [rule_format] :
"ALL s.
 ALL s'.
 ALL x.
 (x isIn X__XBslashXBslash__X (s, s')) = (x isIn s & ~ x isIn s')"

def_of_disjoint [rule_format] :
"ALL s.
 ALL s'.
 (s disjoint s') = (X__intersection__X (s, s') = X_emptySet)"

def_of_productset [rule_format] :
"ALL s.
 ALL t.
 ALL x.
 ALL y. ((x, y) isIn X__Xx__XX5 (s, t)) = (x isIn s & y isIn t)"

emptySet_union_right_unit [rule_format] :
"ALL a. X__union__X (a, X_emptySet) = a"

function_image_structure [rule_format] :
"ALL a.
 ALL f. ALL x. (x isIn X_image (f, a)) = (EX y. y isIn a & f y = x)"

def_of_interval [rule_format] :
"ALL a.
 ALL b.
 XOSqBr__XPeriodXPeriodXPeriod__XCSqBr (a, b) =
 (% r. r >=' a & r <=' b)"

abbrev_of_interval [rule_format] :
"closedinterval = XOSqBr__XPeriodXPeriodXPeriod__XCSqBr"

plus_PointSet_Vector [rule_format] :
"ALL X_P.
 ALL v. X__XPlus__XX5 (X_P, v) = X_image (% x. x +' v, X_P)"

plus_Point_VectorSet [rule_format] :
"ALL X_V.
 ALL p. X__XPlus__XX2 (p, X_V) = X_image (% x. p +' x, X_V)"

plus_PointSet_VectorSet [rule_format] :
"ALL X_P.
 ALL X_V.
 X__XPlus__XX6 (X_P, X_V) =
 bigunion (X_image (% x. X__XPlus__XX5 (X_P, x), X_V))"

def_of_Plane [rule_format] :
"ALL normal.
 ALL offset.
 Plane (offset, normal) =
 (% x. orth(vec(x, offset), gn_inj(normal)))"

declare ga_assoc___Xx__ [simp]
declare ga_right_unit___Xx__ [simp]
declare ga_left_unit___Xx__ [simp]
declare inv_Group [simp]
declare rinv_Group [simp]
declare ga_comm___Xx__ [simp]
declare ga_assoc___Xx___1 [simp]
declare ga_right_unit___Xx___1 [simp]
declare ga_left_unit___Xx___1 [simp]
declare left_zero [simp]
declare right_zero [simp]
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
declare sqrt_def [simp]
declare ga_select_C1 [simp]
declare ga_select_C2 [simp]
declare ga_select_C3 [simp]
declare ga_select_C1_1 [simp]
declare ga_select_C2_1 [simp]
declare ga_select_C3_1 [simp]
declare Ax7 [simp]
declare VectorStar_subtype [simp]
declare ga_assoc___Xx___3_1 [simp]
declare ga_right_unit___Xx___3_1 [simp]
declare ga_left_unit___Xx___3_1 [simp]
declare inv_Group_2_1 [simp]
declare rinv_Group_2_1 [simp]
declare ga_comm___Xx___3 [simp]
declare unit [simp]
declare zero_by_left_zero [simp]
declare zero_by_right_zero [simp]
declare inverse_by_XMinus1 [simp]
declare lindep_reflexivity [simp]
declare lindep_symmetry [simp]
declare orth_symmetric [simp]
declare orthogonal_on_zero_projection [simp]
declare orthogonal_projection_theorem [simp]
declare orthogonal_decomposition_theorem [simp]
declare cross_product_orthogonal [simp]
declare e1e2_nonlindep [simp]
declare vec_def [simp]
declare transitivity_of_vec_plus [simp]
declare emptySet_empty [simp]
declare allSet_contains_all [simp]
declare def_of_isIn [simp]
declare emptySet_union_right_unit [simp]

theorem plane_condition_for_2_points :
"ALL normal.
 ALL offset.
 ALL x.
 ALL y.
 let plane = Plane (offset, normal)
 in x isIn plane & y isIn plane --> orth(vec(x, y), gn_inj(normal))"
using subtype_def subtype_pred_def Ax1_1 inf_def
      RealNonNeg_pred_def RealPos_pred_def abs_def sqr_def sqrt_def
      Pos_def X2_def_Real X3_def_Real X4_def_Real X5_def_Real X6_def_Real
      X7_def_Real X8_def_Real X9_def_Real decimal_def Zero_Point
      Zero_Vector VectorStar_pred_def scalar_multiplication
      scalar_product vector_product ONB1 ONB2 ONB3 lindep_def
      norm_from_inner_prod_def proj_def orthcomp_def orthogonal_def
      point_vector_map vec_def set_comprehension
      abbrev_of_set_comprehension function_image def_of_interval
      abbrev_of_interval plus_PointSet_Vector plus_Point_VectorSet
      plus_PointSet_VectorSet def_of_Plane
by (auto)

ML "Header.record \"plane_condition_for_2_points\""

theorem plane_condition_for_point_and_vector :
"ALL normal.
 ALL offset.
 ALL v.
 ALL x.
 let plane = Plane (offset, normal)
 in x isIn plane & orth(v, gn_inj(normal)) --> x +' v isIn plane"
using subtype_def subtype_pred_def Ax1_1 inf_def
      RealNonNeg_pred_def RealPos_pred_def abs_def sqr_def sqrt_def
      Pos_def X2_def_Real X3_def_Real X4_def_Real X5_def_Real X6_def_Real
      X7_def_Real X8_def_Real X9_def_Real decimal_def Zero_Point
      Zero_Vector VectorStar_pred_def scalar_multiplication
      scalar_product vector_product ONB1 ONB2 ONB3 lindep_def
      norm_from_inner_prod_def proj_def orthcomp_def orthogonal_def
      point_vector_map vec_def set_comprehension
      abbrev_of_set_comprehension function_image def_of_interval
      abbrev_of_interval plus_PointSet_Vector plus_Point_VectorSet
      plus_PointSet_VectorSet def_of_Plane
by (auto)

ML "Header.record \"plane_condition_for_point_and_vector\""

end
