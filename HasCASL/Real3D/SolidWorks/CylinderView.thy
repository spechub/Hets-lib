theory SWCommonPatterns_SWCylByAE_IsCylinder_T
imports "$HETS_LIB/Isabelle/MainHCPairs"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"ga_assoc___Xx__\",
     \"ga_right_unit___Xx__\", \"ga_left_unit___Xx__\", \"inv_Group\",
     \"rinv_Group\", \"ga_comm___Xx__\", \"ga_assoc___Xx___1\",
     \"ga_right_unit___Xx___1\", \"ga_left_unit___Xx___1\",
     \"distr1_Ring\", \"distr2_Ring\", \"ga_comm___Xx___1\",
     \"noZeroDiv\", \"zeroNeqOne\", \"Ax1\", \"ga_assoc___Xx___2\",
     \"ga_right_unit___Xx___2\", \"ga_left_unit___Xx___2\",
     \"inv_Group_1\", \"rinv_Group_1\", \"binary_inverse\", \"Ax1_1\",
     \"refl\", \"trans\", \"antisym\", \"dichotomy_TotalOrder\",
     \"FWO_plus_left\", \"FWO_times_left\", \"FWO_plus_right\",
     \"FWO_times_right\", \"FWO_plus\", \"Ax1_2\",
     \"Real_completeness\", \"geq_def_ExtPartialOrder\",
     \"less_def_ExtPartialOrder\", \"greater_def_ExtPartialOrder\",
     \"ga_comm_inf\", \"ga_comm_sup\", \"inf_def_ExtPartialOrder\",
     \"sup_def_ExtPartialOrder\", \"ga_comm_min\", \"ga_comm_max\",
     \"ga_assoc_min\", \"ga_assoc_max\", \"ga_left_comm_min\",
     \"ga_left_comm_max\", \"min_def_ExtTotalOrder\",
     \"max_def_ExtTotalOrder\", \"min_inf_relation\",
     \"max_sup_relation\", \"RealNonNeg_pred_def\",
     \"RealPos_pred_def\", \"Ax3\", \"Ax4\",
     \"abs_def\", \"sqr_def\", \"sqrt_def\",
     \"Ax1_2_1\", \"X2_def_Real\", \"X3_def_Real\", \"X4_def_Real\",
     \"X5_def_Real\", \"X6_def_Real\", \"X7_def_Real\", \"X8_def_Real\",
     \"X9_def_Real\", \"ZeroToNine_type\", \"decimal_def\",
     \"ga_select_C1\", \"ga_select_C2\", \"ga_select_C3\",
     \"Zero_Point\", \"Point_choice\", \"ga_select_C1_1\",
     \"ga_select_C2_1\", \"ga_select_C3_1\", \"Zero_Vector\",
     \"VectorStar_pred_def\", \"Ax7_1_1\",
     \"def_of_vector_addition\", \"def_of_minus_vector\",
     \"binary_inverse_1_1\", \"scalar_multiplication\",
     \"scalar_product\", \"vector_product\", \"ONB1\", \"ONB2\",
     \"ONB3\", \"cross_left_homogenity\",
     \"cross_product_antisymmetric\", \"ga_assoc___Xx___3_1\",
     \"ga_right_unit___Xx___3_1\", \"ga_left_unit___Xx___3_1\",
     \"inv_Group_2_1\", \"rinv_Group_2_1\", \"ga_comm___Xx___3\",
     \"unit\", \"mix_assoc\", \"distr_Field\", \"distr_Space\",
     \"zero_by_left_zero\", \"zero_by_right_zero\", \"no_zero_divisor\",
     \"inverse_by_XMinus1\", \"distributive\", \"homogeneous\",
     \"symmetric\", \"pos_definite\", \"right_distributive\",
     \"right_homogeneous\", \"degenerate\", \"lindep_def\", \"lindep_reflexivity\",
     \"lindep_symmetry\", \"simple_lindep_condition\",
     \"lindep_nonlindep_transitivity\", \"sqr2_def\",
     \"norm_from_inner_prod_def\", \"proj_def\", \"orthcomp_def\",
     \"orthogonal_def\",\"homogeneous_1\", \"definite\", \"pos_definite_1\",
     \"pos_homogeneous\", \"orth_symmetric\", \"lindep_orth_transitive\",
     \"orthogonal_on_zero_projection\",
     \"orthogonal_projection_theorem\",
     \"orthogonal_decomposition_theorem\",
     \"unique_orthogonal_decomposition\", \"cross_product_orthogonal\",
     \"cross_product_zero_iff_lindep\", \"e1e2_nonlindep\",
     \"point_vector_map\", \"plus_injective\", \"plus_surjective\",
     \"point_vector_plus_associative\", \"vec_def\",
     \"transitivity_of_vec_plus\",
     \"plus_vec_identity\", \"set_comprehension\",
     \"abbrev_of_set_comprehension\", \"function_image\",
     \"emptySet_empty\", \"allSet_contains_all\", \"def_of_isIn\",
     \"def_of_subset\", \"def_of_union\", \"def_of_bigunion\",
     \"def_of_intersection\", \"def_of_difference\",
     \"def_of_disjoint\", \"def_of_productset\", \"def_of_interval\",
     \"abbrev_of_interval\", \"plus_PointSet_Vector\",
     \"plus_Point_VectorSet\", \"plus_PointSet_VectorSet\",
     \"def_of_Plane\", \"plane_condition_for_2_points\",
     \"plane_condition_for_point_and_vector\", \"ga_select_first\",
     \"ga_select_rest\", \"ga_select_SpacePoint\",
     \"ga_select_NormalVector\", \"ga_select_InnerCS\",
     \"ga_select_Center\", \"ga_select_Start\", \"ga_select_End\",
     \"ga_select_From\", \"ga_select_To\", \"ga_select_Points\",
     \"ga_select_Objects\", \"ga_select_Plane\", \"ga_select_Sketch\",
     \"ga_select_Depth\", \"E1_def\", \"E2_def\", \"E3_def\",
     \"VLine_constr\", \"VWithLength_constr\",
     \"VPlane_constr\", \"VPlane2_constr\", \"VConnected_constr\",
     \"VHalfSpace_constr\", \"VHalfSpace2_constr\", \"VBall_constr\",
     \"VCircle_constr\", \"ActAttach_constr\", \"ActExtrude_constr\",
     \"vwl_identity\", \"vwl_length\", \"vwl_lindep\",
     \"semantics_for_Planes\",
     \"semantics_for_SketchObject_listsXMinusBaseCase\",
     \"semantics_for_SketchObject_listsXMinusRecursiveCase\",
     \"semantics_for_Arcs\", \"semantics_for_Sketches\",
     \"semantics_for_ArcExtrusion\",
     \"plane_is_plane\", \"def_of_SWCylinder\",
     \"affine_cylinder_constructible_in_SW\", \"def_of_Cylinder\",
     \"left_zero\", \"right_zero\", \"emptySet_union_right_unit\",
     \"function_image_structure\", \"times_cancel_right_nonneg_leq\",
     \"times_leq_nonneg_cond\", \"orthogonal_existence_theorem\"]"

typedecl NonZero
typedecl PointSet
typedecl Real
typedecl RealNonNeg
typedecl RealPos
typedecl RealSet
typedecl SWFeature
typedecl SWObject
typedecl SWSketchObject
typedecl ('a1) Set
typedecl VectorSet
typedecl VectorStar
typedecl ZeroToNine

datatype Point = X_P "Real" "Real" "Real" ("P/'(_,/ _,/ _')" [3,3,3] 999)
datatype Vector = X_V "Real" "Real" "Real" ("V/'(_,/ _,/ _')" [3,3,3] 999)
datatype 'a SWList = XOSqBrXCSqBr ("[/ ]''") | X__XColonXColon__X 'a "'a SWList" ("(_/ ::''/ _)" [54,54] 52)
datatype SWPlane = X_SWPlane "Point" "VectorStar" "Vector"
datatype SWArc = X_SWArc "Point" "Point" "Point"
datatype SWLine = X_SWLine "Point" "Point"
datatype SWSpline = X_SWSpline "Point SWList"
datatype SWSketch = X_SWSketch "SWSketchObject SWList" "SWPlane"
datatype SWExtrusion = X_SWExtrusion "SWSketch" "Real"

-- "subtype definitions"
axioms

subt_VectorStar_Vector [rule_format] :
"!!(x::VectorStar) (y::Vector). subt x y"

subt_NonZero_Real [rule_format] :
"!!(x::NonZero) (y::Real). subt x y"

subt_RealNonNeg_Real [rule_format] :
"!!(x::RealNonNeg) (y::Real). subt x y"

subt_RealPos_Real [rule_format] :
"!!(x::RealPos) (y::Real). subt x y"


consts
ActAttach :: "Point * (Vector => bool) => Point => bool"
ActExtrude :: "Vector * (Point => bool) => Point => bool"
C1X1 :: "Point => Real" ("C1''/'(_')" [3] 999)
C1X2 :: "Vector => Real" ("C1''''/'(_')" [3] 999)
C2X1 :: "Point => Real" ("C2''/'(_')" [3] 999)
C2X2 :: "Vector => Real" ("C2''''/'(_')" [3] 999)
C3X1 :: "Point => Real" ("C3''/'(_')" [3] 999)
C3X2 :: "Vector => Real" ("C3''''/'(_')" [3] 999)
Cylinder :: "(Point * RealPos) * VectorStar => Point => bool"
E1 :: "SWPlane"
E2 :: "SWPlane"
E3 :: "SWPlane"
PlaneX1 :: "SWSketch => SWPlane" ("Plane''/'(_')" [3] 999)
PlaneX2 :: "Point * VectorStar => Point => bool"
VBall :: "Real => Vector => bool"
VCircle :: "Real * Vector => Vector => bool"
VConnected :: "(Vector => bool) * Vector => Vector => bool"
VHalfSpace :: "Vector => Vector => bool"
VHalfSpace2 :: "Vector => Vector => bool"
VLine :: "Vector * Vector => Vector => bool"
VPlane :: "Vector => Vector => bool"
VPlane2 :: "Vector * Vector => Vector => bool"
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
X_Center :: "SWArc => Point" ("Center/'(_')" [3] 999)
X_Depth :: "SWExtrusion => Real" ("Depth/'(_')" [3] 999)
X_End :: "SWArc => Point" ("End/'(_')" [3] 999)
X_From :: "SWLine => Point" ("From/'(_')" [3] 999)
X_InnerCS :: "SWPlane => Vector" ("InnerCS/'(_')" [3] 999)
X_NormalVector :: "SWPlane => VectorStar" ("NormalVector/'(_')" [3] 999)
X_Objects :: "SWSketch => SWSketchObject SWList" ("Objects/'(_')" [3] 999)
X_Points :: "SWSpline => Point SWList" ("Points/'(_')" [3] 999)
X_Pos :: "Real => bool" ("Pos/'(_')" [3] 999)
X_RealNonNeg_inj :: "RealNonNeg => Real" ("RealNonNeg'_inj/'(_')" [3] 999)
X_RealNonNeg_pred :: "Real => bool" ("RealNonNeg'_pred/'(_')" [3] 999)
X_RealNonNeg_proj :: "Real => RealNonNeg" ("RealNonNeg'_proj/'(_')" [3] 999)
X_RealPos_inj :: "RealPos => Real" ("RealPos'_inj/'(_')" [3] 999)
X_RealPos_pred :: "Real => bool" ("RealPos'_pred/'(_')" [3] 999)
X_RealPos_proj :: "Real => RealPos" ("RealPos'_proj/'(_')" [3] 999)
X_SWCylinder :: "Point => Point => VectorStar => SWFeature" ("SWCylinder/'(_,/ _,/ _')" [3,3,3] 999)
X_SWExtrusion_inj :: "SWExtrusion => SWFeature" ("SWExtrusion'_inj/'(_')" [3] 999)
X_SWExtrusion_proj :: "SWFeature => SWExtrusion" ("SWExtrusion'_proj/'(_')" [3] 999)
X_SWReal :: "Real => Real => Real" ("SWReal/'(_,/ _')" [3,3] 999)
X_Sketch :: "SWExtrusion => SWSketch" ("Sketch/'(_')" [3] 999)
X_SpacePoint :: "SWPlane => Point" ("SpacePoint/'(_')" [3] 999)
X_Start :: "SWArc => Point" ("Start/'(_')" [3] 999)
X_To :: "SWLine => Point" ("To/'(_')" [3] 999)
X_VWithLength :: "Vector => Real => Vector" ("VWithLength/'(_,/ _')" [3,3] 999)
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
X_first :: "'a SWList => 'a partial" ("first/'(_')" [3] 999)
X_gn_inj :: "'a => 'b" ("ggn'_inj/'(_')" [3] 999)
X_gn_proj :: "'a => 'b partial" ("ggn'_proj/'(_')" [3] 999)
X_image :: "('S => 'T) * ('S => bool) => 'T => bool"
X_inv :: "NonZero => NonZero" ("inv''/'(_')" [3] 999)
X_isX1 :: "SWSketchObject * SWPlane => Point => bool"
X_isX2 :: "SWSketchObject SWList * SWPlane => Point => bool"
X_lindep :: "Vector => Vector => bool" ("lindep/'(_,/ _')" [3,3] 999)
X_max :: "Real => Real => Real" ("max''/'(_,/ _')" [3,3] 999)
X_min :: "Real => Real => Real" ("min''/'(_,/ _')" [3,3] 999)
X_orth :: "Vector => Vector => bool" ("orth/'(_,/ _')" [3,3] 999)
X_orthcomp :: "Vector => Vector => Vector" ("orthcomp/'(_,/ _')" [3,3] 999)
X_proj :: "Vector => Vector => Vector" ("proj/'(_,/ _')" [3,3] 999)
X_rest :: "'a SWList => 'a SWList partial" ("rest/'(_')" [3] 999)
X_sqrt :: "RealNonNeg => Real" ("sqrt/'(_')" [3] 999)
X_sup :: "Real => Real => Real partial" ("sup/'(_,/ _')" [3,3] 999)
X_vec :: "Point => Point => Vector" ("vec/'(_,/ _')" [3,3] 999)
bigunion :: "(('S => bool) => bool) => 'S => bool"
closedinterval :: "Real * Real => Real => bool"
e1 :: "Vector"
e2 :: "Vector"
e3 :: "Vector"
iX1 :: "SWFeature => Point => bool"
iX2 :: "SWPlane => Point => bool"
iX3 :: "SWSketch => Point => bool"
infX1 :: "Real => Real => Real partial" ("inf''/'(_,/ _')" [3,3] 999)
infX2 :: "(Real => bool) => Real partial" ("inf''''/'(_')" [3] 999)
setFromProperty :: "('S => bool) => 'S => bool"
sqrX1 :: "Real => RealNonNeg" ("sqr''/'(_')" [3] 999)
sqrX2 :: "Vector => RealNonNeg" ("sqr''''/'(_')" [3] 999)

axioms

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

Ax1 [rule_format] : "ALL x. defOp(gn_proj(x)\<Colon>NonZero partial) = (~ x = 0'')"

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

Ax1_2 [rule_format] :
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
"ALL x. defOp (gn_proj(x)\<Colon>RealNonNeg partial) = RealNonNeg_pred(x)"

Ax4 [rule_format] : "ALL x. defOp (gn_proj(x)\<Colon>RealPos partial) = RealPos_pred(x)"

abs_def [rule_format] :
"ALL x.
 makePartial (abs'(x)) =
 gn_proj(if 0'' <=' x then x else -' x)"

times_cancel_right_nonneg_leq [rule_format] :
"ALL a. ALL b. ALL c. a *'' b <=' c *'' b & b >=' 0'' --> a <=' c"

times_leq_nonneg_cond [rule_format] :
"ALL a. ALL b. 0'' <=' a *'' b & b >=' 0'' --> 0'' <=' a"

sqr_def [rule_format] :
"ALL r. gn_inj(sqr'(r)) = r *'' r"

sqrt_def [rule_format] : "ALL q. sqr'(sqrt(q)) = q"

Ax1_2_1 [rule_format] : "ALL x. Pos(x) = (0'' <=' x)"

X2_def_Real [rule_format] : "2' = 1'' +_3 1''"

X3_def_Real [rule_format] : "3' = 2' +_3 1''"

X4_def_Real [rule_format] : "4' = 3' +_3 1''"

X5_def_Real [rule_format] : "5' = 4' +_3 1''"

X6_def_Real [rule_format] : "6' = 5' +_3 1''"

X7_def_Real [rule_format] : "7' = 6' +_3 1''"

X8_def_Real [rule_format] : "8' = 7' +_3 1''"

X9_def_Real [rule_format] : "9' = 8' +_3 1''"

ZeroToNine_type [rule_format] :
"ALL x.
 defOp (gn_proj(x)) =
 (((((((((x = 0'' | x = 1'') | x = 2') |
        x = 3') |
       x = 4') |
      x = 5') |
     x = 6') |
    x = 7') |
   x = 8') |
  x = 9')"

decimal_def [rule_format] :
"ALL m.
 ALL X_n. m @@ X_n = (gn_inj(m) *'' (9' +_3 1'')) +_3 X_n"

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

Ax7_1_1 [rule_format] :
"ALL x. defOp (gn_proj(x)\<Colon>VectorStar partial) = VectorStar_pred(x)"

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

ONB1 [rule_format] : "e1 = V(1'', 0'', 0'')"

ONB2 [rule_format] : "e2 = V(0'', 1'', 0'')"

ONB3 [rule_format] : "e3 = V(0'', 0'', 1'')"

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

unit [rule_format] : "ALL x. 1'' *_3 x = x"

mix_assoc [rule_format] :
"ALL r. ALL s. ALL x. (r *'' s) *_3 x = r *_3 (s *_3 x)"

distr_Field [rule_format] :
"ALL r. ALL s. ALL x. (r +_3 s) *_3 x = (r *_3 x) +_4 (s *_3 x)"

distr_Space [rule_format] :
"ALL r. ALL x. ALL y. r *_3 (x +_4 y) = (r *_3 x) +_4 (r *_3 y)"

zero_by_left_zero [rule_format] : "ALL x. 0'' *_3 x = 0_3"

zero_by_right_zero [rule_format] : "ALL r. r *_3 0_3 = 0_3"

no_zero_divisor [rule_format] :
"ALL r. ALL x. ~ r = 0'' & ~ x = 0_3 --> ~ r *_3 x = 0_3"

inverse_by_XMinus1 [rule_format] :
"ALL x. -' 1'' *_3 x = -'' x"

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

sqr2_def [rule_format] :
"ALL x. makePartial (sqr''(x)) = gn_proj(x *_4 x)"

norm_from_inner_prod_def [rule_format] :
"ALL x. || x || = sqrt(sqr''(x))"

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

homogeneous_1 [rule_format] :
"ALL r. ALL v. || r *_3 v || = gn_inj(abs'(r)) *'' || v ||"

definite [rule_format] : "ALL v. || v || = 0'' = (v = 0_3)"

pos_definite_1 [rule_format] : "ALL v. 0'' <=' || v ||"

pos_homogeneous [rule_format] :
"ALL r. ALL v. r >=' 0'' --> || r *_3 v || = r *'' || v ||"

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
"ALL z.
 ALL v.
 ALL w.
 ALL x.
 ALL y.
 ((((~ z = 0_3 & x +_4 y = v +_4 w) & lindep(x, z)) & lindep(v, z))
  & orth(z, y)) & orth(z, w) --> x = v & y = w"

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
 PlaneX2 (offset, normal) =
 (% x. orth(vec(x, offset), gn_inj(normal)))"

plane_condition_for_2_points [rule_format] :
"ALL normal.
 ALL offset.
 ALL x.
 ALL y.
 let plane = PlaneX2 (offset, normal)
 in x isIn plane & y isIn plane --> orth(vec(x, y), gn_inj(normal))"

plane_condition_for_point_and_vector [rule_format] :
"ALL normal.
 ALL offset.
 ALL v.
 ALL x.
 let plane = PlaneX2 (offset, normal)
 in x isIn plane & orth(v, gn_inj(normal)) --> x +' v isIn plane"

ga_select_first [rule_format] :
"ALL x_1. ALL x_2. first(x_1 ::' x_2) = makePartial x_1"

ga_select_rest [rule_format] :
"ALL x_1. ALL x_2. rest(x_1 ::' x_2) = makePartial x_2"

ga_select_SpacePoint [rule_format] :
"ALL x_1.
 ALL x_2. ALL x_3. SpacePoint(X_SWPlane x_1 x_2 x_3) = x_1"

ga_select_NormalVector [rule_format] :
"ALL x_1.
 ALL x_2. ALL x_3. NormalVector(X_SWPlane x_1 x_2 x_3) = x_2"

ga_select_InnerCS [rule_format] :
"ALL x_1. ALL x_2. ALL x_3. InnerCS(X_SWPlane x_1 x_2 x_3) = x_3"

ga_select_Center [rule_format] :
"ALL x_1. ALL x_2. ALL x_3. Center(X_SWArc x_1 x_2 x_3) = x_1"

ga_select_Start [rule_format] :
"ALL x_1. ALL x_2. ALL x_3. Start(X_SWArc x_1 x_2 x_3) = x_2"

ga_select_End [rule_format] :
"ALL x_1. ALL x_2. ALL x_3. End(X_SWArc x_1 x_2 x_3) = x_3"

ga_select_From [rule_format] :
"ALL x_1. ALL x_2. From(X_SWLine x_1 x_2) = x_1"

ga_select_To [rule_format] :
"ALL x_1. ALL x_2. To(X_SWLine x_1 x_2) = x_2"

ga_select_Points [rule_format] :
"ALL x_1. Points(X_SWSpline x_1) = x_1"

ga_select_Objects [rule_format] :
"ALL x_1. ALL x_2. Objects(X_SWSketch x_1 x_2) = x_1"

ga_select_Plane [rule_format] :
"ALL x_1. ALL x_2. Plane'(X_SWSketch x_1 x_2) = x_2"

ga_select_Sketch [rule_format] :
"ALL x_1. ALL x_2. Sketch(X_SWExtrusion x_1 x_2) = x_1"

ga_select_Depth [rule_format] :
"ALL x_1. ALL x_2. Depth(X_SWExtrusion x_1 x_2) = x_2"

E1_def [rule_format] :
"E1 =
 X_SWPlane (P(0'', 0'', 0''))
 (VectorStar_proj(V(0'', 0'', 1'')))
 (V(1'', 0'', 0''))"

E2_def [rule_format] :
"E2 =
 X_SWPlane (P(0'', 0'', 0''))
 (VectorStar_proj(V(0'', 1'', 0'')))
 (V(1'', 0'', 0''))"

E3_def [rule_format] :
"E3 =
 X_SWPlane (P(0'', 0'', 0''))
 (VectorStar_proj(V(1'', 0'', 0'')))
 (V(0'', 1'', 0''))"

VLine_constr [rule_format] :
"ALL p1.
 ALL p2.
 VLine (p1, p2) =
 X_image
 (% y. p1 +_4 (y *_3 (p2 -'' p1)),
  closedinterval (0'', 1''))"

VWithLength_constr [rule_format] :
"ALL s.
 ALL v.
 makePartial (VWithLength(v, s)) =
 (if v = 0_3 then makePartial v
     else restrictOp
          (makePartial ((s /' makeTotal (gn_proj( || v || ))) *_3 v))
          (defOp (gn_proj( || v || )\<Colon>NonZero partial)))"

VPlane_constr [rule_format] :
"ALL normal. VPlane normal = (% y. orth(y, normal))"

VPlane2_constr [rule_format] :
"ALL axis1.
 ALL axis2. VPlane2 (axis1, axis2) = VPlane (axis1 #' axis2)"

VConnected_constr [rule_format] :
"ALL frontier.
 ALL point.
 VConnected (frontier, point) =
 (if frontier point then frontier
     else % y. X__intersection__X (VLine (point, y), frontier) =
               X_emptySet)"

VHalfSpace_constr [rule_format] :
"ALL normal.
 VHalfSpace normal = VConnected (VPlane normal, normal)"

VHalfSpace2_constr [rule_format] :
"ALL normal.
 VHalfSpace2 normal =
 X__union__X (VConnected (VPlane normal, normal), VPlane normal)"

VBall_constr [rule_format] :
"ALL r. VBall r = (% y. || y || <=' r)"

VCircle_constr [rule_format] :
"ALL axis.
 ALL r.
 VCircle (r, axis) = X__intersection__X (VPlane axis, VBall r)"

ActAttach_constr [rule_format] :
"ALL point.
 ALL vectors.
 ActAttach (point, vectors) = X__XPlus__XX2 (point, vectors)"

ActExtrude_constr [rule_format] :
"ALL axis.
 ALL points.
 ActExtrude (axis, points) =
 (% x. EX l.
       EX y.
       (l isIn closedinterval (0'', 1'') & y isIn points) &
       x = y +' (l *_3 axis))"

vwl_identity [rule_format] :
"ALL s. ALL v. || v || = s --> VWithLength(v, s) = v"

vwl_length [rule_format] :
"ALL s.
 ALL v.
 ~ v = 0_3 -->
 || VWithLength(v, s) || = gn_inj(abs'(s))"

vwl_lindep [rule_format] :
"ALL s. ALL v. lindep(v, VWithLength(v, s))"

semantics_for_Planes [rule_format] :
"ALL ics.
 ALL X_n.
 ALL X_o.
 iX2 (X_SWPlane X_o X_n ics) =
 ActAttach (X_o, VPlane (gn_inj(X_n)))"

semantics_for_SketchObject_listsXMinusBaseCase [rule_format] :
"ALL plane. X_isX2 ([ ]', plane) = X_emptySet"

semantics_for_SketchObject_listsXMinusRecursiveCase [rule_format] :
"ALL plane.
 ALL sko.
 ALL skos.
 X_isX2 (sko ::' skos, plane) =
 X__union__X (X_isX1 (sko, plane), X_isX2 (skos, plane))"

semantics_for_Arcs [rule_format] :
"ALL plane.
 ALL x.
 ALL y.
 ALL z.
 X_isX1 (gn_inj(X_SWArc x y z), plane) =
 (let r1 = vec(x, y);
      ball = ActAttach (x, VBall ( || r1 || ));
      planeI = iX2 plane
  in X__intersection__X (ball, planeI))"

semantics_for_Sketches [rule_format] :
"ALL plane.
 ALL skos. iX3 (X_SWSketch skos plane) = X_isX2 (skos, plane)"

semantics_for_ArcExtrusion [rule_format] :
"ALL l.
 ALL sk.
 iX1 (SWExtrusion_inj(X_SWExtrusion sk l)) =
 ActExtrude
 (VWithLength(gn_inj(NormalVector(Plane'(sk))), l), iX3 sk)"

plane_is_plane [rule_format] :
"ALL plane.
 iX2 plane = PlaneX2 (SpacePoint(plane), NormalVector(plane))"

def_of_SWCylinder [rule_format] :
"ALL axis.
 ALL boundarypoint.
 ALL center.
 SWCylinder(center, boundarypoint, axis) =
 (let plane = X_SWPlane center axis (V(0'', 0'', 0''));
      arc = X_SWArc center boundarypoint boundarypoint;
      height = || gn_inj(axis) ||
  in SWExtrusion_inj(X_SWExtrusion
                     (X_SWSketch (gn_inj(arc) ::' [ ]') plane) height))"

affine_cylinder_constructible_in_SW [rule_format] :
"ALL axis.
 ALL offset.
 ALL r.
 Cylinder ((offset, r), axis) =
 (let boundary =
      % p. let v = vec(offset, p)
           in orth(v, gn_inj(axis)) & || v || = gn_inj(r);
      boundarypoint = choose'(boundary)
  in iX1 (SWCylinder(offset, boundarypoint, axis)))"

declare ga_assoc___Xx__ [simp]
declare ga_right_unit___Xx__ [simp]
declare ga_left_unit___Xx__ [simp]
declare inv_Group [simp]
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
declare sqrt_def [simp]
declare ga_select_C1 [simp]
declare ga_select_C2 [simp]
declare ga_select_C3 [simp]
declare ga_select_C1_1 [simp]
declare ga_select_C2_1 [simp]
declare ga_select_C3_1 [simp]
declare Ax7_1_1 [simp]
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
declare ga_select_first [simp]
declare ga_select_rest [simp]
declare ga_select_SpacePoint [simp]
declare ga_select_NormalVector [simp]
declare ga_select_InnerCS [simp]
declare ga_select_Center [simp]
declare ga_select_Start [simp]
declare ga_select_End [simp]
declare ga_select_From [simp]
declare ga_select_To [simp]
declare ga_select_Points [simp]
declare ga_select_Objects [simp]
declare ga_select_Plane [simp]
declare ga_select_Sketch [simp]
declare ga_select_Depth [simp]
declare vwl_identity [simp]
declare vwl_lindep [simp]
declare semantics_for_SketchObject_listsXMinusBaseCase [simp]
declare semantics_for_Sketches [simp]


(*
-- let-simplifier
declare flip_def [simp]
definition compose_def [simp]: "compose f g x = f (g x)"

lemma Let_simps:
  "!!f m g. f (Let m g) = Let m (compose f g)"
  "!!m f n. (Let m f) n = Let m (flip f n)"
  "!!f g. compose f (%x. g x) = (%x. f (g x))"
  "!!f y. flip (%x. f x) y = (%x. f x y)"
  "!!f g. compose f (split g) = split (compose (compose f) g)"
  "!!f x. flip (split f) x = split (flip (compose flip f) x)"
unfolding Let_def expand_fun_eq by simp_all

*)

lemmas PO_simps = 
  geq_def_ExtPartialOrder
  less_def_ExtPartialOrder 
  greater_def_ExtPartialOrder

theorem def_of_Cylinder :
"ALL axis.
 ALL offset.
 ALL r.
 Cylinder ((offset, r), axis) =
 (% x. let v = vec(offset, x)
       in ( || proj(v, gn_inj(axis)) || <=' || gn_inj(axis) || &
            || orthcomp(v, gn_inj(axis)) || <=' gn_inj(r)) &
          v *_4 gn_inj(axis) >=' 0'')"

  -- "unfolding some initial definitions"
  unfolding affine_cylinder_constructible_in_SW
  unfolding def_of_SWCylinder

  proof (rule allI)+

    -- "I. SUBTYPE AND PARTIALITY LEMMAS"

    -- "need this to expand a term for application of lemmas"
    have partial_identity: "!!x. makeTotal(makePartial(x)) = x"
      by (simp only: snd_conv makeTotal_def makePartial_def)

    -- "to infer knowledge of the form"
    -- "!!x::subtype. ?defining_predicate(gn_inj(x))"
    -- "where the ? emphasizes the fact, that we want the predicate to be expanded,"
    -- "we would need a tactic which retrieves for a given subtype the 3 rules:"
    -- "S_pred_def, Ax4(linking the defining predicate to the defOp) and subt_S_T"
    -- "As the subtype can be inferred from the context, no arguments would be"
    -- "required for this tactic"
    have RealPos_subtype: "!!x::RealPos. gn_inj x >' 0''"
      by (simp only: RealPos_pred_def [THEN sym], subst Ax4 [THEN sym],
	simp only: gn_inj_defOp subt_RealPos_Real)

    have VectorStar_subtype: "!!x::VectorStar. (~ gn_inj x = 0_3)"
      by (simp only: VectorStar_pred_def [THEN sym], subst Ax7_1_1 [THEN sym],
	simp only: gn_inj_defOp subt_VectorStar_Vector)

    from RealPos_subtype have
      realpos_nonneg: "!!x::RealPos. 0'' <=' gn_inj x"
      by (simp only: PO_simps)

    from subt_RealPos_Real subt_RealNonNeg_Real
    have subt_RealPos_RealNonNeg:
      "!!(x::RealPos) (y::RealNonNeg). subt x y"
      by (rule_tac subt_subsumption, blast,
	simp add: RealPos_pred_def RealNonNeg_pred_def PO_simps)

    from subt_RealPos_RealNonNeg subt_RealNonNeg_Real subt_RealPos_Real
    have real_inj:
      "!!(x::RealPos). (gn_inj(x)\<Colon>Real) = gn_inj(gn_inj(x)\<Colon>RealNonNeg)"
      by (rule_tac subt_inj_diagram, simp)

    have realnonneg_identity:
      "!!x::RealNonNeg. makeTotal(gn_proj((gn_inj x)\<Colon>Real)) = x"
      by (simp only: gn_inj_identity subt_RealNonNeg_Real)
    
    -- "II. GENERAL LEMMAS -- these Lemmas can't be outsourced for the moment"

    from e1e2_nonlindep have space_at_least_2dim: "EX v w. \<not> lindep(v,w)" by blast

    have abs_on_realpos:
      "!!x::RealPos. abs'(gn_inj(x)) = gn_inj x"
      -- "INTERESTING: can't combine the two simp only's!"
    by (subst partial_identity [THEN sym], subst abs_def,
      simp only: if_P realpos_nonneg, simp only: real_inj realnonneg_identity)

    have vwl_pos_length: "!!(s::RealPos) v. ~ v = 0_3 -->
      || VWithLength(v, gn_inj(s)) || = gn_inj(s)"
    proof (rule impI)
      fix s::RealPos
      fix v::Vector
      assume hyp: "v \<noteq> 0_3"
      with vwl_length have
	"|| VWithLength(v, gn_inj s) || = gn_inj(abs'(gn_inj s))" by blast
      also have "\<dots> = gn_inj(gn_inj s\<Colon>RealNonNeg)" by (simp only: abs_on_realpos)
      also have "\<dots> = gn_inj(s)" by (simp only: real_inj)
      finally show "|| VWithLength(v, gn_inj(s)) || = gn_inj(s)" by blast
    qed

    from space_at_least_2dim orthogonal_existence_theorem
    have orth_exists_aux: "!!w. EX x. x \<noteq> 0_3 \<and> orth(x, w)" by blast

    have orth_exists:
      "!!q w (r::RealPos). EX p. let v = vec(q, p) in orth(v, w) & || v || = gn_inj(r)"
      (is "!!q w r. EX p. ?P q w r p")
    proof-
      fix q w
      fix r::RealPos

      from orth_exists_aux obtain v where v_props: "v \<noteq> 0_3 \<and> orth(v, w)" ..
      def vprime_def: v' == "VWithLength(v, gn_inj(r))"
      def p: p == "q +' v'"

      with plus_vec_identity have vp_rel: "v' = vec(q, p)" by simp

      from  lindep_symmetry orth_symmetric vwl_lindep lindep_orth_transitive
	v_props vprime_def have fact1: "orth(v', w)" by blast

      with v_props vwl_pos_length vprime_def
      have "orth(v', w) \<and> || v' || = gn_inj(r)" by blast

      with vp_rel fact1 have "?P q w r p" by simp

      thus "EX p. ?P q w r p" ..
    qed

    -- "need this fact to use the proj_def"
    have subtype_cond: "!A x. (x \<noteq> 0'') \<longrightarrow> (restrictOp A (defOp(gn_proj(x)\<Colon>NonZero partial))) = A"
    proof ((rule allI)+, rule impI)
      fix A x
      assume hyp: "x \<noteq> 0''"
      show "restrictOp A (defOp (gn_proj(x)\<Colon>NonZero partial)) = A"
	apply (subst restrictOp_def)
	apply (subst if_P)
	apply (subst Ax1)
	by (simp add: hyp, simp)
    qed

    -- "END LEMMAS"

    fix axis::VectorStar
    fix offset::Point
    fix r::RealPos

    -- "providing vars for the let-constructs"
    def boundary: boundary == "\<lambda>p. let v = vec(offset, p) in orth(v, gn_inj(axis)) \<and> || v || = gn_inj(r)"
    def boundarypoint: bp == "choose'(boundary)"
    def plane: pln == "X_SWPlane offset axis (V(0'', 0'', 0''))"
    def arc: arc == "X_SWArc offset bp bp"
    def height: ht == "|| gn_inj(axis) ||"
    def sketch: sketch == "X_SWSketch (gn_inj(arc) ::' [ ]') pln"

    -- "additional definitions, not stemming from let-vars"
    def I01: I01 == "closedinterval (0'', 1'')"

    -- "we know that Plane(sketch) = pln"
    from plane sketch ga_select_Plane
    have sketchplane_identity: "pln = Plane'(sketch)" by simp

    -- "we know that NormalVector(pln) = axis"
    from plane ga_select_NormalVector
    have nv_identity: "axis = NormalVector(pln)" by simp
    

    def r1: r1 == "vec(offset, bp)"
    def ball: bll == "ActAttach (offset, VBall ( || r1 || ))"
    def planeI: plnI == "ActAttach (offset, VPlane (gn_inj(axis)))"
    def scaledAxis: axs == "VWithLength(gn_inj(axis), ht)"
    

    -- "we can identify gn_inj(axis) and axs via vwl_identity!"
    from scaledAxis vwl_identity height
    have axis_identity: "axs = gn_inj(axis)" by simp

    have axs_nonzero: "axs \<noteq> 0_3" by (subst axis_identity, rule VectorStar_subtype)
    with non_degenerate rev_contrapos
    have axs_norm_nonzero: "axs *_4 axs \<noteq> 0''" by blast

    -- "PP = ProofPower remark"
    -- "PP: doesn't work in one step!"
    from axs_nonzero pos_definite have "axs *_4 axs >' 0''" by blast
    with PO_simps
    have axs_sqr_nonneg: "axs *_4 axs >=' 0''" by blast

    -- "show facts about bp, r and r1"
    have bp_in_boundary: "boundary bp" 
      proof-
	from boundary orth_exists have "Ex boundary" by blast
	with Point_choice boundarypoint show ?thesis by blast
      qed
    hence r1_r_relation: "|| r1 || = gn_inj(r)"
      by (simp add: r1 boundary Let_def)

    -- "we don't want to manipulate the right hand side, so we replace it by rhs"
    def rhs: rhs == "(\<lambda>x. let v = vec(offset, x)
            in ( || proj(v, gn_inj(axis)) || <=' || gn_inj(axis) || \<and>
                || orthcomp(v, gn_inj(axis)) || <=' gn_inj(r)) \<and>
               v *_4 gn_inj(axis) >=' 0'')"


    -- "going in apply-mode again"
    show "(let boundary = \<lambda>p. let v = vec(offset, p) in orth(v, gn_inj(axis)) \<and> || v || = gn_inj(r);
            boundarypoint = choose'(boundary)
        in iX1 (let plane = X_SWPlane offset axis (V(0'', 0'', 0''));
                    arc = X_SWArc offset boundarypoint boundarypoint; height = || gn_inj(axis) ||
                in SWExtrusion_inj(X_SWExtrusion (X_SWSketch (gn_inj(arc) ::' [ ]') plane) height))) =
       (\<lambda>x. let v = vec(offset, x)
            in ( || proj(v, gn_inj(axis)) || <=' || gn_inj(axis) || \<and>
                || orthcomp(v, gn_inj(axis)) || <=' gn_inj(r)) \<and>
               v *_4 gn_inj(axis) >=' 0'')"
      
      apply (subst rhs [symmetric])

      apply (subst boundary [symmetric])
      -- "get the boundarypoint definition replaced"
      apply (subst Let_def)
      apply (subst boundarypoint [symmetric])
      apply (subst plane [symmetric])
      -- "get the boundarypoint definition replaced"
      apply (subst Let_def)
      apply (subst height [symmetric])
      apply (subst arc [symmetric])
      unfolding Let_def
      apply (subst sketch [symmetric])

      -- "second round of let-elimination, but first some definition unfoldings"
      unfolding semantics_for_ArcExtrusion ActExtrude_constr

      apply (subst sketchplane_identity [symmetric])
      apply (subst nv_identity [symmetric])
      apply (subst sketch)

      unfolding semantics_for_Sketches semantics_for_SketchObject_listsXMinusRecursiveCase

      apply (subst arc)

      unfolding semantics_for_Arcs

      apply (subst I01 [symmetric])
      
      apply (subst r1 [symmetric])
      -- "get the r1 definition replaced"
      apply (subst Let_def)
      apply (subst ball [symmetric])
      apply (subst Let_def)

      apply (subst plane)
      unfolding semantics_for_Planes

      apply (subst planeI [symmetric])
      apply (subst scaledAxis [symmetric])
      unfolding Let_def

      unfolding semantics_for_SketchObject_listsXMinusBaseCase
      apply (subst emptySet_union_right_unit)
      apply (subst def_of_intersection)

      apply (subst rhs)
      apply (subst axis_identity [symmetric])+
      
      proof (rule ext)
	fix x
	def v: v == "vec(offset, x)"
	def vp: vp == "proj(v, axs)" -- "the axis-parallel component"
	def vo: vo == "orthcomp(v, axs)" -- "the axis-orthogonal component"

        -- "using the orthogonal projection theorem here!"
	hence vo_axs_orth: "orth(axs, vo)" by simp
	hence vo_mult_axs_zero: "vo *_4 axs = 0''"
	  by (simp only: orth_symmetric orthogonal_def [symmetric])

	have vp_structure: "EX k. vp = k *_3 axs"
	  unfolding vp
	  apply (subst partial_identity [symmetric], subst proj_def)
	  apply (subst if_not_P, simp add: axs_nonzero)
	  apply (subst subtype_cond, simp add: axs_norm_nonzero)
	  apply (subst partial_identity)
	  by auto

	-- "here we provide already the knowledge that v = vp + vo"
	have v_decomp: "v = vp +_4 vo" by (simp only: vo vp orthogonal_decomposition_theorem)


	from v_decomp have "v *_4 axs = (vp +_4 vo) *_4 axs" by simp
	also have "\<dots> = (vp *_4 axs) +_3 (vo *_4 axs)" by (simp only: distributive)
	also have "\<dots> = (vp *_4 axs)" by (simp add: vo_mult_axs_zero)
	finally have v_mult_axs_simp: "v *_4 axs = vp *_4 axs" by simp
	
	-- "going in apply-mode again"
	show "(\<exists>l y. (l isIn I01 \<and> y isIn bll \<and> y isIn plnI) \<and>
               x = y +' (l *_3 axs)) =
        (let v = vec(offset, x)
         in ( || proj(v, axs) || <=' || axs || \<and>
             || orthcomp(v, axs) || <=' gn_inj(r)) \<and>
            v *_4 axs >=' 0'')"

	  apply (subst v [symmetric])
	  apply (subst Let_def)
	  apply (subst vp [symmetric])
	  apply (subst vo [symmetric])

	  -- "having normalized the problem we can now start the main proof!"
	proof

	assume "\<exists>l y. (l isIn I01 \<and> y isIn bll \<and> y isIn plnI) \<and> x = y +' (l *_3 axs)"
	(is "\<exists>l y. (?I l \<and> ?B y \<and> ?P y) \<and> ?S l y")
	then obtain l y where main_knowledge: "(?I l \<and> ?B y \<and> ?P y) \<and> ?S l y" by blast

	def yvec: y' == "vec(offset, y)" -- "the offset-based component of y"

        -- "we know that y' is in the given VBall because of its structure"
	have yprime_in_ball: "y' isIn VBall ( || r1 || ) \<and> offset +' y' = y" (is "?L y'")
	proof-
	  from main_knowledge	have "EX y1. ?L y1"
	    by (subst (asm) ball, subst (asm) ActAttach_constr,
	      subst (asm) plus_Point_VectorSet, subst (asm) function_image_structure, simp)
	  then obtain y1 where obtained_from_ball: "?L y1" ..
	  with yvec plus_injective vec_def have "y' = y1" by blast
	  with obtained_from_ball show ?thesis by simp
	qed

        -- "identically we know that y' is in the given VPlane because of its structure"
	have yprime_in_plane: "y' isIn  VPlane(gn_inj(axis)) \<and> offset +' y' = y" (is "?L' y'")
	proof-
	  from main_knowledge	have "EX y1. ?L' y1"
	    by (subst (asm) planeI, subst (asm) ActAttach_constr,
	      subst (asm) plus_Point_VectorSet, subst (asm) function_image_structure, simp)
	  then obtain y1 where obtained_from_plane: "?L' y1" ..
	  with yvec plus_injective vec_def have "y' = y1" by blast
	  with obtained_from_plane show ?thesis by simp
	qed

	from v have "x = offset +' v" by simp
	with yprime_in_ball main_knowledge
	have "offset +' v = (offset +' y') +'(l *_3 axs)" by simp
	hence "v = y' +_4 (l *_3 axs)"
	  by (simp only:  point_vector_plus_associative [symmetric] plus_injective)
	hence "vp +_4 vo = y' +_4 (l *_3 axs)" 
	  by (simp only: v_decomp)
	hence vyprime_rel: "vp +_4 vo = (l *_3 axs) +_4 y'" 
	  by (simp only: ga_comm___Xx___3)
	have main_identity: "vp = l *_3 axs \<and> vo = y'"
	  proof (rule_tac z="axs" in unique_orthogonal_decomposition)
	    -- "mi_subgoal1 is equal to axs_nonzero"
 
	    from vyprime_rel have mi_subgoal2: "vp +_4 vo = (l *_3 axs) +_4 y'" .

	    from vp_structure lindep_def have mi_subgoal3: "lindep(vp, axs)"
	      by blast

	    from lindep_def have mi_subgoal4: "lindep(l *_3 axs, axs)" by blast

	    -- "mi_subgoal5 is equal to vo_axs_orth"

	    from axis_identity yprime_in_plane VPlane_constr
	    have mi_subgoal6: "orth(axs, y')" by simp

	    with axs_nonzero mi_subgoal2 mi_subgoal3 mi_subgoal4 vo_axs_orth
	    show "((((((axs \<noteq> 0_3) \<and> ((vp +_4 vo) = ((l *_3 axs) +_4 y'))) \<and> (lindep(vp, axs))) \<and>
              (lindep((l *_3 axs), axs))) \<and> (orth(axs, vo))) \<and> (orth(axs, y')))" by blast
	  qed

	  -- "(vp = l * axs) and 0 <= l <= 1 should gives us the result"

	  -- "0 <= l <= 1"
	  have l_in_unitinterval: "0'' <=' l \<and> l <=' 1''"
	    proof-
	      from main_knowledge I01 have "l isIn closedinterval(0'', 1'')" by blast
	      with abbrev_of_interval have "XOSqBr__XPeriodXPeriodXPeriod__XCSqBr(0'', 1'') l"
		by simp
	      thus ?thesis by (simp add: def_of_interval PO_simps)
	    qed

	  have subgoal1: "|| vp || <=' || axs ||"
	  proof-
	    from main_identity have "|| vp || = || l *_3 axs ||" by simp
	    also have "\<dots> = l *'' || axs ||"
	      by (simp only: PO_simps pos_homogeneous l_in_unitinterval)
	    also have "\<dots> <=' || axs ||"
	      by (subst ga_left_unit___Xx___1 [symmetric],
		rule FWO_times_left,
		simp add: l_in_unitinterval pos_definite_1)
	    finally show ?thesis .
	  qed

	  from r1_r_relation VBall_constr yprime_in_ball main_identity
	  have subgoal2: "|| vo || <=' gn_inj(r)" by simp

	  from v_mult_axs_simp have "v *_4 axs = l *'' (axs *_4 axs)"
	    by (simp add: main_identity homogeneous)
	  also from axs_sqr_nonneg l_in_unitinterval geq_def_ExtPartialOrder
	    FWO_times_right have "\<dots> >=' l *'' 0''" by blast
	  also from right_zero have "\<dots> = 0''" by blast
	  finally have subgoal3: "v *_4 axs >=' 0''" by simp

	  with subgoal1 subgoal2
	  show "( || vp || <=' || axs || \<and> 
	    || vo || <=' gn_inj(r)) \<and> v *_4 axs >=' 0''" by blast
	
        -- "tackle other direction here"
	next

	  assume main_knowledge:
	    "( || vp || <=' || axs || \<and> || vo || <=' gn_inj(r)) \<and> v *_4 axs >=' 0''"
	  
	  -- "We show vp = k * axs, and set l := k, y := offset + vo and"
          -- "verify the four conditions for l and y."
	  from vp_structure obtain l where l_def: "vp = l *_3 axs" ..
	  def y_def: y == "offset +' vo"
	  have "(l isIn I01 \<and> y isIn bll \<and> y isIn plnI) \<and> x = y +' (l *_3 axs)"
	    (is "?G l y")
	  proof-

	    -- "PROOF for first conjunct"

	    from pos_definite_1 have axs_norm_nonneg: "||axs|| >=' 0''"
	      by (simp only: PO_simps)

	    from v_mult_axs_simp main_knowledge l_def homogeneous
	    have "l *'' (axs *_4 axs) >=' 0''" by simp

	    with times_leq_nonneg_cond axs_sqr_nonneg PO_simps
	    have I01_first: "l >=' 0''" by blast

	    with main_knowledge l_def pos_homogeneous
	    have "l *'' || axs || <=' || axs ||"
	      -- "TODO: check whether this means only the logical rules"
	      by (simp only:)

	    with axs_norm_nonneg have I01_second: "l <=' 1''"
	      by (subst (asm) ga_left_unit___Xx___1 [symmetric],
		insert times_cancel_right_nonneg_leq [of l "||axs||"],
		simp)

	    with I01_first I01 def_of_interval abbrev_of_interval
	      def_of_isIn PO_simps
	    have subgoal1: "l isIn I01" by auto
	    
	    -- "PROOF for second conjunct"

	    from main_knowledge r1_r_relation VBall_constr
	    have "vo isIn VBall( || r1 || )" by simp
	    hence subgoal2: "y isIn bll"
	      by (subst y_def,subst ball, 
		subst ActAttach_constr,
		subst plus_Point_VectorSet,
		subst function_image,
		subst def_of_isIn, auto)
	    -- "the same way we obtain the third subgoal!"

	    -- "PROOF for third conjunct"

	    from vo_axs_orth axis_identity VPlane_constr
	    have "vo isIn VPlane(axs)" by simp
	    hence subgoal3: "y isIn plnI"
	      by (subst y_def, subst planeI, subst ActAttach_constr
		, subst plus_Point_VectorSet
		, subst function_image
		, (subst def_of_isIn)+
		, subst axis_identity [symmetric]
		, auto)

	    -- "PROOF for fourth conjunct"

	    have subgoal4: "x = y +' (l *_3 axs)"
	      by (subst y_def, subst l_def [symmetric]
		, subst point_vector_plus_associative [symmetric]
		, subst ga_comm___Xx___3
		, subst v_decomp [symmetric]
		, simp only: ga_comm___Xx___3 v vec_def)

	    with subgoal1 subgoal2 subgoal3 show ?thesis by blast
	  qed
	  thus "EX l y. ?G l y" by auto
	qed
      qed
    qed

ML "Header.record \"def_of_Cylinder\""

end
