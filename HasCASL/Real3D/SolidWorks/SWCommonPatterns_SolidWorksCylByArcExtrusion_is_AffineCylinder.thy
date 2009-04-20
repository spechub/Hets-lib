theory SWCommonPatterns_SolidWorksCylByArcExtrusion_is_AffineCylinder
imports "$HETS_LIB/Isabelle/MainHCPairs"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"inv_Group\", \"rinv_Group\", \"distr1_Ring\", \"distr2_Ring\",
     \"noZeroDiv\", \"zeroNeqOne\", \"Ax1\", \"inv_Group_1\",
     \"rinv_Group_1\", \"binary_inverse\", \"Ax1_1\", \"refl\",
     \"trans\", \"antisym\", \"dichotomy_TotalOrder\",
     \"FWO_plus_left\", \"FWO_times_left\", \"FWO_plus_right\",
     \"FWO_times_right\", \"FWO_plus\", \"Ax1_2\",
     \"Real_completeness\", \"geq_def_ExtPartialOrder\",
     \"less_def_ExtPartialOrder\", \"greater_def_ExtPartialOrder\",
     \"ga_comm_inf\", \"ga_comm_sup\", \"inf_def_ExtPartialOrder\",
     \"sup_def_ExtPartialOrder\", \"ga_comm_min\", \"ga_comm_max\",
     \"ga_assoc_min\", \"ga_assoc_max\", \"ga_left_comm_min\",
     \"ga_left_comm_max\", \"min_def_ExtTotalOrder\",
     \"max_def_ExtTotalOrder\", \"min_inf_relation\",
     \"max_sup_relation\", \"Ax1_3\", \"Ax2\", \"sqr_def\",
     \"sqrt_def\", \"Ax1_2_1\", \"X2_def_Real\", \"X3_def_Real\",
     \"X4_def_Real\", \"X5_def_Real\", \"X6_def_Real\", \"X7_def_Real\",
     \"X8_def_Real\", \"X9_def_Real\", \"ZeroToNine_type\",
     \"decimal_def\", \"ga_select_C1\", \"ga_select_C2\",
     \"ga_select_C3\", \"Zero_Point\", \"ga_select_C1_1\",
     \"ga_select_C2_1\", \"ga_select_C3_1\", \"Zero_Vector\",
     \"def_of_vector_addition\", \"def_of_minus_vector\",
     \"binary_inverse_1_1\", \"scalar_mutliplication\",
     \"scalar_product\", \"vector_product\", \"cross_left_homogenity\",
     \"cross_product_antisymmetric\", \"inv_Group_2_1\",
     \"rinv_Group_2_1\", \"mix_assoc\", \"distr_Field\",
     \"distr_Space\", \"distributiv\", \"homogen\", \"commutativ\",
     \"pos_definit\", \"right_distributiv\", \"right_homogen\",
     \"colin_def\", \"colin_reflexivity\", \"colin_symmetry\",
     \"simple_colin_condition\", \"sqr_def_1_1\",
     \"norm_from_scalar_prod_def\", \"orthogonal_def\",
     \"orth_symmetry\", \"colin_orth_transitivity\",
     \"cross_product_orthogonal\", \"cross_product_zero_iff_colinear\",
     \"point_to_vector_embedding\", \"vector_to_point_embedding\",
     \"Ax1_1_1\", \"vector_point_vector\", \"point_vector_point\",
     \"origin_to_zero\", \"vec_def\", \"compatibility_PVplus_Vplus\",
     \"transitivity_of_vec_XPlus\", \"antisymmetry_of_vec\",
     \"vec_shift_unique_lemma\", \"vec_shift_def_lemma\",
     \"point_vector_add_comm_lemma\", \"set_comprehension\",
     \"function_image\", \"emptySet_not_empty\",
     \"allSet_contains_all\", \"def_of_isIn\", \"def_of_subset\",
     \"def_of_union\", \"def_of_bigunion\", \"def_of_intersection\",
     \"def_of_difference\", \"def_of_disjoint\", \"def_of_productset\",
     \"def_of_interval\", \"plus_PointSet_Vector\",
     \"plus_Point_VectorSet\", \"plus_PointSet_VectorSet\",
     \"def_of_Plane\", \"def_of_Circle\", \"def_of_Cylinder\",
     \"def_of_Cylinder1\", \"plane_condition_for_2_points\",
     \"direction_subtype\", \"ga_select_first\", \"ga_select_rest\",
     \"ga_select_x\", \"ga_select_y\", \"ga_select_z\",
     \"ga_select_x_1\", \"ga_select_y_1\", \"ga_select_z_1\",
     \"ga_select_SpacePoint\", \"ga_select_NormalVector\",
     \"ga_select_InnerCS\", \"ga_select_Center\", \"ga_select_Start\",
     \"ga_select_End\", \"ga_select_From\", \"ga_select_To\",
     \"ga_select_Points\", \"ga_select_Objects\", \"ga_select_Plane\",
     \"ga_select_Sketch\", \"ga_select_Depth\",
     \"ga_select_DraftAngle\", \"ga_select_DraftOutward\",
     \"ga_select_DraftWhileExtruding\", \"ga_select_EndCondition\",
     \"ga_select_WallThickness\", \"ga_select_IsBaseExtrude\",
     \"ga_select_IsBossFeature\", \"ga_select_IsThinFeature\",
     \"E1_def\", \"E2_def\", \"E3_def\", \"VLine_constr\",
     \"VWithLength_constr\", \"VPlane_constr\", \"VPlane2_constr\",
     \"VConnected_constr\", \"VHalfSpace_constr\",
     \"VHalfSpace2_constr\", \"VBall_constr\", \"VCircle_constr\",
     \"ActAttach_constr\", \"ActExtrude_constr\", \"vwl_length\",
     \"vwl_colin\", \"semantics_for_SWPoint\",
     \"semantics_for_SWVector\", \"semantics_for_Planes\",
     \"semantics_for_ArcExtrusion\", \"help4\", \"help5\", \"help6\",
     \"help7\", \"plane_is_plane\", \"def_of_given_arc\",
     \"cylinder_offset\", \"cylinder_radius\", \"cylinder_axis\",
     \"real_extrusion\", \"real_arc\", \"real_plane\",
     \"the_arc_is_wellformed\", \"extrusion_is_cylinder\"]"

typedecl Direction
typedecl NonZero
typedecl PointSet
typedecl Real
typedecl RealPos
typedecl RealSet
typedecl SWArc
typedecl SWExtrusion
typedecl SWFeature
typedecl SWLine
typedecl SWObject
typedecl SWPlane
typedecl SWPoint
typedecl SWSketch
typedecl SWSketchObject
typedecl SWSpline
typedecl SWVector
typedecl ('a1) Set
typedecl VectorSet
typedecl ZeroToNine

datatype Point = X_P "Real" "Real" "Real" ("P/'(_,/ _,/ _')" [3,3,3] 999)
datatype Vector = X_V "Real" "Real" "Real" ("V/'(_,/ _,/ _')" [3,3,3] 999)
datatype 'a SWList = XOSqBrXCSqBr ("[/ ]''") | X__XColonXColon__X 'a "'a SWList" ("(_/ ::''/ _)" [54,54] 52)

consts
ActAttach :: "Point * (Vector => bool) => Point => bool"
ActExtrude :: "Vector * (Point => bool) => Point => bool"
C1X1 :: "Point => Real" ("C1''/'(_')" [3] 999)
C1X2 :: "Vector => Real" ("C1''''/'(_')" [3] 999)
C2X1 :: "Point => Real" ("C2''/'(_')" [3] 999)
C2X2 :: "Vector => Real" ("C2''''/'(_')" [3] 999)
C3X1 :: "Point => Real" ("C3''/'(_')" [3] 999)
C3X2 :: "Vector => Real" ("C3''''/'(_')" [3] 999)
Circle :: "(Point * Real) * Vector => Point => bool"
Cylinder :: "(Point * Real) * Vector => Point => bool"
Cylinder1 :: "(Point * Real) * Vector => Point => bool"
E1 :: "SWPlane"
E2 :: "SWPlane"
E3 :: "SWPlane"
PlaneX1 :: "SWSketch => SWPlane" ("Plane''/'(_')" [3] 999)
PlaneX2 :: "Point * Vector => Point => bool"
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
X_Center :: "SWArc => SWPoint" ("Center/'(_')" [3] 999)
X_Depth :: "SWExtrusion => Real" ("Depth/'(_')" [3] 999)
X_DraftAngle :: "SWExtrusion => Real" ("DraftAngle/'(_')" [3] 999)
X_DraftOutward :: "SWExtrusion => bool" ("DraftOutward/'(_')" [3] 999)
X_DraftWhileExtruding :: "SWExtrusion => bool" ("DraftWhileExtruding/'(_')" [3] 999)
X_End :: "SWArc => SWPoint" ("End/'(_')" [3] 999)
X_EndCondition :: "SWExtrusion => Real" ("EndCondition/'(_')" [3] 999)
X_From :: "SWLine => SWPoint" ("From/'(_')" [3] 999)
X_InnerCS :: "SWPlane => SWVector" ("InnerCS/'(_')" [3] 999)
X_IsBaseExtrude :: "SWExtrusion => bool" ("IsBaseExtrude/'(_')" [3] 999)
X_IsBossFeature :: "SWExtrusion => bool" ("IsBossFeature/'(_')" [3] 999)
X_IsThinFeature :: "SWExtrusion => bool" ("IsThinFeature/'(_')" [3] 999)
X_NormalVector :: "SWPlane => SWVector" ("NormalVector/'(_')" [3] 999)
X_Objects :: "SWSketch => SWSketchObject SWList" ("Objects/'(_')" [3] 999)
X_Points :: "SWSpline => SWPoint SWList" ("Points/'(_')" [3] 999)
X_Pos :: "Real => bool" ("Pos/'(_')" [3] 999)
X_SWArc :: "SWPoint => SWPoint => SWPoint => SWArc"
X_SWExtrusion :: "SWSketch => Real => Real => bool => bool => Real => Real => bool => bool => bool => SWExtrusion"
X_SWLine :: "SWPoint => SWPoint => SWLine"
X_SWPlane :: "SWPoint => SWVector => SWVector => SWPlane"
X_SWPoint :: "Real => Real => Real => SWPoint"
X_SWReal :: "Real => Real => Real" ("SWReal/'(_,/ _')" [3,3] 999)
X_SWSketch :: "SWSketchObject SWList => SWPlane => SWSketch"
X_SWSpline :: "SWPoint SWList => SWSpline"
X_SWVector :: "Real => Real => Real => SWVector"
X_Sketch :: "SWExtrusion => SWSketch" ("Sketch/'(_')" [3] 999)
X_SpacePoint :: "SWPlane => SWPoint" ("SpacePoint/'(_')" [3] 999)
X_Start :: "SWArc => SWPoint" ("Start/'(_')" [3] 999)
X_To :: "SWLine => SWPoint" ("To/'(_')" [3] 999)
X_VWithLength :: "Vector => Real => Vector" ("VWithLength/'(_,/ _')" [3,3] 999)
X_WallThickness :: "SWExtrusion => Real" ("WallThickness/'(_')" [3] 999)
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
X_abs :: "Real => RealPos" ("abs''/'(_')" [3] 999)
X_allSet :: "'S => bool" ("allSet/'(_')" [3] 999)
X_asPoint :: "Vector => Point" ("asPoint/'(_')" [3] 999)
X_asVector :: "Point => Vector" ("asVector/'(_')" [3] 999)
X_colin :: "Vector => Vector => bool" ("colin/'(_,/ _')" [3,3] 999)
X_emptySet :: "'S => bool" ("emptySet/'(_')" [3] 999)
X_first :: "'a SWList => 'a partial" ("first/'(_')" [3] 999)
X_gn_inj :: "'a => 'b" ("gn'_inj/'(_')" [3] 999)
X_gn_proj :: "'a => 'b partial" ("gn'_proj/'(_')" [3] 999)
X_image :: "('S => 'T) * ('S => bool) => 'T => bool"
X_inv :: "NonZero => NonZero" ("inv''/'(_')" [3] 999)
X_ip :: "SWPoint => Point" ("ip/'(_')" [3] 999)
X_iv :: "SWVector => Vector" ("iv/'(_')" [3] 999)
X_max :: "Real => Real => Real" ("max''/'(_,/ _')" [3,3] 999)
X_min :: "Real => Real => Real" ("min''/'(_,/ _')" [3,3] 999)
X_orth :: "Vector => Vector => bool" ("orth/'(_,/ _')" [3,3] 999)
X_rest :: "'a SWList => 'a SWList partial" ("rest/'(_')" [3] 999)
X_sqrt :: "RealPos => Real" ("sqrt/'(_')" [3] 999)
X_sup :: "Real => Real => Real partial" ("sup/'(_,/ _')" [3,3] 999)
X_vec :: "Point => Point => Vector" ("vec/'(_,/ _')" [3,3] 999)
arc :: "SWArc"
axis :: "Vector"
b1 :: "bool"
b2 :: "bool"
b3 :: "bool"
b4 :: "bool"
b5 :: "bool"
bigunion :: "(('S => bool) => bool) => 'S => bool"
boundarypoint :: "SWPoint"
center :: "SWPoint"
height :: "Real"
iX1 :: "SWFeature => Point => bool"
iX2 :: "SWPlane => Point => bool"
infX1 :: "Real => Real => Real partial" ("inf''/'(_,/ _')" [3,3] 999)
infX2 :: "(Real => bool) => Real partial" ("inf''''/'(_')" [3] 999)
offset :: "Point"
plane :: "SWPlane"
radius :: "Real"
sqrX1 :: "Real => RealPos" ("sqr''/'(_')" [3] 999)
sqrX2 :: "Vector => RealPos" ("sqr''''/'(_')" [3] 999)
x1 :: "Real"
x2 :: "Real"
x3 :: "Real"
xX1 :: "SWPoint => Real" ("x''/'(_')" [3] 999)
xX2 :: "SWVector => Real" ("x''''/'(_')" [3] 999)
yX1 :: "SWPoint => Real" ("y''/'(_')" [3] 999)
yX2 :: "SWVector => Real" ("y''''/'(_')" [3] 999)
zX1 :: "SWPoint => Real" ("z''/'(_')" [3] 999)
zX2 :: "SWVector => Real" ("z''''/'(_')" [3] 999)

axioms
inv_Group [rule_format] : "ALL X_x. -' X_x +_3 X_x = 0''"

rinv_Group [rule_format] : "ALL X_x. X_x +_3 -' X_x = 0''"

distr1_Ring [rule_format] :
"ALL X_x.
 ALL X_y.
 ALL X_z. (X_x +_3 X_y) *'' X_z = (X_x *'' X_z) +_3 (X_y *'' X_z)"

distr2_Ring [rule_format] :
"ALL X_x.
 ALL X_y.
 ALL X_z. X_z *'' (X_x +_3 X_y) = (X_z *'' X_x) +_3 (X_z *'' X_y)"

noZeroDiv [rule_format] :
"ALL X_x. ALL X_y. X_x *'' X_y = 0'' --> X_x = 0'' | X_y = 0''"

zeroNeqOne [rule_format] : "~ 1'' = 0''"

Ax1 [rule_format] : "ALL X_x. defOp (gn_proj(X_x)) = (~ X_x = 0'')"

inv_Group_1 [rule_format] : "ALL X_x. inv'(X_x) *' X_x = 1'"

rinv_Group_1 [rule_format] : "ALL X_x. X_x *' inv'(X_x) = 1'"

binary_inverse [rule_format] :
"ALL X_x. ALL X_y. X_x -' X_y = X_x +_3 -' X_y"

Ax1_1 [rule_format] :
"ALL X_x. ALL X_y. X_x /' X_y = X_x *'' gn_inj(inv'(X_y))"

refl [rule_format] : "ALL X_x. X_x <=' X_x"

trans [rule_format] :
"ALL X_x.
 ALL X_y. ALL X_z. X_x <=' X_y & X_y <=' X_z --> X_x <=' X_z"

antisym [rule_format] :
"ALL X_x. ALL X_y. X_x <=' X_y & X_y <=' X_x --> X_x = X_y"

dichotomy_TotalOrder [rule_format] :
"ALL X_x. ALL X_y. X_x <=' X_y | X_y <=' X_x"

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
 (ALL m2. (ALL X_x. S X_x --> X_x <=' m2) --> m <=' m2)"

Real_completeness [rule_format] :
"ALL S.
 (EX X_x. S X_x) & (EX B. ALL X_x. S X_x --> X_x <=' B) -->
 (EX m. makePartial m = inf''(S))"

geq_def_ExtPartialOrder [rule_format] :
"ALL X_x. ALL X_y. (X_x >=' X_y) = (X_y <=' X_x)"

less_def_ExtPartialOrder [rule_format] :
"ALL X_x. ALL X_y. (X_x <' X_y) = (X_x <=' X_y & ~ X_x = X_y)"

greater_def_ExtPartialOrder [rule_format] :
"ALL X_x. ALL X_y. (X_x >' X_y) = (X_y <' X_x)"

ga_comm_inf [rule_format] :
"ALL X_x. ALL X_y. inf'(X_x, X_y) = inf'(X_y, X_x)"

ga_comm_sup [rule_format] :
"ALL X_x. ALL X_y. sup(X_x, X_y) = sup(X_y, X_x)"

inf_def_ExtPartialOrder [rule_format] :
"ALL X_x.
 ALL X_y.
 ALL X_z.
 inf'(X_x, X_y) = makePartial X_z =
 (X_z <=' X_x &
  X_z <=' X_y & (ALL t. t <=' X_x & t <=' X_y --> t <=' X_z))"

sup_def_ExtPartialOrder [rule_format] :
"ALL X_x.
 ALL X_y.
 ALL X_z.
 sup(X_x, X_y) = makePartial X_z =
 (X_x <=' X_z &
  X_y <=' X_z & (ALL t. X_x <=' t & X_y <=' t --> X_z <=' t))"

ga_comm_min [rule_format] :
"ALL X_x. ALL X_y. min'(X_x, X_y) = min'(X_y, X_x)"

ga_comm_max [rule_format] :
"ALL X_x. ALL X_y. max'(X_x, X_y) = max'(X_y, X_x)"

ga_assoc_min [rule_format] :
"ALL X_x.
 ALL X_y.
 ALL X_z. min'(min'(X_x, X_y), X_z) = min'(X_x, min'(X_y, X_z))"

ga_assoc_max [rule_format] :
"ALL X_x.
 ALL X_y.
 ALL X_z. max'(max'(X_x, X_y), X_z) = max'(X_x, max'(X_y, X_z))"

ga_left_comm_min [rule_format] :
"ALL X_x.
 ALL X_y.
 ALL X_z. min'(X_x, min'(X_y, X_z)) = min'(X_y, min'(X_x, X_z))"

ga_left_comm_max [rule_format] :
"ALL X_x.
 ALL X_y.
 ALL X_z. max'(X_x, max'(X_y, X_z)) = max'(X_y, max'(X_x, X_z))"

min_def_ExtTotalOrder [rule_format] :
"ALL X_x.
 ALL X_y. min'(X_x, X_y) = (if X_x <=' X_y then X_x else X_y)"

max_def_ExtTotalOrder [rule_format] :
"ALL X_x.
 ALL X_y. max'(X_x, X_y) = (if X_x <=' X_y then X_y else X_x)"

min_inf_relation [rule_format] :
"ALL X_x. ALL X_y. makePartial (min'(X_x, X_y)) = inf'(X_x, X_y)"

max_sup_relation [rule_format] :
"ALL X_x. ALL X_y. makePartial (max'(X_x, X_y)) = sup(X_x, X_y)"

Ax1_3 [rule_format] :
"ALL X_x. defOp (gn_proj(X_x)) = (X_x >=' 0'')"

Ax2 [rule_format] :
"ALL X_x.
 makePartial (abs'(X_x)) =
 gn_proj(makeTotal
         (makePartial (if 0'' <=' X_x then X_x else -' X_x)))"

sqr_def [rule_format] :
"ALL r. gn_inj(sqr'(r)) = makePartial (r *'' r)"

sqrt_def [rule_format] : "ALL q. sqr'(sqrt(q)) = q"

Ax1_2_1 [rule_format] : "ALL X_x. Pos(X_x) = (0'' <=' X_x)"

X2_def_Real [rule_format] : "2' = gn_inj(1') +_3 gn_inj(1')"

X3_def_Real [rule_format] : "3' = 2' +_3 gn_inj(1')"

X4_def_Real [rule_format] : "4' = 3' +_3 gn_inj(1')"

X5_def_Real [rule_format] : "5' = 4' +_3 gn_inj(1')"

X6_def_Real [rule_format] : "6' = 5' +_3 gn_inj(1')"

X7_def_Real [rule_format] : "7' = 6' +_3 gn_inj(1')"

X8_def_Real [rule_format] : "8' = 7' +_3 gn_inj(1')"

X9_def_Real [rule_format] : "9' = 8' +_3 gn_inj(1')"

ZeroToNine_type [rule_format] :
"ALL X_x.
 defOp (gn_proj(X_x)) =
 (((((((((X_x = 0'' | makePartial X_x = gn_inj(1')) | X_x = 2') |
        X_x = 3') |
       X_x = 4') |
      X_x = 5') |
     X_x = 6') |
    X_x = 7') |
   X_x = 8') |
  X_x = 9')"

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

ga_select_C1_1 [rule_format] :
"ALL x_1. ALL x_2. ALL x_3. C1''(V(x_1, x_2, x_3)) = x_1"

ga_select_C2_1 [rule_format] :
"ALL x_1. ALL x_2. ALL x_3. C2''(V(x_1, x_2, x_3)) = x_2"

ga_select_C3_1 [rule_format] :
"ALL x_1. ALL x_2. ALL x_3. C3''(V(x_1, x_2, x_3)) = x_3"

Zero_Vector [rule_format] : "0_3 = V(0'', 0'', 0'')"

def_of_vector_addition [rule_format] :
"ALL X_x.
 ALL X_y.
 X_x +_4 X_y =
 V(C1''(X_x) +_3 C1''(X_y), C2''(X_x) +_3 C2''(X_y),
 C3''(X_x) +_3 C3''(X_y))"

def_of_minus_vector [rule_format] :
"ALL X_x. -'' X_x = V(-' C1''(X_x), -' C2''(X_x), -' C3''(X_x))"

binary_inverse_1_1 [rule_format] :
"ALL X_x. ALL X_y. X_x -'' X_y = X_x +_4 -'' X_y"

scalar_mutliplication [rule_format] :
"ALL X_x.
 ALL X_y.
 X_x *_3 X_y =
 V(X_x *'' C1''(X_y), X_x *'' C2''(X_y), X_x *'' C3''(X_y))"

scalar_product [rule_format] :
"ALL X_x.
 ALL X_y.
 X_x *_4 X_y =
 ((C1''(X_x) *'' C1''(X_y)) +_3 (C2''(X_x) *'' C2''(X_y))) +_3
 (C3''(X_x) *'' C3''(X_y))"

vector_product [rule_format] :
"ALL X_x.
 ALL X_y.
 X_x #' X_y =
 V((C2''(X_x) *'' C3''(X_y)) -' (C2''(X_y) *'' C3''(X_x)),
 (C3''(X_x) *'' C1''(X_y)) -' (C3''(X_y) *'' C1''(X_x)),
 (C1''(X_x) *'' C2''(X_y)) -' (C1''(X_y) *'' C2''(X_x)))"

cross_left_homogenity [rule_format] :
"ALL r. ALL X_x. ALL X_y. r *_3 (X_x #' X_y) = (r *_3 X_x) #' X_y"

cross_product_antisymmetric [rule_format] :
"ALL X_x. ALL X_y. X_x #' X_y = -'' (X_y #' X_x)"

inv_Group_2_1 [rule_format] : "ALL X_x. -'' X_x +_4 X_x = 0_3"

rinv_Group_2_1 [rule_format] : "ALL X_x. X_x +_4 -'' X_x = 0_3"

mix_assoc [rule_format] :
"ALL r. ALL s. ALL X_x. (r *'' s) *_3 X_x = r *_3 (s *_3 X_x)"

distr_Field [rule_format] :
"ALL r.
 ALL s. ALL X_x. (r +_3 s) *_3 X_x = (r *_3 X_x) +_4 (s *_3 X_x)"

distr_Space [rule_format] :
"ALL r.
 ALL X_x.
 ALL X_y. r *_3 (X_x +_4 X_y) = (r *_3 X_x) +_4 (r *_3 X_y)"

distributiv [rule_format] :
"ALL v. ALL v'. ALL w. (v +_4 v') *_4 w = (v *_4 w) +_3 (v' *_4 w)"

homogen [rule_format] :
"ALL a. ALL v. ALL w. (a *_3 v) *_4 w = a *'' (v *_4 w)"

commutativ [rule_format] : "ALL v. ALL w. v *_4 w = w *_4 v"

pos_definit [rule_format] : "ALL v. v *_4 v = 0'' --> v = 0_3"

right_distributiv [rule_format] :
"ALL v. ALL v'. ALL w. w *_4 (v +_4 v') = (w *_4 v) +_3 (w *_4 v')"

right_homogen [rule_format] :
"ALL a. ALL v. ALL w. v *_4 (a *_3 w) = a *'' (v *_4 w)"

colin_def [rule_format] :
"ALL X_x.
 ALL X_y. colin(X_x, X_y) = (X_y = 0_3 | (EX r. X_x = r *_3 X_y))"

colin_reflexivity [rule_format] : "ALL X_x. colin(X_x, X_x)"

colin_symmetry [rule_format] :
"ALL X_x. ALL X_y. colin(X_x, X_y) --> colin(X_y, X_x)"

simple_colin_condition [rule_format] :
"ALL r. ALL X_x. ALL X_y. X_x = r *_3 X_y --> colin(X_x, X_y)"

sqr_def_1_1 [rule_format] :
"ALL X_x. makePartial (sqr''(X_x)) = gn_proj(X_x *_4 X_x)"

norm_from_scalar_prod_def [rule_format] :
"ALL X_x. || X_x || = sqrt(sqr''(X_x))"

orthogonal_def [rule_format] :
"ALL X_x. ALL X_y. orth(X_x, X_y) = (X_x *_4 X_y = 0'')"

orth_symmetry [rule_format] :
"ALL X_x. ALL X_y. orth(X_x, X_y) --> orth(X_y, X_x)"

colin_orth_transitivity [rule_format] :
"ALL X_x.
 ALL X_y.
 ALL X_z. colin(X_x, X_y) & orth(X_y, X_z) --> orth(X_x, X_z)"

cross_product_orthogonal [rule_format] :
"ALL X_x. ALL X_y. orth(X_x, X_x #' X_y)"

cross_product_zero_iff_colinear [rule_format] :
"ALL X_x. ALL X_y. colin(X_x, X_y) = (X_x #' X_y = 0_3)"

point_to_vector_embedding [rule_format] :
"ALL p. asVector(p) = V(C1'(p), C2'(p), C3'(p))"

vector_to_point_embedding [rule_format] :
"ALL v. asPoint(v) = P(C1''(v), C2''(v), C3''(v))"

Ax1_1_1 [rule_format] : "0' = asPoint(0_3)"

vector_point_vector [rule_format] :
"ALL v. asVector(asPoint(v)) = v"

point_vector_point [rule_format] :
"ALL p. asPoint(asVector(p)) = p"

origin_to_zero [rule_format] : "asVector(0') = 0_3"

vec_def [rule_format] :
"ALL p. ALL q. vec(p, q) = asVector(q) -'' asVector(p)"

compatibility_PVplus_Vplus [rule_format] :
"ALL p. ALL v. p +' v = asPoint(asVector(p) +_4 v)"

transitivity_of_vec_XPlus [rule_format] :
"ALL p. ALL q. ALL r. vec(p, q) +_4 vec(q, r) = vec(p, r)"

antisymmetry_of_vec [rule_format] :
"ALL p. ALL q. vec(p, q) = -'' vec(q, p)"

vec_shift_unique_lemma [rule_format] :
"ALL p. ALL q. ALL v. p +' v = q --> v = vec(p, q)"

vec_shift_def_lemma [rule_format] :
"ALL p. ALL q. p +' vec(p, q) = q"

point_vector_add_comm_lemma [rule_format] :
"ALL p. ALL v. ALL w. (p +' v) +' w = (p +' w) +' v"

set_comprehension [rule_format] : "ALL s. XLBrace__XRBrace s = s"

function_image [rule_format] :
"ALL XX.
 ALL f.
 X_image (f, XX) =
 XLBrace__XRBrace (% X_x. EX X_y. X_y isIn XX & f X_y = X_x)"

emptySet_not_empty [rule_format] : "ALL X_x. ~ X_x isIn X_emptySet"

allSet_contains_all [rule_format] : "ALL X_x. X_x isIn X_allSet"

def_of_isIn [rule_format] : "ALL s. ALL X_x. (X_x isIn s) = s X_x"

def_of_subset [rule_format] :
"ALL s.
 ALL s'. (s subset s') = (ALL X_x. X_x isIn s --> X_x isIn s')"

def_of_union [rule_format] :
"ALL s.
 ALL s'.
 ALL X_x.
 (X_x isIn X__union__X (s, s')) = (X_x isIn s | X_x isIn s')"

def_of_bigunion [rule_format] :
"ALL XXXX.
 ALL X_x.
 (X_x isIn bigunion XXXX) = (EX XX. XX isIn XXXX & X_x isIn XX)"

def_of_intersection [rule_format] :
"ALL s.
 ALL s'.
 ALL X_x.
 (X_x isIn X__intersection__X (s, s')) = (X_x isIn s & X_x isIn s')"

def_of_difference [rule_format] :
"ALL s.
 ALL s'.
 ALL X_x.
 (X_x isIn X__XBslashXBslash__X (s, s')) =
 (X_x isIn s & ~ X_x isIn s')"

def_of_disjoint [rule_format] :
"ALL s.
 ALL s'.
 (s disjoint s') = (X__intersection__X (s, s') = X_emptySet)"

def_of_productset [rule_format] :
"ALL s.
 ALL t.
 ALL X_x.
 ALL X_y.
 ((X_x, X_y) isIn X__Xx__XX5 (s, t)) = (X_x isIn s & X_y isIn t)"

def_of_interval [rule_format] :
"ALL a.
 ALL b.
 XOSqBr__XPeriodXPeriodXPeriod__XCSqBr (a, b) =
 (% r. r >=' a & r <=' b)"

plus_PointSet_Vector [rule_format] :
"ALL X_P.
 ALL v. X__XPlus__XX5 (X_P, v) = X_image (% X_x. X_x +' v, X_P)"

plus_Point_VectorSet [rule_format] :
"ALL X_V.
 ALL p. X__XPlus__XX2 (p, X_V) = X_image (% X_x. p +' X_x, X_V)"

plus_PointSet_VectorSet [rule_format] :
"ALL X_P.
 ALL X_V.
 X__XPlus__XX6 (X_P, X_V) =
 bigunion (X_image (% X_x. X__XPlus__XX5 (X_P, X_x), X_V))"

def_of_Plane [rule_format] :
"ALL normal.
 ALL X_offset.
 PlaneX2 (X_offset, normal) =
 XLBrace__XRBrace (% X_x. orth(vec(X_x, X_offset), normal))"

def_of_Circle [rule_format] :
"ALL X_offset.
 ALL orientation.
 ALL r.
 Circle ((X_offset, r), orientation) =
 XLBrace__XRBrace
 (% X_x. EX X_y.
         (orth(X_y, orientation) & || X_y || <=' r) &
         X_x = X_offset +' X_y)"

def_of_Cylinder [rule_format] :
"ALL X_axis.
 ALL X_offset.
 ALL r.
 Cylinder ((X_offset, r), X_axis) =
 XLBrace__XRBrace
 (% X_x. EX l.
         EX X_y.
         ((l isIn XOSqBr__XPeriodXPeriodXPeriod__XCSqBr (0'', gn_inj(1')) &
           orth(X_y, X_axis)) &
          || X_y || <=' r) &
         X_x = (X_offset +' (l *_3 X_axis)) +' X_y)"

def_of_Cylinder1 [rule_format] :
"ALL X_axis.
 ALL X_offset.
 ALL r.
 Cylinder1 ((X_offset, r), X_axis) =
 XLBrace__XRBrace
 (% X_x. EX l.
         EX X_y.
         ((l isIn XOSqBr__XPeriodXPeriodXPeriod__XCSqBr (0'', gn_inj(1')) &
           orth(X_y, X_axis)) &
          || X_y || <=' r) &
         X_x = (X_offset +' (l *_3 X_axis)) +' X_y)"

plane_condition_for_2_points [rule_format] :
"ALL normal.
 ALL X_offset.
 ALL X_x.
 ALL X_y.
 let X_plane = PlaneX2 (X_offset, normal)
 in X_x isIn X_plane & X_y isIn X_plane -->
    orth(vec(X_x, X_y), normal)"

direction_subtype [rule_format] :
"ALL X_x.
 defOp (gn_proj(X_x)) =
 (makePartial X_x = gn_inj(1') | X_x = -' gn_inj(1'))"

ga_select_first [rule_format] :
"ALL x_1. ALL x_2. first(x_1 ::' x_2) = makePartial x_1"

ga_select_rest [rule_format] :
"ALL x_1. ALL x_2. rest(x_1 ::' x_2) = makePartial x_2"

ga_select_x [rule_format] :
"ALL x_1. ALL x_2. ALL x_3. x''(X_SWVector x_1 x_2 x_3) = x_1"

ga_select_y [rule_format] :
"ALL x_1. ALL x_2. ALL x_3. y''(X_SWVector x_1 x_2 x_3) = x_2"

ga_select_z [rule_format] :
"ALL x_1. ALL x_2. ALL x_3. z''(X_SWVector x_1 x_2 x_3) = x_3"

ga_select_x_1 [rule_format] :
"ALL x_1. ALL x_2. ALL x_3. x'(X_SWPoint x_1 x_2 x_3) = x_1"

ga_select_y_1 [rule_format] :
"ALL x_1. ALL x_2. ALL x_3. y'(X_SWPoint x_1 x_2 x_3) = x_2"

ga_select_z_1 [rule_format] :
"ALL x_1. ALL x_2. ALL x_3. z'(X_SWPoint x_1 x_2 x_3) = x_3"

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
"ALL x_1.
 ALL x_2.
 ALL x_3.
 ALL x_4.
 ALL x_5.
 ALL x_6.
 ALL x_7.
 ALL x_8.
 ALL x_9.
 ALL x_10.
 Sketch(X_SWExtrusion x_1 x_2 x_3 x_4 x_5 x_6 x_7 x_8 x_9 x_10) =
 x_1"

ga_select_Depth [rule_format] :
"ALL x_1.
 ALL x_2.
 ALL x_3.
 ALL x_4.
 ALL x_5.
 ALL x_6.
 ALL x_7.
 ALL x_8.
 ALL x_9.
 ALL x_10.
 Depth(X_SWExtrusion x_1 x_2 x_3 x_4 x_5 x_6 x_7 x_8 x_9 x_10) =
 x_2"

ga_select_DraftAngle [rule_format] :
"ALL x_1.
 ALL x_2.
 ALL x_3.
 ALL x_4.
 ALL x_5.
 ALL x_6.
 ALL x_7.
 ALL x_8.
 ALL x_9.
 ALL x_10.
 DraftAngle(X_SWExtrusion x_1 x_2 x_3 x_4 x_5 x_6 x_7 x_8 x_9
            x_10) =
 x_3"

ga_select_DraftOutward [rule_format] :
"ALL x_1.
 ALL x_2.
 ALL x_3.
 ALL x_4.
 ALL x_5.
 ALL x_6.
 ALL x_7.
 ALL x_8.
 ALL x_9.
 ALL x_10.
 DraftOutward(X_SWExtrusion x_1 x_2 x_3 x_4 x_5 x_6 x_7 x_8 x_9
              x_10) =
 x_4"

ga_select_DraftWhileExtruding [rule_format] :
"ALL x_1.
 ALL x_2.
 ALL x_3.
 ALL x_4.
 ALL x_5.
 ALL x_6.
 ALL x_7.
 ALL x_8.
 ALL x_9.
 ALL x_10.
 DraftWhileExtruding(X_SWExtrusion x_1 x_2 x_3 x_4 x_5 x_6 x_7 x_8
                     x_9 x_10) =
 x_5"

ga_select_EndCondition [rule_format] :
"ALL x_1.
 ALL x_2.
 ALL x_3.
 ALL x_4.
 ALL x_5.
 ALL x_6.
 ALL x_7.
 ALL x_8.
 ALL x_9.
 ALL x_10.
 EndCondition(X_SWExtrusion x_1 x_2 x_3 x_4 x_5 x_6 x_7 x_8 x_9
              x_10) =
 x_6"

ga_select_WallThickness [rule_format] :
"ALL x_1.
 ALL x_2.
 ALL x_3.
 ALL x_4.
 ALL x_5.
 ALL x_6.
 ALL x_7.
 ALL x_8.
 ALL x_9.
 ALL x_10.
 WallThickness(X_SWExtrusion x_1 x_2 x_3 x_4 x_5 x_6 x_7 x_8 x_9
               x_10) =
 x_7"

ga_select_IsBaseExtrude [rule_format] :
"ALL x_1.
 ALL x_2.
 ALL x_3.
 ALL x_4.
 ALL x_5.
 ALL x_6.
 ALL x_7.
 ALL x_8.
 ALL x_9.
 ALL x_10.
 IsBaseExtrude(X_SWExtrusion x_1 x_2 x_3 x_4 x_5 x_6 x_7 x_8 x_9
               x_10) =
 x_8"

ga_select_IsBossFeature [rule_format] :
"ALL x_1.
 ALL x_2.
 ALL x_3.
 ALL x_4.
 ALL x_5.
 ALL x_6.
 ALL x_7.
 ALL x_8.
 ALL x_9.
 ALL x_10.
 IsBossFeature(X_SWExtrusion x_1 x_2 x_3 x_4 x_5 x_6 x_7 x_8 x_9
               x_10) =
 x_9"

ga_select_IsThinFeature [rule_format] :
"ALL x_1.
 ALL x_2.
 ALL x_3.
 ALL x_4.
 ALL x_5.
 ALL x_6.
 ALL x_7.
 ALL x_8.
 ALL x_9.
 ALL x_10.
 IsThinFeature(X_SWExtrusion x_1 x_2 x_3 x_4 x_5 x_6 x_7 x_8 x_9
               x_10) =
 x_10"

E1_def [rule_format] :
"E1 =
 X_SWPlane (X_SWPoint 0'' 0'' 0'') (X_SWVector 0'' 0'' (gn_inj(1')))
 (X_SWVector (gn_inj(1')) 0'' 0'')"

E2_def [rule_format] :
"E2 =
 X_SWPlane (X_SWPoint 0'' 0'' 0'') (X_SWVector 0'' (gn_inj(1')) 0'')
 (X_SWVector (gn_inj(1')) 0'' 0'')"

E3_def [rule_format] :
"E3 =
 X_SWPlane (X_SWPoint 0'' 0'' 0'') (X_SWVector (gn_inj(1')) 0'' 0'')
 (X_SWVector 0'' (gn_inj(1')) 0'')"

VLine_constr [rule_format] :
"ALL p1.
 ALL p2.
 VLine (p1, p2) =
 X_image
 (% X_y. p1 +_4 (X_y *_3 (p2 -'' p1)),
  XOSqBr__XPeriodXPeriodXPeriod__XCSqBr (0'', gn_inj(1')))"

VWithLength_constr [rule_format] :
"ALL s.
 ALL v.
 makePartial (VWithLength(v, s)) =
 (if v = 0_3 then makePartial v
     else restrictOp
          (makePartial ((s /' makeTotal (gn_proj( || v || ))) *_3 v))
          (defOp (gn_proj( || v || ))))"

VPlane_constr [rule_format] :
"ALL normal.
 VPlane normal = XLBrace__XRBrace (% X_y. orth(X_y, normal))"

VPlane2_constr [rule_format] :
"ALL axis1.
 ALL axis2. VPlane2 (axis1, axis2) = VPlane (axis1 #' axis2)"

VConnected_constr [rule_format] :
"ALL frontier.
 ALL point.
 VConnected (frontier, point) =
 (if frontier point then frontier
     else XLBrace__XRBrace
          (% X_y. X__intersection__X (VLine (point, X_y), frontier) =
                  X_emptySet))"

VHalfSpace_constr [rule_format] :
"ALL normal.
 VHalfSpace normal = VConnected (VPlane normal, normal)"

VHalfSpace2_constr [rule_format] :
"ALL normal.
 VHalfSpace2 normal =
 X__union__X (VConnected (VPlane normal, normal), VPlane normal)"

VBall_constr [rule_format] :
"ALL r. VBall r = XLBrace__XRBrace (% X_y. || X_y || <=' r)"

VCircle_constr [rule_format] :
"ALL X_axis.
 ALL r.
 VCircle (r, X_axis) = X__intersection__X (VPlane X_axis, VBall r)"

ActAttach_constr [rule_format] :
"ALL point.
 ALL vectors.
 ActAttach (point, vectors) = X__XPlus__XX2 (point, vectors)"

ActExtrude_constr [rule_format] :
"ALL X_axis.
 ALL points.
 ActExtrude (X_axis, points) =
 XLBrace__XRBrace
 (% X_x. EX l.
         EX X_y.
         (l isIn XOSqBr__XPeriodXPeriodXPeriod__XCSqBr (0'', gn_inj(1')) &
          X_y isIn points) &
         X_x = X_y +' (l *_3 X_axis))"

vwl_length [rule_format] :
"ALL s.
 ALL v.
 ~ v = 0_3 -->
 makePartial ( || VWithLength(v, s) || ) = gn_inj(abs'(s))"

vwl_colin [rule_format] :
"ALL s. ALL v. colin(v, VWithLength(v, s))"

semantics_for_SWPoint [rule_format] :
"ALL point. ip(point) = P(x'(point), y'(point), z'(point))"

semantics_for_SWVector [rule_format] :
"ALL vector. iv(vector) = V(x''(vector), y''(vector), z''(vector))"

semantics_for_Planes [rule_format] :
"ALL ics.
 ALL X_n.
 ALL X_o.
 iX2 (X_SWPlane X_o X_n ics) =
 ActAttach (ip(X_o), VPlane (iv(X_n)))"

semantics_for_ArcExtrusion [rule_format] :
"ALL X_b1.
 ALL X_b2.
 ALL X_b3.
 ALL X_b4.
 ALL X_b5.
 ALL l.
 ALL X_plane.
 ALL X_x.
 ALL X_x1.
 ALL X_x2.
 ALL X_x3.
 ALL X_y.
 ALL X_z.
 iX1
 (gn_inj(X_SWExtrusion
         (X_SWSketch (gn_inj(X_SWArc X_x X_y X_z) ::' [ ]') X_plane) l X_x1
         X_b1 X_b2 X_x2 X_x3 X_b3 X_b4 X_b5)) =
 (if X_y = X_z
     then let cp = ip(X_x);
              r1 = vec(cp, ip(X_y));
              ball = ActAttach (cp, VBall ( || r1 || ));
              planeI = iX2 X_plane;
              scaledAxis = VWithLength(iv(NormalVector(X_plane)), l)
          in ActExtrude (scaledAxis, X__intersection__X (ball, planeI))
     else X_emptySet)"

help4 [rule_format] :
"ALL pl1.
 ALL po1.
 ALL po2.
 let pl = iX2 pl1
 in po1 isIn pl & po2 isIn pl -->
    orth(iv(NormalVector(pl1)), vec(po1, po2))"

help5 [rule_format] :
"ALL A.
 ALL Q. (let a = A in % b. Q a b) = (% b. let a = A in Q a b)"

help6 [rule_format] :
"ALL pl1.
 pl1 =
 X_SWPlane (SpacePoint(pl1)) (NormalVector(pl1)) (InnerCS(pl1))"

help7 [rule_format] :
"ALL pl1.
 ALL po1.
 let pl = iX2 pl1
 in orth(vec(ip(SpacePoint(pl1)), po1), iv(NormalVector(pl1))) -->
    po1 isIn pl"

plane_is_plane [rule_format] :
"ALL X_plane.
 iX2 X_plane =
 PlaneX2 (ip(SpacePoint(X_plane)), iv(NormalVector(X_plane)))"

def_of_given_arc [rule_format] :
"arc = X_SWArc center boundarypoint boundarypoint"

cylinder_offset [rule_format] : "offset = ip(center)"

cylinder_radius [rule_format] :
"radius = || vec(ip(center), ip(boundarypoint)) ||"

cylinder_axis [rule_format] :
"axis = VWithLength(iv(NormalVector(plane)), height)"

real_extrusion [rule_format] : "height >' 0''"

real_arc [rule_format] : "~ center = boundarypoint"

real_plane [rule_format] :
"~ NormalVector(plane) = X_SWVector 0'' 0'' 0''"

the_arc_is_wellformed [rule_format] :
"let c = ip(center);
     bp = ip(boundarypoint);
     p = iX2 plane
 in c isIn p & bp isIn p"

declare inv_Group [simp]
declare rinv_Group [simp]
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
declare sqrt_def [simp]
declare ga_select_C1 [simp]
declare ga_select_C2 [simp]
declare ga_select_C3 [simp]
declare ga_select_C1_1 [simp]
declare ga_select_C2_1 [simp]
declare ga_select_C3_1 [simp]
declare inv_Group_2_1 [simp]
declare rinv_Group_2_1 [simp]
declare colin_reflexivity [simp]
declare colin_symmetry [simp]
declare orth_symmetry [simp]
declare cross_product_orthogonal [simp]
declare vector_point_vector [simp]
declare point_vector_point [simp]
declare origin_to_zero [simp]
declare transitivity_of_vec_XPlus [simp]
declare vec_shift_def_lemma [simp]
declare emptySet_not_empty [simp]
declare allSet_contains_all [simp]
declare def_of_isIn [simp]
declare ga_select_first [simp]
declare ga_select_rest [simp]
declare ga_select_x [simp]
declare ga_select_y [simp]
declare ga_select_z [simp]
declare ga_select_x_1 [simp]
declare ga_select_y_1 [simp]
declare ga_select_z_1 [simp]
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
declare ga_select_DraftAngle [simp]
declare ga_select_DraftOutward [simp]
declare ga_select_DraftWhileExtruding [simp]
declare ga_select_EndCondition [simp]
declare ga_select_WallThickness [simp]
declare ga_select_IsBaseExtrude [simp]
declare ga_select_IsBossFeature [simp]
declare ga_select_IsThinFeature [simp]
declare vwl_colin [simp]
declare real_extrusion [simp]

theorem extrusion_is_cylinder :
"iX1
 (gn_inj(X_SWExtrusion (X_SWSketch (gn_inj(arc) ::' [ ]') plane)
         height x1 b1 b2 x2 x3 b3 b4 b5)) =
 Cylinder ((offset, radius), axis)"
  proof -
    def I01: interv01 == "XOSqBr__XPeriodXPeriodXPeriod__XCSqBr (0'', gn_inj(1'))"
    def k_bpoint: b_point == "ip(boundarypoint)"
    def k_plane: the_plane == "iX2 plane"
    def k_nv: n_plane == "iv(NormalVector(plane))"
    def k_offs: o_plane == "ip(SpacePoint(plane))"


      -- "introducing global facts"
    from help6 have
      p_struct: "plane = X_SWPlane (SpacePoint(plane)) (NormalVector(plane)) (InnerCS(plane))" by auto
    
    from the_arc_is_wellformed have
      p_bp_elem: "b_point isIn the_plane" by (simp only: Let_def k_plane k_bpoint)
    
    from the_arc_is_wellformed cylinder_offset have
      p_offs_elem: "offset isIn the_plane" by (simp only: Let_def k_plane k_bpoint)

    from k_plane plane_is_plane k_nv k_offs have
      theplane_struct: "the_plane = PlaneX2 (o_plane, n_plane)" by simp

    from vwl_colin colin_symmetry have
      axis_normal_colin: "colin(axis, n_plane)" by (simp only: cylinder_axis  k_nv [symmetric])

    show ?thesis

      apply (subst def_of_given_arc)
      apply (subst semantics_for_ArcExtrusion)
      apply (subst if_P, simp)
      -- "We need some way to pushing the let environment to the isar proof context"
      apply (simp only: Let_def)
      apply (simp only: def_of_Cylinder ActExtrude_constr set_comprehension)
      apply (simp only: I01 [symmetric])
      apply (simp only: ActAttach_constr)
      apply (simp only: cylinder_axis [symmetric])
      apply (simp only: cylinder_radius [symmetric])
      apply (simp only: cylinder_offset [symmetric] k_bpoint [symmetric])
      apply (simp only: k_plane [symmetric])

      apply (rule ext)

      -- "Now we split our task in two subgoals"
      proof (rule iffI)


	fix X_x
	assume "\<exists>l X_y. (l isIn interv01 \<and>
          X_y isIn
          X__intersection__X
          (X__XPlus__XX2 (offset, VBall ( radius )),
          the_plane)) \<and> X_x = X_y +' (l *_3 axis)"
	(is "\<exists>l X_y. ?A l X_y")

	then obtain l X_y_h where
	  h_1: "?A l X_y_h" (is "((?I l) \<and> (X_y_h isIn ?B)) \<and> (?C X_y_h l)") by auto

	def have_x_y: X_y == "vec(offset, X_y_h)" -- "this is the right instance for X_y!"

	with h_1 have "((l isIn interv01 \<and> orth(X_y, axis)) \<and> || X_y || <=' radius) \<and>
          X_x = (offset +' (l *_3 axis)) +' X_y" (is "?H l X_y")
      
	  -- "!!! THE MAIN PROOF OF THIS DIRECTION"
	proof -
	  assume ass1: "?A l X_y_h"
	  (is "(?I l \<and> X_y_h isIn X__intersection__X(?t1, the_plane)) \<and> ?t2")

(*
	    We have here a conjunction of 4 conjuncts to show:
	    1. "l isIn interv01" or shortened: "?I l"
	    which is already in the assumption

	    2. "orth(X_y, axis)"
	    which follows from some basic facts about colinearity and orthogonality
	    together with the fact that the interpretation of the given plane is
	    an affine plane (plane_is_plane) and that the vector between two points
	    on a plane is orthogonal to the normal vector of the plane
	    (plane_condition_for_2_points).

	    3. "|| X_y || <=' radius"
	    which follows from the fact, that X_y_h is in the Ball of radius = radius
	    with center = offset, and that X_y is actually vec(offset, X_y_h)

	    4. "X_x = (offset +' (l *_3 axis)) +' X_y"
	    Replacing
	    X_x by "X_y_h +' (l *_3 axis)"
	    and 
	    X_y by "vec(offset, X_y_h)"
	    and using "vec(x,y) = asVector(y)-asVector(x)"
	    and lifting the points offset and X_y_h to vectors yields 
	    a simple group-equation of the following form:
	    h + ax = o + ax + h - o
	    It would be nice to have group reasoning support at that place.
	    As we don't have it here, we don't follow the sketched proof but
	    use some special lemmas.
*)

	  then have subgoal1_1: "?I l" by simp

	  from ass1 have "X_y_h isIn X__intersection__X(?t1, the_plane)" by simp

	  -- "very hard to guess how we have to use the rule!!, TODO: try to generalize this drawback"
	  hence "X_y_h isIn ?t1 & X_y_h isIn the_plane" by (simp only: def_of_intersection [symmetric])
	  hence "X_y_h isIn the_plane" by simp

	  with p_offs_elem have
	    pre_for_orth: "offset isIn the_plane & X_y_h isIn the_plane" by simp

	  with orth_symmetry have_x_y theplane_struct plane_condition_for_2_points have
	    subgoal1_2a: "orth(n_plane, X_y)" by (simp add: Let_def)

	  with orth_symmetry axis_normal_colin colin_orth_transitivity have
	    subgoal1_2: "orth(X_y, axis)" by blast

	  have ball_xyh_elem: "X_y_h isIn ?t1" proof-
	    from ass1 have "X_y_h isIn X__intersection__X(?t1 , the_plane)" by auto
	    hence "(X_y_h isIn ?t1) \<and> (X_y_h isIn the_plane)"
	      by (simp only: def_of_intersection [symmetric])
	    thus ?thesis ..
	  qed

	  hence "X_y isIn (VBall radius)"
	  proof (simp add: vec_def plus_Point_VectorSet function_image set_comprehension)
	    assume "\<exists>X_y. VBall radius X_y \<and> offset +' X_y = X_y_h" (is "\<exists>X_y. ?VB X_y")
	    then obtain X_y2 where k_VB: "?VB X_y2" (is "?VB1 \<and> ?VB2") by auto
	    
	    from k_VB have_x_y vec_shift_unique_lemma have "X_y2 = X_y" by auto
	    with k_VB show "VBall radius X_y" by auto
	  qed

	  hence subgoal1_3: "|| X_y || <=' radius" by (simp add: VBall_constr set_comprehension)


thm cylinder_axis
(*
"axis = VWithLength(iv(NormalVector(plane)), height)"
*)

thm simple_colin_condition
thm colin_orth_transitivity
by auto
"colin(X_x, X_y) & orth(X_y, X_z) --> orth(X_x, X_z)"


	    apply (simp only: k_nv [symmetric] k_offs [symmetric])
	    by auto

 by (simp add: Let_def)

	  
thm semantics_for_Planes
(*
iX2 (X_SWPlane ?X_o ?X_n ?ics) = ActAttach (ip(?X_o), VPlane (iv(?X_n)))
*)

thm plane_condition_for_2_points
(* 
let X_plane = PlaneX2 (?X_offset, ?normal)
in ?X_x isIn X_plane \<and> ?X_y isIn X_plane \<longrightarrow> orth(vec(?X_x, ?X_y), ?normal)


    def k_nv: n_plane == "iv(NormalVector(plane))"
    def k_offs: o_plane == "ip(SpacePoint(plane))"

need to show that the_plane = Plane (o_plane, n_plane)
with:  k_plane plane_is_plane k_nv k_offs
*)


thm plane_is_plane
(*
iX2 ?X_plane = PlaneX2 (ip(SpacePoint(?X_plane)), iv(NormalVector(?X_plane)))
*)

thm k_plane
(*
the_plane \<equiv> iX2 plane
*)

thm p_struct
(*
plane = X_SWPlane (SpacePoint(plane)) (NormalVector(plane)) (InnerCS(plane))
*)



using Ax1_1 Ax2 sqr_def sqrt_def X2_def_Real X3_def_Real
      X4_def_Real X5_def_Real X6_def_Real X7_def_Real X8_def_Real
      X9_def_Real decimal_def Zero_Point Zero_Vector
      scalar_mutliplication scalar_product vector_product colin_def
      sqr_def_1_1 norm_from_scalar_prod_def orthogonal_def
      point_to_vector_embedding vector_to_point_embedding Ax1_1_1 vec_def
      compatibility_PVplus_Vplus set_comprehension function_image
      def_of_interval plus_PointSet_Vector plus_Point_VectorSet
      plus_PointSet_VectorSet def_of_Plane def_of_Circle def_of_Cylinder
      def_of_Cylinder1 E1_def E2_def E3_def VLine_constr
      VWithLength_constr VPlane_constr VPlane2_constr VConnected_constr
      VHalfSpace_constr VHalfSpace2_constr VBall_constr VCircle_constr
      ActAttach_constr ActExtrude_constr semantics_for_SWPoint
      semantics_for_SWVector def_of_given_arc cylinder_offset
      cylinder_radius cylinder_axis
by (auto)

ML "Header.record \"extrusion_is_cylinder\""

end
