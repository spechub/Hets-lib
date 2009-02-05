theory SWCommonPatterns_SWCylByAE_IsCylinder_T
imports "$HETS_LIB/Isabelle/MainHCPairs"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"help1\", \"help2\", \"help3\", \"help4\", \"help5\", \"help6\",
     \"inv_Group\", \"rinv_Group\", \"distr1_Ring\", \"distr2_Ring\",
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
     \"max_sup_relation\", \"Ax1_3\", \"Ax1_4\", \"sqr_def\",
     \"sqrt_def\", \"Ax1_2_1\", \"X2_def_Real\", \"X3_def_Real\",
     \"X4_def_Real\", \"X5_def_Real\", \"X6_def_Real\", \"X7_def_Real\",
     \"X8_def_Real\", \"X9_def_Real\", \"ZeroToNine_type\",
     \"decimal_def\", \"direction_subtype\", \"ga_select_x\",
     \"ga_select_y\", \"ga_select_z\", \"ga_select_ArcPlane\",
     \"ga_select_Center\", \"ga_select_Start\", \"ga_select_End\",
     \"ga_select_SpacePoint\", \"ga_select_NormalVector\",
     \"ga_select_getArc\", \"ga_select_From\", \"ga_select_Length\",
     \"ga_select_ExDirection\", \"ga_select_getPlane\",
     \"degenerated_Point_def\", \"degenerated_Plane_def\", \"E1_def\",
     \"E2_def\", \"E3_def\", \"nondegeneratedpoint_subtype\",
     \"nondegeneratedplane_subtype\", \"ga_select_C1\",
     \"ga_select_C2\", \"ga_select_C3\", \"Zero_Point\", \"Ax1_1_1\",
     \"ga_select_C1_1\", \"ga_select_C2_1\", \"ga_select_C3_1\",
     \"Zero_Vector\", \"def_of_vector_addition\",
     \"def_of_minus_vector\", \"binary_inverse_1_1\",
     \"scalar_mutliplication\", \"scalar_product\", \"vector_product\",
     \"the_norm_of_a_vector\", \"orthogonal_def\", \"colin_def\",
     \"cross_product_antisymmetric\", \"cross_product_orthogonal\",
     \"cross_product_zero_iff_colinear\", \"orth_symmetry\",
     \"colin_orth_transitivity\", \"colin_reflexivity\",
     \"colin_symmetry\", \"point_to_vector_embedding\",
     \"vector_to_point_embedding\", \"vec_def\",
     \"compatibility_PVplus_Vplus\", \"transitivity_of_vec_XPlus\",
     \"antisymmetry_of_vec\", \"set_comprehension\", \"function_image\",
     \"emptySet_not_empty\", \"allSet_contains_all\", \"def_of_isIn\",
     \"def_of_subset\", \"def_of_union\", \"def_of_bigunion\",
     \"def_of_intersection\", \"def_of_difference\",
     \"def_of_disjoint\", \"def_of_productset\", \"def_of_interval\",
     \"plus_PointSet_Vector\", \"plus_Point_VectorSet\",
     \"plus_PointSet_VectorSet\", \"def_of_Circle\",
     \"def_of_Cylinder\", \"VLine_constr\", \"VWithLength_constr\",
     \"VPlane_constr\", \"VPlane2_constr\", \"VConnected_constr\",
     \"VHalfSpace_constr\", \"VHalfSpace2_constr\", \"VBall_constr\",
     \"VCircle_constr\", \"ActAttach_constr\", \"ActExtrude_constr\",
     \"constrfact1\", \"pointsemantics_for_SWPoint\",
     \"vectorsemantics_for_SWPoint\", \"semantics_for_plane\",
     \"semantics_for_Arc\", \"semantics_for_ArcExtrusion\",
     \"def_of_given_arc\", \"def_of_given_cylinder\",
     \"real_extrusion\", \"real_arc\", \"the_arc_is_wellformed\",
     \"viewdef_of_offset\", \"viewdef_of_axis\", \"viewdef_of_C\",
     \"viewdef_of_radius\", \"Ax1_5\",
     \"the_length_of_the_axis_is_the_height\",
     \"nonXMinuscollapsed_cylinder\"]"

typedecl Direction
typedecl NonZero
typedecl PointSet
typedecl Real
typedecl RealPos
typedecl RealSet
typedecl SWPlaneNonDegenerated
typedecl SWPointNonDegenerated
typedecl ('a1) Set
typedecl VectorSet
typedecl ZeroToNine

datatype SWPoint = X_SWPoint "Real" "Real" "Real"
         and SWArc = X_SWArc "SWPlane" "SWPoint" "SWPoint" "SWPoint"
         and SWPlane = X_SWPlane "SWPoint" "SWPoint"
         and SWObject = X_Arc "SWArc" ("Arc/'(_')" [3] 999) | X_Extrusion "SWObject" "Real" "Direction" ("Extrusion/'(_,/ _,/ _')" [3,3,3] 999) | X_Plane "SWPlane" ("Plane/'(_')" [3] 999)
datatype Point = X_P "Real" "Real" "Real" ("P/'(_,/ _,/ _')" [3,3,3] 999)
datatype Vector = X_V "Real" "Real" "Real" ("V/'(_,/ _,/ _')" [3,3,3] 999)

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
E1 :: "SWPlane"
E2 :: "SWPlane"
E3 :: "SWPlane"
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
XVBar__XVBar :: "Vector => Real" ("(|/ _/ |)" [10] 999)
X_ArcPlane :: "SWArc => SWPlane" ("ArcPlane/'(_')" [3] 999)
X_C :: "Point => bool" ("C/'(_')" [3] 999)
X_Center :: "SWArc => SWPoint" ("Center/'(_')" [3] 999)
X_End :: "SWArc => SWPoint" ("End/'(_')" [3] 999)
X_ExDirection :: "SWObject => Direction" ("ExDirection/'(_')" [3] 999)
X_From :: "SWObject => SWObject" ("From/'(_')" [3] 999)
X_Length :: "SWObject => Real" ("Length/'(_')" [3] 999)
X_NormalVector :: "SWPlane => SWPoint" ("NormalVector/'(_')" [3] 999)
X_Pos :: "Real => bool" ("Pos/'(_')" [3] 999)
X_SpacePoint :: "SWPlane => SWPoint" ("SpacePoint/'(_')" [3] 999)
X_Start :: "SWArc => SWPoint" ("Start/'(_')" [3] 999)
X_VWithLength :: "Vector => Real => Vector" ("VWithLength/'(_,/ _')" [3,3] 999)
X__XAtXAt__X :: "ZeroToNine => Real => Real" ("(_/ @@/ _)" [54,54] 52)
X__XBslashXBslash__X :: "('S => bool) * ('S => bool) => 'S => bool"
X__XGtXEq__X :: "Real => Real => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XGt__X :: "Real => Real => bool" ("(_/ >''/ _)" [44,44] 42)
X__XHash__X :: "Vector => Vector => Vector" ("(_/ #''/ _)" [54,54] 52)
X__XLtXEq__X :: "Real => Real => bool" ("(_/ <=''/ _)" [44,44] 42)
X__XLt__X :: "Real => Real => bool" ("(_/ <''/ _)" [44,44] 42)
X__XMinus__XX1 :: "Real => NonZero => Real" ("(_/ -''/ _)" [54,54] 52)
X__XMinus__XX2 :: "Real => Real => Real" ("(_/ -''''/ _)" [54,54] 52)
X__XMinus__XX3 :: "Vector => Vector => Vector" ("(_/ -'_3/ _)" [54,54] 52)
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
X_abs :: "Real => Real" ("abs''/'(_')" [3] 999)
X_allSet :: "'S => bool" ("allSet/'(_')" [3] 999)
X_asPoint :: "Vector => Point" ("asPoint/'(_')" [3] 999)
X_asVector :: "Point => Vector" ("asVector/'(_')" [3] 999)
X_colin :: "Vector => Vector => bool" ("colin/'(_,/ _')" [3,3] 999)
X_emptySet :: "'S => bool" ("emptySet/'(_')" [3] 999)
X_getArc :: "SWObject => SWArc" ("getArc/'(_')" [3] 999)
X_getPlane :: "SWObject => SWPlane" ("getPlane/'(_')" [3] 999)
X_gn_inj :: "'a => 'b" ("gn'_inj/'(_')" [3] 999)
X_gn_proj :: "'a => 'b partial" ("gn'_proj/'(_')" [3] 999)
X_image :: "('S => 'T) * ('S => bool) => 'T => bool"
X_inv :: "NonZero => NonZero" ("inv''/'(_')" [3] 999)
X_ip :: "SWPoint => Point" ("ip/'(_')" [3] 999)
X_iv :: "SWPoint => Vector" ("iv/'(_')" [3] 999)
X_max :: "Real => Real => Real" ("max''/'(_,/ _')" [3,3] 999)
X_min :: "Real => Real => Real" ("min''/'(_,/ _')" [3,3] 999)
X_orth :: "Vector => Vector => bool" ("orth/'(_,/ _')" [3,3] 999)
X_sqr :: "Real => Real" ("sqr/'(_')" [3] 999)
X_sqrt :: "RealPos => RealPos" ("sqrt/'(_')" [3] 999)
X_sup :: "Real => Real => Real partial" ("sup/'(_,/ _')" [3,3] 999)
X_vec :: "Point => Point => Vector" ("vec/'(_,/ _')" [3,3] 999)
X_x :: "SWPoint => Real" ("x/'(_')" [3] 999)
X_y :: "SWPoint => Real" ("y/'(_')" [3] 999)
X_z :: "SWPoint => Real" ("z/'(_')" [3] 999)
arc :: "SWArc"
axis :: "Vector"
bigunion :: "(('S => bool) => bool) => 'S => bool"
boundarypoint :: "SWPoint"
center :: "SWPoint"
cylinder :: "SWObject"
degeneratedX1 :: "SWPlane => bool" ("degenerated''/'(_')" [3] 999)
degeneratedX2 :: "SWPoint => bool" ("degenerated''''/'(_')" [3] 999)
direction :: "Direction"
height :: "Real"
i :: "SWObject => Point => bool"
infX1 :: "Real => Real => Real partial" ("inf''/'(_,/ _')" [3,3] 999)
infX2 :: "(Real => bool) => Real partial" ("inf''''/'(_')" [3] 999)
offset :: "Point"
plane :: "SWPlaneNonDegenerated"
radius :: "Real"

axioms
help1 [rule_format] :
"ALL p2.
 ALL X_n.
 X__intersection__X
 (VHalfSpace2 (iv(gn_inj(p2))), VHalfSpace2 (-'' iv(gn_inj(p2)))) =
 VPlane (iv(gn_inj(X_n)))"

help2 [rule_format] :
"ALL p2.
 X__union__X (VHalfSpace2 (iv(p2)), VHalfSpace2 (-'' iv(p2))) =
 X_allSet"

help3 [rule_format] :
"ALL c.
 ALL p1.
 ALL pl1.
 i (Arc(X_SWArc (gn_inj(pl1)) c p1 p1)) =
 (let cp = ip(c);
      r = iv(p1) -_3 iv(c);
      X_Ball = VBall ( | r | );
      X_plane = i (Plane(gn_inj(pl1)))
  in X__intersection__X (ActAttach (cp, X_Ball), X_plane))"

help4 [rule_format] :
"ALL pl2.
 ALL po1.
 ALL po2.
 let pl = i (Plane(pl2))
 in po1 isIn pl & po2 isIn pl -->
    orth(iv(NormalVector(pl2)), vec(po1, po2))"

help5 [rule_format] :
"ALL A.
 ALL Q. (let a = A in % b. Q a b) = (% b. let a = A in Q a b)"

help6 [rule_format] :
"ALL p1.
 ALL p2.
 ALL pl2.
 p1 = SpacePoint(pl2) & p2 = NormalVector(pl2) -->
 pl2 = X_SWPlane p1 p2"

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

Ax1 [rule_format] : "ALL X_x. True = (~ X_x = 0'')"

inv_Group_1 [rule_format] : "ALL X_x. inv'(X_x) *' X_x = 1'"

rinv_Group_1 [rule_format] : "ALL X_x. X_x *' inv'(X_x) = 1'"

binary_inverse [rule_format] :
"ALL X_x. ALL X_y. X_x -'' X_y = X_x +_3 -' X_y"

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
"ALL X_x. ALL X_y. inf'(X_x, X_y) =s= inf'(X_y, X_x)"

ga_comm_sup [rule_format] :
"ALL X_x. ALL X_y. sup(X_x, X_y) =s= sup(X_y, X_x)"

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
"ALL X_x. abs'(X_x) = (if 0'' <=' X_x then X_x else -' X_x)"

Ax1_4 [rule_format] : "ALL X_x. True = (X_x >=' 0'')"

sqr_def [rule_format] : "ALL r. sqr(r) = r *'' r"

sqrt_def [rule_format] :
"ALL q.
 (let (Xb1, Xc0) = gn_proj(sqr(gn_inj(q)))
  in if Xb1 then makePartial (sqrt(Xc0)) else noneOp) =
 makePartial q"

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
 True =
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

direction_subtype [rule_format] :
"ALL X_x.
 True = (makePartial X_x = gn_inj(1') | X_x = -' gn_inj(1'))"

ga_select_x [rule_format] :
"ALL x_1_1.
 ALL x_1_2. ALL x_1_3. x(X_SWPoint x_1_1 x_1_2 x_1_3) = x_1_1"

ga_select_y [rule_format] :
"ALL x_1_1.
 ALL x_1_2. ALL x_1_3. y(X_SWPoint x_1_1 x_1_2 x_1_3) = x_1_2"

ga_select_z [rule_format] :
"ALL x_1_1.
 ALL x_1_2. ALL x_1_3. z(X_SWPoint x_1_1 x_1_2 x_1_3) = x_1_3"

ga_select_ArcPlane [rule_format] :
"ALL x_1_1.
 ALL x_1_2.
 ALL x_1_3.
 ALL x_1_4. ArcPlane(X_SWArc x_1_1 x_1_2 x_1_3 x_1_4) = x_1_1"

ga_select_Center [rule_format] :
"ALL x_1_1.
 ALL x_1_2.
 ALL x_1_3.
 ALL x_1_4. Center(X_SWArc x_1_1 x_1_2 x_1_3 x_1_4) = x_1_2"

ga_select_Start [rule_format] :
"ALL x_1_1.
 ALL x_1_2.
 ALL x_1_3.
 ALL x_1_4. Start(X_SWArc x_1_1 x_1_2 x_1_3 x_1_4) = x_1_3"

ga_select_End [rule_format] :
"ALL x_1_1.
 ALL x_1_2.
 ALL x_1_3. ALL x_1_4. End(X_SWArc x_1_1 x_1_2 x_1_3 x_1_4) = x_1_4"

ga_select_SpacePoint [rule_format] :
"ALL x_1_1. ALL x_1_2. SpacePoint(X_SWPlane x_1_1 x_1_2) = x_1_1"

ga_select_NormalVector [rule_format] :
"ALL x_1_1. ALL x_1_2. NormalVector(X_SWPlane x_1_1 x_1_2) = x_1_2"

ga_select_getArc [rule_format] :
"ALL x_1_1. getArc(Arc(x_1_1)) = x_1_1"

ga_select_From [rule_format] :
"ALL x_1_1.
 ALL x_1_2. ALL x_1_3. From(Extrusion(x_1_1, x_1_2, x_1_3)) = x_1_1"

ga_select_Length [rule_format] :
"ALL x_1_1.
 ALL x_1_2.
 ALL x_1_3. Length(Extrusion(x_1_1, x_1_2, x_1_3)) = x_1_2"

ga_select_ExDirection [rule_format] :
"ALL x_1_1.
 ALL x_1_2.
 ALL x_1_3. ExDirection(Extrusion(x_1_1, x_1_2, x_1_3)) = x_1_3"

ga_select_getPlane [rule_format] :
"ALL x_1_1. getPlane(Plane(x_1_1)) = x_1_1"

degenerated_Point_def [rule_format] :
"degeneratedX2 = (% p. p = X_SWPoint 0'' 0'' 0'')"

degenerated_Plane_def [rule_format] :
"degeneratedX1 = (% p. degenerated''(NormalVector(p)))"

E1_def [rule_format] :
"E1 =
 X_SWPlane (X_SWPoint 0'' 0'' 0'') (X_SWPoint 0'' 0'' (gn_inj(1')))"

E2_def [rule_format] :
"E2 =
 X_SWPlane (X_SWPoint 0'' 0'' 0'') (X_SWPoint 0'' (gn_inj(1')) 0'')"

E3_def [rule_format] :
"E3 =
 X_SWPlane (X_SWPoint 0'' 0'' 0'') (X_SWPoint (gn_inj(1')) 0'' 0'')"

nondegeneratedpoint_subtype [rule_format] :
"ALL p. True = (~ degenerated''(p))"

nondegeneratedplane_subtype [rule_format] :
"ALL p. True = (~ degenerated'(p))"

ga_select_C1 [rule_format] :
"ALL x_1_1.
 ALL x_1_2. ALL x_1_3. C1'(P(x_1_1, x_1_2, x_1_3)) = x_1_1"

ga_select_C2 [rule_format] :
"ALL x_1_1.
 ALL x_1_2. ALL x_1_3. C2'(P(x_1_1, x_1_2, x_1_3)) = x_1_2"

ga_select_C3 [rule_format] :
"ALL x_1_1.
 ALL x_1_2. ALL x_1_3. C3'(P(x_1_1, x_1_2, x_1_3)) = x_1_3"

Zero_Point [rule_format] : "0' = P(0'', 0'', 0'')"

Ax1_1_1 [rule_format] :
"ALL X_x. ALL X_y. X_x -' X_y = X_x *'' gn_inj(inv'(X_y))"

ga_select_C1_1 [rule_format] :
"ALL x_1_1.
 ALL x_1_2. ALL x_1_3. C1''(V(x_1_1, x_1_2, x_1_3)) = x_1_1"

ga_select_C2_1 [rule_format] :
"ALL x_1_1.
 ALL x_1_2. ALL x_1_3. C2''(V(x_1_1, x_1_2, x_1_3)) = x_1_2"

ga_select_C3_1 [rule_format] :
"ALL x_1_1.
 ALL x_1_2. ALL x_1_3. C3''(V(x_1_1, x_1_2, x_1_3)) = x_1_3"

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
"ALL X_x. ALL X_y. X_x -_3 X_y = X_x +_4 -'' X_y"

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
 V((C2''(X_x) *'' C3''(X_y)) -'' (C2''(X_y) *'' C3''(X_x)),
 (C3''(X_x) *'' C1''(X_y)) -'' (C3''(X_y) *'' C1''(X_x)),
 (C1''(X_x) *'' C2''(X_y)) -'' (C1''(X_y) *'' C2''(X_x)))"

the_norm_of_a_vector [rule_format] :
"ALL X_x.
 makePartial ( | X_x | ) =
 (let (Xb3, Xc0) =
      let (Xb2, Xc1) = gn_proj(X_x *_4 X_x)
      in if Xb2 then makePartial (sqrt(Xc1)) else noneOp
  in if Xb3 then gn_proj(Xc0) else noneOp)"

orthogonal_def [rule_format] :
"ALL X_x. ALL X_y. orth(X_x, X_y) = (X_x *_4 X_y = 0'')"

colin_def [rule_format] :
"ALL X_x.
 ALL X_y. colin(X_x, X_y) = (X_y = 0_3 | (EX r. X_x = r *_3 X_y))"

cross_product_antisymmetric [rule_format] :
"ALL X_x. ALL X_y. X_x #' X_y = -'' (X_y #' X_x)"

cross_product_orthogonal [rule_format] :
"ALL X_x. ALL X_y. orth(X_x, X_x #' X_y)"

cross_product_zero_iff_colinear [rule_format] :
"ALL X_x. ALL X_y. colin(X_x, X_y) = (X_x #' X_y = 0_3)"

orth_symmetry [rule_format] :
"ALL X_x. ALL X_y. orth(X_x, X_y) --> orth(X_y, X_x)"

colin_orth_transitivity [rule_format] :
"ALL X_x.
 ALL X_y.
 ALL X_z. colin(X_x, X_y) & orth(X_y, X_z) --> orth(X_x, X_z)"

colin_reflexivity [rule_format] : "ALL X_x. colin(X_x, X_x)"

colin_symmetry [rule_format] :
"ALL X_x. ALL X_y. colin(X_x, X_y) --> colin(X_y, X_x)"

point_to_vector_embedding [rule_format] :
"ALL p. asVector(p) = V(C1'(p), C2'(p), C3'(p))"

vector_to_point_embedding [rule_format] :
"ALL p. ALL v. asPoint(v) = P(C1'(p), C2'(p), C3'(p))"

vec_def [rule_format] :
"ALL p. ALL p'. vec(p, p') = asVector(p') -_3 asVector(p)"

compatibility_PVplus_Vplus [rule_format] :
"ALL p. ALL v. asVector(p +' v) = asVector(p) +_4 v"

transitivity_of_vec_XPlus [rule_format] :
"ALL p. ALL q. ALL r. vec(p, q) +_4 vec(q, r) = vec(p, r)"

antisymmetry_of_vec [rule_format] :
"ALL p. ALL q. vec(p, q) = -'' vec(q, p)"

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

def_of_Circle [rule_format] :
"ALL X_offset.
 ALL orientation.
 ALL r.
 Circle ((X_offset, r), orientation) =
 XLBrace__XRBrace
 (% X_x. EX X_y.
         (orth(X_y, orientation) & | X_y | <=' r) & X_x = X_offset +' X_y)"

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
          | X_y | <=' r) &
         X_x = (X_offset +' (l *_3 X_axis)) +' X_y)"

VLine_constr [rule_format] :
"ALL p1.
 ALL p2.
 VLine (p1, p2) =
 X_image
 (% X_y. p1 +_4 (X_y *_3 (p2 -_3 p1)),
  XOSqBr__XPeriodXPeriodXPeriod__XCSqBr (0'', gn_inj(1')))"

VWithLength_constr [rule_format] :
"ALL s.
 ALL v.
 VWithLength(v, s) =
 (if v = 0_3 then v
     else (X__Xx__XX3 (X__XSlash__X s (gn_inj( | v | )::NonZero)) v))"
(*
VWithLength_constr [rule_format] :
"ALL s.
 ALL v.
 makePartial (VWithLength(v, s)) =
 (if v = 0_3 then makePartial v
     else mapPartial (flip X__Xx__XX3 v)
          (mapPartial (X__XSlash_X s) (gn_proj( | v | ))))"
*)

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
"ALL r. VBall r = XLBrace__XRBrace (% X_y. | X_y | <=' r)"

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

constrfact1 [rule_format] :
"ALL s. ALL v. ~ v = 0_3 --> | VWithLength(v, s) | = abs'(s)"

pointsemantics_for_SWPoint [rule_format] :
"ALL point. ip(point) = P(x(point), y(point), z(point))"

vectorsemantics_for_SWPoint [rule_format] :
"ALL point. iv(point) = asVector(ip(point))"

semantics_for_plane [rule_format] :
"ALL X_x.
 ALL X_y.
 i (Plane(X_SWPlane X_x X_y)) =
 ActAttach (ip(X_x), VPlane (iv(X_y)))"

semantics_for_Arc [rule_format] :
"ALL p.
 ALL X_x.
 ALL X_y.
 ALL X_z.
 i (Arc(X_SWArc p X_x X_y X_z)) =
 (let cp = ip(X_x);
      X_center = iv(X_x);
      p1 = iv(X_y);
      p2 = iv(X_z);
      X_n = iv(NormalVector(p));
      r1 = p1 -_3 X_center;
      r2 = p2 -_3 X_center;
      X_Ball = VBall ( | r1 | );
      HS1 = VHalfSpace2 (X_n #' r1);
      HS2 = VHalfSpace2 (r2 #' X_n);
      X_plane = i (Plane(p))
  in X__intersection__X
     (ActAttach
      (cp,
       X__intersection__X
       (X_Ball,
        if (X_n #' r1) *_4 r2 >' 0'' then X__intersection__X (HS1, HS2)
           else X__union__X (HS1, HS2))),
      X_plane))"

semantics_for_ArcExtrusion [rule_format] :
"ALL a.
 ALL d.
 ALL l.
 i (Extrusion(Arc(a), l, d)) =
 (let X_axis = iv(NormalVector(ArcPlane(a)));
      scaledAxis = VWithLength(X_axis, gn_inj(d) *'' l);
      X_arc = i (Arc(a))
  in ActExtrude (scaledAxis, X_arc))"

def_of_given_arc [rule_format] :
"arc = X_SWArc (gn_inj(plane)) center boundarypoint boundarypoint"

def_of_given_cylinder [rule_format] :
"cylinder = Extrusion(Arc(arc), height, direction)"

real_extrusion [rule_format] : "height >' 0''"

real_arc [rule_format] : "~ center = boundarypoint"

the_arc_is_wellformed [rule_format] :
"let c = ip(center);
     bp = ip(boundarypoint);
     p = i (Plane(gn_inj(plane)))
 in c isIn p & bp isIn p"

viewdef_of_offset [rule_format] : "offset = ip(center)"

viewdef_of_axis [rule_format] :
"axis =
 VWithLength(iv(NormalVector(gn_inj(plane))),
 gn_inj(direction) *'' height)"

viewdef_of_C [rule_format] : "X_C = i cylinder"

viewdef_of_radius [rule_format] :
"radius = | iv(boundarypoint) -_3 iv(center) |"

declare help1 [simp]
declare help2 [simp]
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
declare ga_select_x [simp]
declare ga_select_y [simp]
declare ga_select_z [simp]
declare ga_select_ArcPlane [simp]
declare ga_select_Center [simp]
declare ga_select_Start [simp]
declare ga_select_End [simp]
declare ga_select_SpacePoint [simp]
declare ga_select_NormalVector [simp]
declare ga_select_getArc [simp]
declare ga_select_From [simp]
declare ga_select_Length [simp]
declare ga_select_ExDirection [simp]
declare ga_select_getPlane [simp]
declare ga_select_C1 [simp]
declare ga_select_C2 [simp]
declare ga_select_C3 [simp]
declare ga_select_C1_1 [simp]
declare ga_select_C2_1 [simp]
declare ga_select_C3_1 [simp]
declare cross_product_orthogonal [simp]
declare orth_symmetry [simp]
declare colin_reflexivity [simp]
declare colin_symmetry [simp]
declare transitivity_of_vec_XPlus [simp]
declare emptySet_not_empty [simp]
declare allSet_contains_all [simp]
declare def_of_isIn [simp]
declare real_extrusion [simp]


theorem Ax1_5 : "X_C = Cylinder ((offset, radius), axis)"
proof -
  -- "introducing abbreviations"
  def k_inter: interv01 == "XOSqBr__XPeriodXPeriodXPeriod__XCSqBr (0'', gn_inj(1'))"
  def k_nv: n_plane == "NormalVector(gn_inj(plane))"
  def k_offs: o_plane == "SpacePoint(gn_inj(plane))"
  def k_swplane: sw_plane == "gn_inj(plane)::SWPlane"
  def k_plane: the_plane == "i(Plane(gn_inj(plane)))"
  def k_bpoint: b_point == "ip(boundarypoint)"

  -- "introducing facts"
  from help6 k_nv k_offs have
    p_struct: "gn_inj(plane) = X_SWPlane o_plane n_plane" by auto

  from the_arc_is_wellformed have
    p_bp_elem: "b_point isIn the_plane" by (simp only: Let_def k_plane k_bpoint)

  from the_arc_is_wellformed viewdef_of_offset have
    p_offs_elem: "offset isIn the_plane" by (simp only: Let_def k_plane k_bpoint)
  
  show ?thesis
  -- "expanding the definitions"
  apply (simp only: viewdef_of_C)
  apply (simp only: def_of_Cylinder)
  apply (simp only: def_of_given_cylinder)
  apply (simp only: def_of_given_arc)
  apply (simp only: semantics_for_ArcExtrusion)
  apply (simp only: ga_select_ArcPlane)
  apply (simp only: ActExtrude_constr)
  apply (simp only: k_inter [symmetric])
  apply (simp only: set_comprehension)
  apply (simp only: help5)

  apply (simp only: Let_def)
  apply (simp only: viewdef_of_axis [symmetric])

  apply (simp only: help3)
  apply (simp only: ActAttach_constr Let_def)
  apply (simp only: viewdef_of_radius [symmetric])

  apply (simp only: viewdef_of_offset [symmetric])

  apply (simp only: k_plane [symmetric])

(*
  apply (simp only: p_struct)
  apply (simp only: semantics_for_plane)
  apply (simp only: ActAttach_constr Let_def)
  apply (simp only: VPlane_constr)
  apply (simp only: VBall_constr)
*)

  apply (rule ext)
  
  proof (rule iffI) -- "introduces two subgoals"
    fix X_x
    assume "\<exists>l X_y. (l isIn interv01 \<and>
              X_y isIn
              X__intersection__X
               (X__XPlus__XX2
                 (offset, VBall(radius)),
                the_plane)) \<and>
             X_x = X_y +' (l *_3 axis)" (is "\<exists>l X_y. ?A l X_y")
    then obtain l X_y_h where
      h_1: "?A l X_y_h" (is "((?I l) \<and> (X_y_h isIn ?B)) \<and> (?C X_y_h l)") by auto
    -- "this is the right instance for X_y!"
    def have_x_y: X_y == "vec(offset, X_y_h)"
    with h_1 have "((l isIn interv01 \<and> orth(X_y, axis)) \<and> | X_y | <=' radius) \<and>
                  X_x = (offset +' (l *_3 axis)) +' X_y" (is "?H l X_y")

    -- "!!! THE MAIN PROOF OF THIS DIRECTION"
    proof -
      assume ass1: "(l isIn interv01 \<and>
	X_y_h isIn
	X__intersection__X
	(X__XPlus__XX2 (offset,
	VBall(radius)), the_plane)) \<and>
	X_x = X_y_h +' (l *_3 axis)"
      (is "(?I l \<and> X_y_h isIn X__intersection__X(?t1, the_plane)) \<and> ?t2")

      -- "there are 4 goals to prove:"
      
      -- "1st. "
      hence subgoal1: "?I l" by auto


      have p_xyh_elem: "X_y_h isIn the_plane" proof-
	from ass1 have "X_y_h isIn X__intersection__X(?t1 , the_plane)" by auto
	hence "(X_y_h isIn ?t1) \<and> (X_y_h isIn the_plane)"
	  by (simp only: def_of_intersection [symmetric])
	thus ?thesis ..
      qed
      with p_offs_elem have "offset isIn the_plane \<and> X_y_h isIn the_plane" ..
      with k_plane k_swplane have p_ox_elem: "offset isIn i(Plane(sw_plane)) \<and> X_y_h isIn i(Plane(sw_plane))" by auto
      from help4 have "offset isIn i(Plane(sw_plane)) \<and> X_y_h isIn i(Plane(sw_plane))
	\<longrightarrow> orth(iv(NormalVector(sw_plane)), vec(offset, X_y_h))"
	by (simp only:Let_def) auto

      with p_ox_elem have "orth(iv(NormalVector(sw_plane)), vec(offset, X_y_h))" by auto
      with k_nv k_swplane have subgoal2_first: "orth(iv(n_plane), vec(offset,X_y_h))" by auto

      have "colin(axis,iv(n_plane))"
	apply (simp only: viewdef_of_axis k_nv [symmetric])
	apply (simp only: VWithLength_constr)
	apply (cases "iv(n_plane) = 0_3")
	apply simp
	by (simp add: colin_def) auto

      with subgoal2_first colin_orth_transitivity
      have "orth(axis, vec(offset,X_y_h))" by blast
     
      -- "2nd. "
      with orth_symmetry have_x_y have "orth(X_y, axis)" by auto

      

      -- "todo"
      


      show "?H l X_y" sorry 
    qed

    thus "\<exists>l X_y. ?H l X_y" by auto
    -- "first goal solved"
    
    next

    -- "tackle next goal"
    fix X_x
    assume "\<exists>l X_y. ((l isIn interv01 \<and> orth(X_y, axis)) \<and> | X_y | <=' radius) \<and>
              X_x = (offset +' (l *_3 axis)) +' X_y" (is "\<exists>l X_y. ?A l X_y")
    then obtain l X_y_h where
      h_2: "?A l X_y_h" (is "((?I l \<and> ?O X_y_h) \<and> (?C X_y_h)) \<and> (?D X_y_h l)") by auto
    def X_y == "offset +' X_y_h"
    with h_2 have "(l isIn interv01 \<and>
                   X_y isIn
                   X__intersection__X
                    (X__XPlus__XX2 (offset, VBall(radius)),
                     i (Plane(gn_inj(plane))))) \<and>
                  X_x = X_y +' (l *_3 axis)" (is "?H l X_y")

    -- "!!! THE MAIN PROOF OF THIS DIRECTION"
    proof -
      show "?H l X_y" sorry
    qed

    thus "\<exists>l X_y. ?H l X_y" by auto
    -- "second (and last) goal solved"
  qed
qed




ML "Header.record \"Ax1_5\""

theorem the_length_of_the_axis_is_the_height : "| axis | = height"
using Ax1_1 Ax1_3 sqr_def sqrt_def X2_def_Real X3_def_Real
      X4_def_Real X5_def_Real X6_def_Real X7_def_Real X8_def_Real
      X9_def_Real decimal_def degenerated_Point_def degenerated_Plane_def
      E1_def E2_def E3_def Zero_Point Ax1_1_1 Zero_Vector
      scalar_mutliplication scalar_product vector_product
      the_norm_of_a_vector orthogonal_def colin_def vec_def
      set_comprehension function_image def_of_interval
      plus_PointSet_Vector plus_Point_VectorSet plus_PointSet_VectorSet
      def_of_Circle def_of_Cylinder VLine_constr VWithLength_constr
      VPlane_constr VPlane2_constr VConnected_constr VHalfSpace_constr
      VHalfSpace2_constr VBall_constr VCircle_constr ActAttach_constr
      ActExtrude_constr pointsemantics_for_SWPoint
      vectorsemantics_for_SWPoint def_of_given_arc def_of_given_cylinder
      viewdef_of_offset viewdef_of_axis viewdef_of_C viewdef_of_radius
by auto

ML "Header.record \"the_length_of_the_axis_is_the_height\""

theorem nonXMinuscollapsed_cylinder :
"radius >' 0'' & height >' 0''"
using Ax1_1 Ax1_3 sqr_def sqrt_def X2_def_Real X3_def_Real
      X4_def_Real X5_def_Real X6_def_Real X7_def_Real X8_def_Real
      X9_def_Real decimal_def degenerated_Point_def degenerated_Plane_def
      E1_def E2_def E3_def Zero_Point Ax1_1_1 Zero_Vector
      scalar_mutliplication scalar_product vector_product
      the_norm_of_a_vector orthogonal_def colin_def vec_def
      set_comprehension function_image def_of_interval
      plus_PointSet_Vector plus_Point_VectorSet plus_PointSet_VectorSet
      def_of_Circle def_of_Cylinder VLine_constr VWithLength_constr
      VPlane_constr VPlane2_constr VConnected_constr VHalfSpace_constr
      VHalfSpace2_constr VBall_constr VCircle_constr ActAttach_constr
      ActExtrude_constr pointsemantics_for_SWPoint
      vectorsemantics_for_SWPoint def_of_given_arc def_of_given_cylinder
      viewdef_of_offset viewdef_of_axis viewdef_of_C viewdef_of_radius
by auto

ML "Header.record \"nonXMinuscollapsed_cylinder\""

end
