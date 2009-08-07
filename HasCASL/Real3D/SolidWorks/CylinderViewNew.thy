theory SWCommonPatterns_SWCylByAE_IsCylinder_T
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"ga_subt_reflexive\", \"ga_subt_transitive\",
     \"ga_subt_inj_proj\", \"ga_inj_transitive\",
     \"ga_subt_NonZero_XLt_Real\", \"ga_subt_RealNonNeg_XLt_Real\",
     \"ga_subt_RealPos_XLt_Real\", \"ga_subt_SWArc_XLt_SWSketchObject\",
     \"ga_subt_SWExtrusion_XLt_SWFeature\",
     \"ga_subt_SWFeature_XLt_SWObject\",
     \"ga_subt_SWLine_XLt_SWSketchObject\",
     \"ga_subt_SWPlane_XLt_SWObject\",
     \"ga_subt_SWSketch_XLt_SWObject\",
     \"ga_subt_SWSketchObject_XLt_SWObject\",
     \"ga_subt_SWSpline_XLt_SWSketchObject\",
     \"ga_subt_VectorStar_XLt_Vector\", \"ga_subt_ZeroToNine_XLt_Real\",
     \"ga_assoc___Xx__\", \"ga_right_unit___Xx__\",
     \"ga_left_unit___Xx__\", \"inv_Group\", \"rinv_Group\",
     \"ga_comm___Xx__\", \"ga_assoc___Xx___9\",
     \"ga_right_unit___Xx___7\", \"ga_left_unit___Xx___8\",
     \"distr1_Ring\", \"distr2_Ring\", \"left_zero\", \"right_zero\",
     \"ga_comm___Xx___14\", \"noZeroDiv\", \"zeroNeqOne\",
     \"NonZero_type\", \"ga_assoc___Xx___22\",
     \"ga_right_unit___Xx___18\", \"ga_left_unit___Xx___20\",
     \"inv_Group_21\", \"rinv_Group_19\", \"binary_inverse\", \"binary_field_inverse\",
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
     \"RealPos_pred_def\", \"RealNonNeg_type\", \"RealPos_type\",
     \"abs_def\", \"times_cancel_right_nonneg_leq\",
     \"times_leq_nonneg_cond\", \"sqr_def\", \"sqrt_def\", \"Pos_def\",
     \"X2_def_Real\", \"X3_def_Real\", \"X4_def_Real\", \"X5_def_Real\",
     \"X6_def_Real\", \"X7_def_Real\", \"X8_def_Real\", \"X9_def_Real\",
     \"ZeroToNine_type\", \"decimal_def\", \"ga_select_C1\",
     \"ga_select_C2\", \"ga_select_C3\", \"Zero_Point\",
     \"Point_choice\", \"ga_select_C1_151\", \"ga_select_C2_152\",
     \"ga_select_C3_153\", \"Zero_Vector\", \"VectorStar_pred_def\",
     \"VectorStar_type\", \"def_of_vector_addition\",
     \"def_of_minus_vector\", \"binary_inverse_82\",
     \"scalar_multiplication\", \"scalar_product\", \"vector_product\",
     \"ONB1\", \"ONB2\", \"ONB3\", \"cross_left_homogenity\",
     \"cross_product_antisymmetric\", \"ga_assoc___Xx___82\",
     \"ga_right_unit___Xx___76\", \"ga_left_unit___Xx___78\",
     \"inv_Group_79\", \"rinv_Group_77\", \"ga_comm___Xx___80\",
     \"unit\", \"mix_assoc\", \"distr_Field\", \"distr_Space\",
     \"zero_by_left_zero\", \"zero_by_right_zero\",
     \"inverse_by_XMinus1\", \"no_zero_divisor\", \"distributive\",
     \"homogeneous\", \"symmetric\", \"pos_definite\",
     \"right_distributive\", \"right_homogeneous\", \"non_degenerate\",
     \"lindep_def\", \"lindep_reflexivity\", \"lindep_symmetry\",
     \"simple_lindep_condition\", \"lindep_nonlindep_transitivity\",
     \"norm_from_inner_prod_def\", \"proj_def\", \"orthcomp_def\",
     \"orthogonal_def\", \"homogeneous_93\", \"definite\",
     \"pos_definite_94\", \"pos_homogeneous\", \"orth_symmetric\",
     \"lindep_orth_transitive\", \"orthogonal_existence_theorem\",
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
     \"plane_condition_for_point_and_vector\", \"ga_select_first\",
     \"ga_select_rest\", \"ga_select_SpacePoint\",
     \"ga_select_NormalVector\", \"ga_select_InnerCS\",
     \"ga_select_Center\", \"ga_select_Start\", \"ga_select_End\",
     \"ga_select_From\", \"ga_select_To\", \"ga_select_Points\",
     \"ga_select_Objects\", \"ga_select_Plane\",
     \"ga_select_Objects_1\", \"ga_select_SkchCtrtStatus\",
     \"ga_select_Objects_2\", \"ga_select_Sketch\", \"ga_select_Depth\",
     \"E1_def\", \"E2_def\", \"E3_def\", \"VLine_constr\",
     \"VWithLength_constr\", \"VPlane_constr\", \"VPlane2_constr\",
     \"VConnected_constr\", \"VHalfSpace_constr\",
     \"VHalfSpace2_constr\", \"VBall_constr\", \"VCircle_constr\",
     \"ActAttach_constr\", \"ActExtrude_constr\", \"vwl_identity\",
     \"vwl_length\", \"vwl_lindep\", \"semantics_for_Planes\",
     \"semantics_for_SketchObject_listsXMinusBaseCase\",
     \"semantics_for_SketchObject_listsXMinusRecursiveCase\",
     \"semantics_for_Arcs\", \"semantics_for_Sketches\",
     \"semantics_for_ArcExtrusion\", \"plane_is_plane\",
     \"def_of_SWCylinder\", \"affine_cylinder_constructible_in_SW\",
     \"def_of_Cylinder\"]"

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
datatype 'a List = XOSqBrXCSqBr ("['']") |
                   X__XColonXColon__X 'a "'a List" ("(_/ ::''/ _)" [54,54] 52)
datatype SWPlane = X_SWPlane "Point" "VectorStar" "Vector"
datatype SWArc = X_SWArc "Point" "Point" "Point"
datatype SWLine = X_SWLine "Point" "Point"
datatype SWSpline = X_SWSpline "Point List"
datatype SWSketch = X_SWSketch "SWSketchObject List" "SWPlane"
datatype SWSkchCtrtParam = sgANGLE | sgARCANG180 | sgARCANG270 |
                           sgARCANG90 | sgARCANGBOTTOM | sgARCANGLEFT |
                           sgARCANGRIGHT | sgARCANGTOP | sgATINTERSECT |
                           sgATMIDDLE | sgATPIERCE | sgCOINCIDENT | sgCOLINEAR |
                           sgCONCENTRIC | sgCORADIAL | sgDIAMETER | sgDISTANCE |
                           sgFIXXED ("sgFIXED") | sgHORIZONTAL | sgHORIZPOINTS |
                           sgOFFSETEDGE | sgPARALLEL | sgPERPENDICULAR |
                           sgSAMELENGTH | sgSNAPANGLE | sgSNAPGRID |
                           sgSNAPLENGTH | sgSYMMETRIC | sgTANGENT | sgUSEEDGE |
                           sgVERTICAL | sgVERTPOINTS
datatype SWSkchCtrtStatus = X_Autosolve_off ("Autosolve'_off") |
                            X_Fully_constrained ("Fully'_constrained") |
                            X_No_solution ("No'_solution") |
                            X_Over_constrained ("Over'_constrained") |
                            X_Under_constrained ("Under'_constrained")
datatype SWSkchCtrtObject = X_SWSkchCtrtObject "SWSkchCtrtParam List"
datatype SWSkchCtrts = X_SWSkchCtrts "SWSkchCtrtStatus" "SWSkchCtrtObject List"
datatype SWExtrusion = X_SWExtrusion "SWSketch" "Real"

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
ObjectsX1 :: "SWSkchCtrtObject => SWSkchCtrtParam List" ("Objects''/'(_')" [3] 999)
ObjectsX2 :: "SWSkchCtrts => SWSkchCtrtObject List" ("Objects''''/'(_')" [3] 999)
ObjectsX3 :: "SWSketch => SWSketchObject List" ("Objects'_3/'(_')" [3] 999)
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
X_Points :: "SWSpline => Point List" ("Points/'(_')" [3] 999)
X_Pos :: "Real => bool" ("Pos/'(_')" [3] 999)
X_RealNonNeg_pred :: "Real => bool" ("RealNonNeg'_pred/'(_')" [3] 999)
X_RealPos_pred :: "Real => bool" ("RealPos'_pred/'(_')" [3] 999)
X_SWCylinder :: "Point => Point => VectorStar => SWFeature" ("SWCylinder/'(_,/ _,/ _')" [3,3,3] 999)
X_SWReal :: "Real => Real => Real" ("SWReal/'(_,/ _')" [3,3] 999)
X_SkchCtrtStatus :: "SWSkchCtrts => SWSkchCtrtStatus" ("SkchCtrtStatus/'(_')" [3] 999)
X_Sketch :: "SWExtrusion => SWSketch" ("Sketch/'(_')" [3] 999)
X_SpacePoint :: "SWPlane => Point" ("SpacePoint/'(_')" [3] 999)
X_Start :: "SWArc => Point" ("Start/'(_')" [3] 999)
X_To :: "SWLine => Point" ("To/'(_')" [3] 999)
X_VWithLength :: "Vector => Real => Vector" ("VWithLength/'(_,/ _')" [3,3] 999)
X_VectorStar_pred :: "Vector => bool" ("VectorStar'_pred/'(_')" [3] 999)
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
X_first :: "'a List => 'a partial" ("first/'(_')" [3] 999)
X_gn_inj :: "'a => 'b" ("gn'_inj/'(_')" [3] 999)
X_gn_proj :: "'a => 'b partial" ("gn'_proj/'(_')" [3] 999)
X_gn_subt :: "'a => 'b => bool" ("gn'_subt/'(_,/ _')" [3,3] 999)
X_image :: "('S => 'T) * ('S => bool) => 'T => bool"
X_inv :: "NonZero => NonZero" ("inv''/'(_')" [3] 999)
X_isX1 :: "SWSketchObject * SWPlane => Point => bool"
X_isX2 :: "SWSketchObject List * SWPlane => Point => bool"
X_lindep :: "Vector => Vector => bool" ("lindep/'(_,/ _')" [3,3] 999)
X_max :: "Real => Real => Real" ("max''/'(_,/ _')" [3,3] 999)
X_min :: "Real => Real => Real" ("min''/'(_,/ _')" [3,3] 999)
X_orth :: "Vector => Vector => bool" ("orth/'(_,/ _')" [3,3] 999)
X_orthcomp :: "Vector => Vector => Vector" ("orthcomp/'(_,/ _')" [3,3] 999)
X_proj :: "Vector => Vector => Vector" ("proj/'(_,/ _')" [3,3] 999)
X_rest :: "'a List => 'a List partial" ("rest/'(_')" [3] 999)
X_sqr :: "Real => RealNonNeg" ("sqr/'(_')" [3] 999)
X_sqrt :: "RealNonNeg => RealNonNeg" ("sqrt/'(_')" [3] 999)
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

axioms
ga_subt_reflexive [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). gn_subt((x :: 'a), (y :: 'a))"

ga_subt_transitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'b).
 ALL (z :: 'c).
 gn_subt((x :: 'a), (y :: 'b)) & gn_subt((y :: 'b), (z :: 'c)) -->
 gn_subt((x :: 'a), (z :: 'c))"

ga_subt_inj_proj [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'b).
 gn_subt((x :: 'a), (y :: 'b)) -->
 (y :: 'b) = gn_inj((x :: 'a)) =
 (makePartial (x :: 'a) =
  (X_gn_proj :: 'b => 'a partial) (y :: 'b))"

(*
 this is false, consider, e.g., 1::Real, 2::NonZero, 1'::RealPos
 we have RealPos < NonZero < Real, and 1 = gn_inj(1') but not 1 = gn_inj(2) !
*)
ga_inj_transitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'b).
 ALL (z :: 'c).
 gn_subt((x :: 'a), (y :: 'b)) & gn_subt((y :: 'b), (z :: 'c)) -->
 (z :: 'c) = gn_inj((x :: 'a)) =
 ((y :: 'b) = gn_inj((x :: 'a)) & (z :: 'c) = gn_inj((y :: 'b)))"

ga_subt_NonZero_XLt_Real [rule_format] :
"gn_subt((x :: NonZero), (y :: Real))"

ga_subt_RealNonNeg_XLt_Real [rule_format] :
"gn_subt((x :: RealNonNeg), (y :: Real))"

ga_subt_RealPos_XLt_Real [rule_format] :
"gn_subt((x :: RealPos), (y :: Real))"

ga_subt_SWArc_XLt_SWSketchObject [rule_format] :
"gn_subt((x :: SWArc), (y :: SWSketchObject))"

ga_subt_SWExtrusion_XLt_SWFeature [rule_format] :
"gn_subt((x :: SWExtrusion), (y :: SWFeature))"

ga_subt_SWFeature_XLt_SWObject [rule_format] :
"gn_subt((x :: SWFeature), (y :: SWObject))"

ga_subt_SWLine_XLt_SWSketchObject [rule_format] :
"gn_subt((x :: SWLine), (y :: SWSketchObject))"

ga_subt_SWPlane_XLt_SWObject [rule_format] :
"gn_subt((x :: SWPlane), (y :: SWObject))"

ga_subt_SWSketch_XLt_SWObject [rule_format] :
"gn_subt((x :: SWSketch), (y :: SWObject))"

ga_subt_SWSketchObject_XLt_SWObject [rule_format] :
"gn_subt((x :: SWSketchObject), (y :: SWObject))"

ga_subt_SWSpline_XLt_SWSketchObject [rule_format] :
"gn_subt((x :: SWSpline), (y :: SWSketchObject))"

ga_subt_VectorStar_XLt_Vector [rule_format] :
"gn_subt((x :: VectorStar), (y :: Vector))"

ga_subt_ZeroToNine_XLt_Real [rule_format] :
"gn_subt((x :: ZeroToNine), (y :: Real))"

ga_assoc___Xx__ [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real).
 ((x :: Real) +_3 (y :: Real)) +_3 (z :: Real) =
 (x :: Real) +_3 ((y :: Real) +_3 (z :: Real))"

ga_right_unit___Xx__ [rule_format] :
"ALL (x :: Real). (x :: Real) +_3 0'' = (x :: Real)"

ga_left_unit___Xx__ [rule_format] :
"ALL (x :: Real). 0'' +_3 (x :: Real) = (x :: Real)"

inv_Group [rule_format] :
"ALL (x :: Real). -' (x :: Real) +_3 (x :: Real) = 0''"

rinv_Group [rule_format] :
"ALL (x :: Real). (x :: Real) +_3 -' (x :: Real) = 0''"

ga_comm___Xx__ [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 (x :: Real) +_3 (y :: Real) = (y :: Real) +_3 (x :: Real)"

ga_assoc___Xx___9 [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real).
 ((x :: Real) *'' (y :: Real)) *'' (z :: Real) =
 (x :: Real) *'' ((y :: Real) *'' (z :: Real))"

ga_right_unit___Xx___7 [rule_format] :
"ALL (x :: Real). (x :: Real) *'' 1'' = (x :: Real)"

ga_left_unit___Xx___8 [rule_format] :
"ALL (x :: Real). 1'' *'' (x :: Real) = (x :: Real)"

distr1_Ring [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real).
 ((x :: Real) +_3 (y :: Real)) *'' (z :: Real) =
 ((x :: Real) *'' (z :: Real)) +_3 ((y :: Real) *'' (z :: Real))"

distr2_Ring [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real).
 (z :: Real) *'' ((x :: Real) +_3 (y :: Real)) =
 ((z :: Real) *'' (x :: Real)) +_3 ((z :: Real) *'' (y :: Real))"

left_zero [rule_format] :
"ALL (x :: Real). 0'' *'' (x :: Real) = 0''"

right_zero [rule_format] :
"ALL (x :: Real). (x :: Real) *'' 0'' = 0''"

ga_comm___Xx___14 [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 (x :: Real) *'' (y :: Real) = (y :: Real) *'' (x :: Real)"

noZeroDiv [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 (x :: Real) *'' (y :: Real) = 0'' -->
 (x :: Real) = 0'' | (y :: Real) = 0''"

zeroNeqOne [rule_format] : "~ 1'' = 0''"

NonZero_type [rule_format] :
"ALL (x :: Real).
 defOp ((X_gn_proj :: Real => NonZero partial) (x :: Real)) =
 (~ (x :: Real) = 0'')"

ga_assoc___Xx___22 [rule_format] :
"ALL (x :: NonZero).
 ALL (y :: NonZero).
 ALL (z :: NonZero).
 ((x :: NonZero) *' (y :: NonZero)) *' (z :: NonZero) =
 (x :: NonZero) *' ((y :: NonZero) *' (z :: NonZero))"

ga_right_unit___Xx___18 [rule_format] :
"ALL (x :: NonZero). (x :: NonZero) *' 1' = (x :: NonZero)"

ga_left_unit___Xx___20 [rule_format] :
"ALL (x :: NonZero). 1' *' (x :: NonZero) = (x :: NonZero)"

inv_Group_21 [rule_format] :
"ALL (x :: NonZero). inv'((x :: NonZero)) *' (x :: NonZero) = 1'"

rinv_Group_19 [rule_format] :
"ALL (x :: NonZero). (x :: NonZero) *' inv'((x :: NonZero)) = 1'"

binary_inverse [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 (x :: Real) -' (y :: Real) = (x :: Real) +_3 -' (y :: Real)"

binary_field_inverse [rule_format] :
"ALL (x :: Real).
 ALL (y :: NonZero).
 (x :: Real) /' (y :: NonZero) =
 (x :: Real) *'' gn_inj(inv'((y :: NonZero)))"

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
 (a :: Real) +_3 (c :: Real) <=' (b :: Real) +_3 (c :: Real)"

FWO_times_left [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real).
 (a :: Real) <=' (b :: Real) & 0'' <=' (c :: Real) -->
 (a :: Real) *'' (c :: Real) <=' (b :: Real) *'' (c :: Real)"

FWO_plus_right [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real).
 (b :: Real) <=' (c :: Real) -->
 (a :: Real) +_3 (b :: Real) <=' (a :: Real) +_3 (c :: Real)"

FWO_times_right [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real).
 (b :: Real) <=' (c :: Real) & 0'' <=' (a :: Real) -->
 (a :: Real) *'' (b :: Real) <=' (a :: Real) *'' (c :: Real)"

FWO_plus [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real).
 ALL (d :: Real).
 (a :: Real) <=' (c :: Real) & (b :: Real) <=' (d :: Real) -->
 (a :: Real) +_3 (b :: Real) <=' (c :: Real) +_3 (d :: Real)"

inf_def [rule_format] :
"ALL (S :: Real => bool).
 ALL (m :: Real).
 inf''((S :: Real => bool)) = makePartial (m :: Real) =
 (ALL (m2 :: Real).
  (ALL (x :: Real).
   (S :: Real => bool) (x :: Real) -->
   (x :: Real) <=' (m2 :: Real)) -->
  (m :: Real) <=' (m2 :: Real))"

Real_completeness [rule_format] :
"ALL (S :: Real => bool).
 (EX (x :: Real). (S :: Real => bool) (x :: Real)) &
 (EX (B :: Real).
  ALL (x :: Real).
  (S :: Real => bool) (x :: Real) -->
  (x :: Real) <=' (B :: Real)) -->
 (EX (m :: Real).
  makePartial (m :: Real) = inf''((S :: Real => bool)))"

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
 sup((x :: Real), (y :: Real)) = sup((y :: Real), (x :: Real))"

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
 sup((x :: Real), (y :: Real)) = makePartial (z :: Real) =
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
 sup((x :: Real), (y :: Real))"

RealNonNeg_pred_def [rule_format] :
"ALL (x :: Real).
 RealNonNeg_pred((x :: Real)) = ((x :: Real) >=' 0'')"

RealPos_pred_def [rule_format] :
"ALL (x :: Real). RealPos_pred((x :: Real)) = ((x :: Real) >' 0'')"

RealNonNeg_type [rule_format] :
"ALL (x :: Real).
 defOp ((X_gn_proj :: Real => RealNonNeg partial) (x :: Real)) =
 RealNonNeg_pred((x :: Real))"

RealPos_type [rule_format] :
"ALL (x :: Real).
 defOp ((X_gn_proj :: Real => RealPos partial) (x :: Real)) =
 RealPos_pred((x :: Real))"

abs_def [rule_format] :
"ALL (x :: Real).
 makePartial (abs'((x :: Real))) =
 (if 0'' <=' (x :: Real)
     then (X_gn_proj :: Real => RealNonNeg partial) (x :: Real)
     else (X_gn_proj :: Real => RealNonNeg partial) (-' (x :: Real)))"

times_cancel_right_nonneg_leq [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real).
 (a :: Real) *'' (b :: Real) <=' (c :: Real) *'' (b :: Real) &
 (b :: Real) >=' 0'' -->
 (a :: Real) <=' (c :: Real)"

times_leq_nonneg_cond [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 0'' <=' (a :: Real) *'' (b :: Real) & (b :: Real) >=' 0'' -->
 0'' <=' (a :: Real)"

sqr_def [rule_format] :
"ALL (r :: Real).
 gn_inj(sqr((r :: Real))) =
 makePartial ((r :: Real) *'' (r :: Real))"

sqrt_def [rule_format] :
"ALL (q :: RealNonNeg).
 sqr(gn_inj(sqrt((q :: RealNonNeg)))) = (q :: RealNonNeg)"

Pos_def [rule_format] :
"ALL (x :: Real). Pos((x :: Real)) = (0'' <=' (x :: Real))"

X2_def_Real [rule_format] : "2' = gn_inj(1') +_3 gn_inj(1')"

X3_def_Real [rule_format] : "3' = 2' +_3 gn_inj(1')"

X4_def_Real [rule_format] : "4' = 3' +_3 gn_inj(1')"

X5_def_Real [rule_format] : "5' = 4' +_3 gn_inj(1')"

X6_def_Real [rule_format] : "6' = 5' +_3 gn_inj(1')"

X7_def_Real [rule_format] : "7' = 6' +_3 gn_inj(1')"

X8_def_Real [rule_format] : "8' = 7' +_3 gn_inj(1')"

X9_def_Real [rule_format] : "9' = 8' +_3 gn_inj(1')"

ZeroToNine_type [rule_format] :
"ALL (x :: Real).
 defOp ((X_gn_proj :: Real => ZeroToNine partial) (x :: Real)) =
 ((((((((((x :: Real) = 0'' |
          makePartial (x :: Real) = gn_inj(1')) |
         (x :: Real) = 2') |
        (x :: Real) = 3') |
       (x :: Real) = 4') |
      (x :: Real) = 5') |
     (x :: Real) = 6') |
    (x :: Real) = 7') |
   (x :: Real) = 8') |
  (x :: Real) = 9')"

decimal_def [rule_format] :
"ALL (m :: ZeroToNine).
 ALL (X_n :: Real).
 (m :: ZeroToNine) @@ (X_n :: Real) =
 (gn_inj((m :: ZeroToNine)) *'' (9' +_3 gn_inj(1'))) +_3
 (X_n :: Real)"

ga_select_C1 [rule_format] :
"ALL (x_1 :: Real).
 ALL (x_2 :: Real).
 ALL (x_3 :: Real).
 C1'(P((x_1 :: Real), (x_2 :: Real), (x_3 :: Real))) =
 (x_1 :: Real)"

ga_select_C2 [rule_format] :
"ALL (x_1 :: Real).
 ALL (x_2 :: Real).
 ALL (x_3 :: Real).
 C2'(P((x_1 :: Real), (x_2 :: Real), (x_3 :: Real))) =
 (x_2 :: Real)"

ga_select_C3 [rule_format] :
"ALL (x_1 :: Real).
 ALL (x_2 :: Real).
 ALL (x_3 :: Real).
 C3'(P((x_1 :: Real), (x_2 :: Real), (x_3 :: Real))) =
 (x_3 :: Real)"

Zero_Point [rule_format] : "0' = P(0'', 0'', 0'')"

Point_choice [rule_format] :
"ALL (X_P :: Point => bool).
 (EX (y :: Point). (X_P :: Point => bool) (y :: Point)) -->
 (X_P :: Point => bool) (choose'((X_P :: Point => bool)))"

ga_select_C1_151 [rule_format] :
"ALL (x_1 :: Real).
 ALL (x_2 :: Real).
 ALL (x_3 :: Real).
 C1''(V((x_1 :: Real), (x_2 :: Real), (x_3 :: Real))) =
 (x_1 :: Real)"

ga_select_C2_152 [rule_format] :
"ALL (x_1 :: Real).
 ALL (x_2 :: Real).
 ALL (x_3 :: Real).
 C2''(V((x_1 :: Real), (x_2 :: Real), (x_3 :: Real))) =
 (x_2 :: Real)"

ga_select_C3_153 [rule_format] :
"ALL (x_1 :: Real).
 ALL (x_2 :: Real).
 ALL (x_3 :: Real).
 C3''(V((x_1 :: Real), (x_2 :: Real), (x_3 :: Real))) =
 (x_3 :: Real)"

Zero_Vector [rule_format] : "0_3 = V(0'', 0'', 0'')"

VectorStar_pred_def [rule_format] :
"ALL (x :: Vector).
 VectorStar_pred((x :: Vector)) = (~ (x :: Vector) = 0_3)"

VectorStar_type [rule_format] :
"ALL (x :: Vector).
 defOp ((X_gn_proj :: Vector => VectorStar partial) (x :: Vector)) =
 VectorStar_pred((x :: Vector))"

def_of_vector_addition [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 (x :: Vector) +_4 (y :: Vector) =
 V(C1''((x :: Vector)) +_3 C1''((y :: Vector)),
 C2''((x :: Vector)) +_3 C2''((y :: Vector)),
 C3''((x :: Vector)) +_3 C3''((y :: Vector)))"

def_of_minus_vector [rule_format] :
"ALL (x :: Vector).
 -'' (x :: Vector) =
 V(-' C1''((x :: Vector)), -' C2''((x :: Vector)),
 -' C3''((x :: Vector)))"

binary_inverse_82 [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 (x :: Vector) -'' (y :: Vector) =
 (x :: Vector) +_4 -'' (y :: Vector)"

scalar_multiplication [rule_format] :
"ALL (x :: Real).
 ALL (y :: Vector).
 (x :: Real) *_3 (y :: Vector) =
 V((x :: Real) *'' C1''((y :: Vector)),
 (x :: Real) *'' C2''((y :: Vector)),
 (x :: Real) *'' C3''((y :: Vector)))"

scalar_product [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 (x :: Vector) *_4 (y :: Vector) =
 ((C1''((x :: Vector)) *'' C1''((y :: Vector))) +_3
  (C2''((x :: Vector)) *'' C2''((y :: Vector))))
 +_3 (C3''((x :: Vector)) *'' C3''((y :: Vector)))"

vector_product [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 (x :: Vector) #' (y :: Vector) =
 V((C2''((x :: Vector)) *'' C3''((y :: Vector))) -'
   (C2''((y :: Vector)) *'' C3''((x :: Vector))),
 (C3''((x :: Vector)) *'' C1''((y :: Vector))) -'
 (C3''((y :: Vector)) *'' C1''((x :: Vector))),
 (C1''((x :: Vector)) *'' C2''((y :: Vector))) -'
 (C1''((y :: Vector)) *'' C2''((x :: Vector))))"

ONB1 [rule_format] : "e1 = V(gn_inj(1'), 0'', 0'')"

ONB2 [rule_format] : "e2 = V(0'', gn_inj(1'), 0'')"

ONB3 [rule_format] : "e3 = V(0'', 0'', gn_inj(1'))"

cross_left_homogenity [rule_format] :
"ALL (r :: Real).
 ALL (x :: Vector).
 ALL (y :: Vector).
 (r :: Real) *_3 ((x :: Vector) #' (y :: Vector)) =
 ((r :: Real) *_3 (x :: Vector)) #' (y :: Vector)"

cross_product_antisymmetric [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 (x :: Vector) #' (y :: Vector) =
 -'' ((y :: Vector) #' (x :: Vector))"

ga_assoc___Xx___82 [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 ALL (z :: Vector).
 ((x :: Vector) +_4 (y :: Vector)) +_4 (z :: Vector) =
 (x :: Vector) +_4 ((y :: Vector) +_4 (z :: Vector))"

ga_right_unit___Xx___76 [rule_format] :
"ALL (x :: Vector). (x :: Vector) +_4 0_3 = (x :: Vector)"

ga_left_unit___Xx___78 [rule_format] :
"ALL (x :: Vector). 0_3 +_4 (x :: Vector) = (x :: Vector)"

inv_Group_79 [rule_format] :
"ALL (x :: Vector). -'' (x :: Vector) +_4 (x :: Vector) = 0_3"

rinv_Group_77 [rule_format] :
"ALL (x :: Vector). (x :: Vector) +_4 -'' (x :: Vector) = 0_3"

ga_comm___Xx___80 [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 (x :: Vector) +_4 (y :: Vector) = (y :: Vector) +_4 (x :: Vector)"

unit [rule_format] :
"ALL (x :: Vector). gn_inj(1') *_3 (x :: Vector) = (x :: Vector)"

mix_assoc [rule_format] :
"ALL (r :: Real).
 ALL (s :: Real).
 ALL (x :: Vector).
 ((r :: Real) *'' (s :: Real)) *_3 (x :: Vector) =
 (r :: Real) *_3 ((s :: Real) *_3 (x :: Vector))"

distr_Field [rule_format] :
"ALL (r :: Real).
 ALL (s :: Real).
 ALL (x :: Vector).
 ((r :: Real) +_3 (s :: Real)) *_3 (x :: Vector) =
 ((r :: Real) *_3 (x :: Vector)) +_4
 ((s :: Real) *_3 (x :: Vector))"

distr_Space [rule_format] :
"ALL (r :: Real).
 ALL (x :: Vector).
 ALL (y :: Vector).
 (r :: Real) *_3 ((x :: Vector) +_4 (y :: Vector)) =
 ((r :: Real) *_3 (x :: Vector)) +_4
 ((r :: Real) *_3 (y :: Vector))"

zero_by_left_zero [rule_format] :
"ALL (x :: Vector). 0'' *_3 (x :: Vector) = 0_3"

zero_by_right_zero [rule_format] :
"ALL (r :: Real). (r :: Real) *_3 0_3 = 0_3"

inverse_by_XMinus1 [rule_format] :
"ALL (x :: Vector).
 -' gn_inj(1') *_3 (x :: Vector) = -'' (x :: Vector)"

no_zero_divisor [rule_format] :
"ALL (r :: Real).
 ALL (x :: Vector).
 ~ (r :: Real) = 0'' & ~ (x :: Vector) = 0_3 -->
 ~ (r :: Real) *_3 (x :: Vector) = 0_3"

distributive [rule_format] :
"ALL (v :: Vector).
 ALL (v' :: Vector).
 ALL (w :: Vector).
 ((v :: Vector) +_4 (v' :: Vector)) *_4 (w :: Vector) =
 ((v :: Vector) *_4 (w :: Vector)) +_3
 ((v' :: Vector) *_4 (w :: Vector))"

homogeneous [rule_format] :
"ALL (a :: Real).
 ALL (v :: Vector).
 ALL (w :: Vector).
 ((a :: Real) *_3 (v :: Vector)) *_4 (w :: Vector) =
 (a :: Real) *'' ((v :: Vector) *_4 (w :: Vector))"

symmetric [rule_format] :
"ALL (v :: Vector).
 ALL (w :: Vector).
 (v :: Vector) *_4 (w :: Vector) = (w :: Vector) *_4 (v :: Vector)"

pos_definite [rule_format] :
"ALL (v :: Vector).
 ~ (v :: Vector) = 0_3 --> (v :: Vector) *_4 (v :: Vector) >' 0''"

right_distributive [rule_format] :
"ALL (v :: Vector).
 ALL (v' :: Vector).
 ALL (w :: Vector).
 (w :: Vector) *_4 ((v :: Vector) +_4 (v' :: Vector)) =
 ((w :: Vector) *_4 (v :: Vector)) +_3
 ((w :: Vector) *_4 (v' :: Vector))"

right_homogeneous [rule_format] :
"ALL (a :: Real).
 ALL (v :: Vector).
 ALL (w :: Vector).
 (v :: Vector) *_4 ((a :: Real) *_3 (w :: Vector)) =
 (a :: Real) *'' ((v :: Vector) *_4 (w :: Vector))"

non_degenerate [rule_format] :
"ALL (v :: Vector).
 (v :: Vector) *_4 (v :: Vector) = 0'' --> (v :: Vector) = 0_3"

lindep_def [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 lindep((x :: Vector), (y :: Vector)) =
 ((y :: Vector) = 0_3 |
  (EX (r :: Real). (x :: Vector) = (r :: Real) *_3 (y :: Vector)))"

lindep_reflexivity [rule_format] :
"ALL (x :: Vector). lindep((x :: Vector), (x :: Vector))"

lindep_symmetry [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 lindep((x :: Vector), (y :: Vector)) -->
 lindep((y :: Vector), (x :: Vector))"

simple_lindep_condition [rule_format] :
"ALL (r :: Real).
 ALL (x :: Vector).
 ALL (y :: Vector).
 (x :: Vector) = (r :: Real) *_3 (y :: Vector) -->
 lindep((x :: Vector), (y :: Vector))"

lindep_nonlindep_transitivity [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 ALL (z :: Vector).
 (~ (x :: Vector) = 0_3 & lindep((x :: Vector), (y :: Vector))) &
 ~ lindep((y :: Vector), (z :: Vector)) -->
 ~ lindep((x :: Vector), (z :: Vector))"

norm_from_inner_prod_def [rule_format] :
"ALL (x :: Vector).
 makePartial ( || (x :: Vector) || ) =
 restrictOp
 ((X_gn_proj :: RealNonNeg => Real partial)
  (sqrt(makeTotal
        ((X_gn_proj :: Real => RealNonNeg partial)
         ((x :: Vector) *_4 (x :: Vector))))))
 (defOp
  ((X_gn_proj :: Real => RealNonNeg partial)
   ((x :: Vector) *_4 (x :: Vector))))"

proj_def [rule_format] :
"ALL (v :: Vector).
 ALL (w :: Vector).
 makePartial (proj((v :: Vector), (w :: Vector))) =
 (if (w :: Vector) = 0_3 then makePartial 0_3
     else restrictOp
          (makePartial
           ((((v :: Vector) *_4 (w :: Vector)) /'
             makeTotal
             ((X_gn_proj :: Real => NonZero partial)
              ((w :: Vector) *_4 (w :: Vector))))
            *_3 (w :: Vector)))
          (defOp
           ((X_gn_proj :: Real => NonZero partial)
            ((w :: Vector) *_4 (w :: Vector)))))"

orthcomp_def [rule_format] :
"ALL (v :: Vector).
 ALL (w :: Vector).
 orthcomp((v :: Vector), (w :: Vector)) =
 (v :: Vector) -'' proj((v :: Vector), (w :: Vector))"

orthogonal_def [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 orth((x :: Vector), (y :: Vector)) =
 ((x :: Vector) *_4 (y :: Vector) = 0'')"

homogeneous_93 [rule_format] :
"ALL (r :: Real).
 ALL (v :: Vector).
 || (r :: Real) *_3 (v :: Vector) || =
 gn_inj(abs'((r :: Real))) *'' || (v :: Vector) ||"

definite [rule_format] :
"ALL (v :: Vector).
 || (v :: Vector) || = 0'' = ((v :: Vector) = 0_3)"

pos_definite_94 [rule_format] :
"ALL (v :: Vector). 0'' <=' || (v :: Vector) ||"

pos_homogeneous [rule_format] :
"ALL (r :: Real).
 ALL (v :: Vector).
 (r :: Real) >=' 0'' -->
 || (r :: Real) *_3 (v :: Vector) || =
 (r :: Real) *'' || (v :: Vector) ||"

orth_symmetric [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 orth((x :: Vector), (y :: Vector)) -->
 orth((y :: Vector), (x :: Vector))"

lindep_orth_transitive [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 ALL (z :: Vector).
 lindep((x :: Vector), (y :: Vector)) &
 orth((y :: Vector), (z :: Vector)) -->
 orth((x :: Vector), (z :: Vector))"

orthogonal_existence_theorem [rule_format] :
"ALL (x :: Vector).
 (EX (a :: Vector).
  EX (b :: Vector). ~ lindep((a :: Vector), (b :: Vector))) -->
 (EX (c :: Vector).
  ~ (c :: Vector) = 0_3 & orth((c :: Vector), (x :: Vector)))"

orthogonal_on_zero_projection [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 proj((x :: Vector), (y :: Vector)) = 0_3 -->
 orth((x :: Vector), (y :: Vector))"

orthogonal_projection_theorem [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 orth(orthcomp((x :: Vector), (y :: Vector)), (y :: Vector))"

orthogonal_decomposition_theorem [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 proj((x :: Vector), (y :: Vector)) +_4
 orthcomp((x :: Vector), (y :: Vector)) =
 (x :: Vector)"

unique_orthogonal_decomposition [rule_format] :
"ALL (v :: Vector).
 ALL (w :: Vector).
 ALL (x :: Vector).
 ALL (y :: Vector).
 ALL (z :: Vector).
 ((((~ (z :: Vector) = 0_3 &
     (x :: Vector) +_4 (y :: Vector) =
     (v :: Vector) +_4 (w :: Vector)) &
    lindep((x :: Vector), (z :: Vector))) &
   lindep((v :: Vector), (z :: Vector))) &
  orth((z :: Vector), (y :: Vector))) &
 orth((z :: Vector), (w :: Vector)) -->
 (x :: Vector) = (v :: Vector) & (y :: Vector) = (w :: Vector)"

cross_product_orthogonal [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 orth((x :: Vector), (x :: Vector) #' (y :: Vector))"

cross_product_zero_iff_lindep [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 lindep((x :: Vector), (y :: Vector)) =
 ((x :: Vector) #' (y :: Vector) = 0_3)"

e1e2_nonlindep [rule_format] : "~ lindep(e1, e2)"

point_vector_map [rule_format] :
"ALL (p :: Point).
 ALL (v :: Vector).
 (p :: Point) +' (v :: Vector) =
 P(C1'((p :: Point)) +_3 C1''((v :: Vector)),
 C2'((p :: Point)) +_3 C2''((v :: Vector)),
 C3'((p :: Point)) +_3 C3''((v :: Vector)))"

plus_injective [rule_format] :
"ALL (p :: Point).
 ALL (v :: Vector).
 ALL (w :: Vector).
 (p :: Point) +' (v :: Vector) = (p :: Point) +' (w :: Vector) -->
 (v :: Vector) = (w :: Vector)"

plus_surjective [rule_format] :
"ALL (p :: Point).
 ALL (q :: Point).
 EX (y :: Vector). (p :: Point) +' (y :: Vector) = (q :: Point)"

point_vector_plus_associative [rule_format] :
"ALL (p :: Point).
 ALL (v :: Vector).
 ALL (w :: Vector).
 (p :: Point) +' ((v :: Vector) +_4 (w :: Vector)) =
 ((p :: Point) +' (v :: Vector)) +' (w :: Vector)"

vec_def [rule_format] :
"ALL (p :: Point).
 ALL (q :: Point).
 (p :: Point) +' vec((p :: Point), (q :: Point)) = (q :: Point)"

transitivity_of_vec_plus [rule_format] :
"ALL (p :: Point).
 ALL (q :: Point).
 ALL (r :: Point).
 vec((p :: Point), (q :: Point)) +_4
 vec((q :: Point), (r :: Point)) =
 vec((p :: Point), (r :: Point))"

plus_vec_identity [rule_format] :
"ALL (p :: Point).
 ALL (q :: Point).
 ALL (v :: Vector).
 (p :: Point) +' (v :: Vector) = (q :: Point) -->
 (v :: Vector) = vec((p :: Point), (q :: Point))"

set_comprehension [rule_format] :
"ALL (s :: 'S => bool).
 XLBrace__XRBrace (s :: 'S => bool) = (s :: 'S => bool)"

abbrev_of_set_comprehension [rule_format] :
"setFromProperty = XLBrace__XRBrace"

function_image [rule_format] :
"ALL (XX :: 'S => bool).
 ALL (f :: 'S => 'T).
 X_image ((f :: 'S => 'T), (XX :: 'S => bool)) =
 (% (x :: 'T). EX (y :: 'S).
               (y :: 'S) isIn (XX :: 'S => bool) &
               (f :: 'S => 'T) (y :: 'S) = (x :: 'T))"

emptySet_empty [rule_format] :
"ALL (x :: 'S). ~ (x :: 'S) isIn X_emptySet"

allSet_contains_all [rule_format] :
"ALL (x :: 'S). (x :: 'S) isIn X_allSet"

def_of_isIn [rule_format] :
"ALL (s :: 'S => bool).
 ALL (x :: 'S).
 ((x :: 'S) isIn (s :: 'S => bool)) = (s :: 'S => bool) (x :: 'S)"

def_of_subset [rule_format] :
"ALL (s :: 'S => bool).
 ALL (s' :: 'S => bool).
 ((s :: 'S => bool) subset (s' :: 'S => bool)) =
 (ALL (x :: 'S).
  (x :: 'S) isIn (s :: 'S => bool) -->
  (x :: 'S) isIn (s' :: 'S => bool))"

def_of_union [rule_format] :
"ALL (s :: 'S => bool).
 ALL (s' :: 'S => bool).
 ALL (x :: 'S).
 ((x :: 'S) isIn
  X__union__X ((s :: 'S => bool), (s' :: 'S => bool))) =
 ((x :: 'S) isIn (s :: 'S => bool) |
  (x :: 'S) isIn (s' :: 'S => bool))"

def_of_bigunion [rule_format] :
"ALL (XXXX :: ('S => bool) => bool).
 ALL (x :: 'S).
 ((x :: 'S) isIn bigunion (XXXX :: ('S => bool) => bool)) =
 (EX (XX :: 'S => bool).
  (XX :: 'S => bool) isIn (XXXX :: ('S => bool) => bool) &
  (x :: 'S) isIn (XX :: 'S => bool))"

def_of_intersection [rule_format] :
"ALL (s :: 'S => bool).
 ALL (s' :: 'S => bool).
 ALL (x :: 'S).
 ((x :: 'S) isIn
  X__intersection__X ((s :: 'S => bool), (s' :: 'S => bool))) =
 ((x :: 'S) isIn (s :: 'S => bool) &
  (x :: 'S) isIn (s' :: 'S => bool))"

def_of_difference [rule_format] :
"ALL (s :: 'S => bool).
 ALL (s' :: 'S => bool).
 ALL (x :: 'S).
 ((x :: 'S) isIn
  X__XBslashXBslash__X ((s :: 'S => bool), (s' :: 'S => bool))) =
 ((x :: 'S) isIn (s :: 'S => bool) &
  ~ (x :: 'S) isIn (s' :: 'S => bool))"

def_of_disjoint [rule_format] :
"ALL (s :: 'S => bool).
 ALL (s' :: 'S => bool).
 ((s :: 'S => bool) disjoint (s' :: 'S => bool)) =
 (X__intersection__X ((s :: 'S => bool), (s' :: 'S => bool)) =
  X_emptySet)"

def_of_productset [rule_format] :
"ALL (s :: 'S => bool).
 ALL (t :: 'T => bool).
 ALL (x :: 'S).
 ALL (y :: 'T).
 (((x :: 'S), (y :: 'T)) isIn
  X__Xx__XX5 ((s :: 'S => bool), (t :: 'T => bool))) =
 ((x :: 'S) isIn (s :: 'S => bool) &
  (y :: 'T) isIn (t :: 'T => bool))"

emptySet_union_right_unit [rule_format] :
"ALL (a :: 'S => bool).
 X__union__X ((a :: 'S => bool), X_emptySet) = (a :: 'S => bool)"

function_image_structure [rule_format] :
"ALL (a :: 'S => bool).
 ALL (f :: 'S => 'T).
 ALL (x :: 'T).
 ((x :: 'T) isIn X_image ((f :: 'S => 'T), (a :: 'S => bool))) =
 (EX (y :: 'S).
  (y :: 'S) isIn (a :: 'S => bool) &
  (f :: 'S => 'T) (y :: 'S) = (x :: 'T))"

def_of_interval [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 XOSqBr__XPeriodXPeriodXPeriod__XCSqBr ((a :: Real), (b :: Real)) =
 (% (r :: Real). (r :: Real) >=' (a :: Real) &
                 (r :: Real) <=' (b :: Real))"

abbrev_of_interval [rule_format] :
"closedinterval = XOSqBr__XPeriodXPeriodXPeriod__XCSqBr"

plus_PointSet_Vector [rule_format] :
"ALL (X_P :: Point => bool).
 ALL (v :: Vector).
 X__XPlus__XX5 ((X_P :: Point => bool), (v :: Vector)) =
 X_image
 (% (x :: Point). (x :: Point) +' (v :: Vector),
  (X_P :: Point => bool))"

plus_Point_VectorSet [rule_format] :
"ALL (X_V :: Vector => bool).
 ALL (p :: Point).
 X__XPlus__XX2 ((p :: Point), (X_V :: Vector => bool)) =
 X_image
 (% (x :: Vector). (p :: Point) +' (x :: Vector),
  (X_V :: Vector => bool))"

plus_PointSet_VectorSet [rule_format] :
"ALL (X_P :: Point => bool).
 ALL (X_V :: Vector => bool).
 X__XPlus__XX6 ((X_P :: Point => bool), (X_V :: Vector => bool)) =
 bigunion
 (X_image
  (% (x :: Vector). X__XPlus__XX5
                    ((X_P :: Point => bool), (x :: Vector)),
   (X_V :: Vector => bool)))"

def_of_Plane [rule_format] :
"ALL (normal :: VectorStar).
 ALL (offset :: Point).
 PlaneX2 ((offset :: Point), (normal :: VectorStar)) =
 (% (x :: Point). orth(vec((x :: Point), (offset :: Point)),
                  gn_inj((normal :: VectorStar))))"

plane_condition_for_2_points [rule_format] :
"ALL (normal :: VectorStar).
 ALL (offset :: Point).
 ALL (x :: Point).
 ALL (y :: Point).
 let (plane :: Point => bool) =
     PlaneX2 ((offset :: Point), (normal :: VectorStar))
 in (x :: Point) isIn (plane :: Point => bool) &
    (y :: Point) isIn (plane :: Point => bool) -->
    orth(vec((x :: Point), (y :: Point)),
    gn_inj((normal :: VectorStar)))"

plane_condition_for_point_and_vector [rule_format] :
"ALL (normal :: VectorStar).
 ALL (offset :: Point).
 ALL (v :: Vector).
 ALL (x :: Point).
 let (plane :: Point => bool) =
     PlaneX2 ((offset :: Point), (normal :: VectorStar))
 in (x :: Point) isIn (plane :: Point => bool) &
    orth((v :: Vector), gn_inj((normal :: VectorStar))) -->
    (x :: Point) +' (v :: Vector) isIn (plane :: Point => bool)"

ga_select_first [rule_format] :
"ALL (x_1 :: 'a).
 ALL (x_2 :: 'a List).
 first((x_1 :: 'a) ::' (x_2 :: 'a List)) = makePartial (x_1 :: 'a)"

ga_select_rest [rule_format] :
"ALL (x_1 :: 'a).
 ALL (x_2 :: 'a List).
 rest((x_1 :: 'a) ::' (x_2 :: 'a List)) =
 makePartial (x_2 :: 'a List)"

ga_select_SpacePoint [rule_format] :
"ALL (x_1 :: Point).
 ALL (x_2 :: VectorStar).
 ALL (x_3 :: Vector).
 SpacePoint(X_SWPlane (x_1 :: Point) (x_2 :: VectorStar)
            (x_3 :: Vector)) =
 (x_1 :: Point)"

ga_select_NormalVector [rule_format] :
"ALL (x_1 :: Point).
 ALL (x_2 :: VectorStar).
 ALL (x_3 :: Vector).
 NormalVector(X_SWPlane (x_1 :: Point) (x_2 :: VectorStar)
              (x_3 :: Vector)) =
 (x_2 :: VectorStar)"

ga_select_InnerCS [rule_format] :
"ALL (x_1 :: Point).
 ALL (x_2 :: VectorStar).
 ALL (x_3 :: Vector).
 InnerCS(X_SWPlane (x_1 :: Point) (x_2 :: VectorStar)
         (x_3 :: Vector)) =
 (x_3 :: Vector)"

ga_select_Center [rule_format] :
"ALL (x_1 :: Point).
 ALL (x_2 :: Point).
 ALL (x_3 :: Point).
 Center(X_SWArc (x_1 :: Point) (x_2 :: Point) (x_3 :: Point)) =
 (x_1 :: Point)"

ga_select_Start [rule_format] :
"ALL (x_1 :: Point).
 ALL (x_2 :: Point).
 ALL (x_3 :: Point).
 Start(X_SWArc (x_1 :: Point) (x_2 :: Point) (x_3 :: Point)) =
 (x_2 :: Point)"

ga_select_End [rule_format] :
"ALL (x_1 :: Point).
 ALL (x_2 :: Point).
 ALL (x_3 :: Point).
 End(X_SWArc (x_1 :: Point) (x_2 :: Point) (x_3 :: Point)) =
 (x_3 :: Point)"

ga_select_From [rule_format] :
"ALL (x_1 :: Point).
 ALL (x_2 :: Point).
 From(X_SWLine (x_1 :: Point) (x_2 :: Point)) = (x_1 :: Point)"

ga_select_To [rule_format] :
"ALL (x_1 :: Point).
 ALL (x_2 :: Point).
 To(X_SWLine (x_1 :: Point) (x_2 :: Point)) = (x_2 :: Point)"

ga_select_Points [rule_format] :
"ALL (x_1 :: Point List).
 Points(X_SWSpline (x_1 :: Point List)) = (x_1 :: Point List)"

ga_select_Objects [rule_format] :
"ALL (x_1 :: SWSketchObject List).
 ALL (x_2 :: SWPlane).
 Objects_3(X_SWSketch (x_1 :: SWSketchObject List)
           (x_2 :: SWPlane)) =
 (x_1 :: SWSketchObject List)"

ga_select_Plane [rule_format] :
"ALL (x_1 :: SWSketchObject List).
 ALL (x_2 :: SWPlane).
 Plane'(X_SWSketch (x_1 :: SWSketchObject List) (x_2 :: SWPlane)) =
 (x_2 :: SWPlane)"

ga_select_Objects_1 [rule_format] :
"ALL (x_1 :: SWSkchCtrtParam List).
 Objects'(X_SWSkchCtrtObject (x_1 :: SWSkchCtrtParam List)) =
 (x_1 :: SWSkchCtrtParam List)"

ga_select_SkchCtrtStatus [rule_format] :
"ALL (x_1 :: SWSkchCtrtStatus).
 ALL (x_2 :: SWSkchCtrtObject List).
 SkchCtrtStatus(X_SWSkchCtrts (x_1 :: SWSkchCtrtStatus)
                (x_2 :: SWSkchCtrtObject List)) =
 (x_1 :: SWSkchCtrtStatus)"

ga_select_Objects_2 [rule_format] :
"ALL (x_1 :: SWSkchCtrtStatus).
 ALL (x_2 :: SWSkchCtrtObject List).
 Objects''(X_SWSkchCtrts (x_1 :: SWSkchCtrtStatus)
           (x_2 :: SWSkchCtrtObject List)) =
 (x_2 :: SWSkchCtrtObject List)"

ga_select_Sketch [rule_format] :
"ALL (x_1 :: SWSketch).
 ALL (x_2 :: Real).
 Sketch(X_SWExtrusion (x_1 :: SWSketch) (x_2 :: Real)) =
 (x_1 :: SWSketch)"

ga_select_Depth [rule_format] :
"ALL (x_1 :: SWSketch).
 ALL (x_2 :: Real).
 Depth(X_SWExtrusion (x_1 :: SWSketch) (x_2 :: Real)) =
 (x_2 :: Real)"

E1_def [rule_format] :
"makePartial E1 =
 restrictOp
 (makePartial
  (X_SWPlane (P(0'', 0'', 0''))
   (makeTotal
    ((X_gn_proj :: Vector => VectorStar partial)
     (V(0'', 0'', gn_inj(1')))))
   (V(gn_inj(1'), 0'', 0''))))
 (defOp
  ((X_gn_proj :: Vector => VectorStar partial)
   (V(0'', 0'', gn_inj(1')))))"

E2_def [rule_format] :
"makePartial E2 =
 restrictOp
 (makePartial
  (X_SWPlane (P(0'', 0'', 0''))
   (makeTotal
    ((X_gn_proj :: Vector => VectorStar partial)
     (V(0'', gn_inj(1'), 0''))))
   (V(gn_inj(1'), 0'', 0''))))
 (defOp
  ((X_gn_proj :: Vector => VectorStar partial)
   (V(0'', gn_inj(1'), 0''))))"

E3_def [rule_format] :
"makePartial E3 =
 restrictOp
 (makePartial
  (X_SWPlane (P(0'', 0'', 0''))
   (makeTotal
    ((X_gn_proj :: Vector => VectorStar partial)
     (V(gn_inj(1'), 0'', 0''))))
   (V(0'', gn_inj(1'), 0''))))
 (defOp
  ((X_gn_proj :: Vector => VectorStar partial)
   (V(gn_inj(1'), 0'', 0''))))"

VLine_constr [rule_format] :
"ALL (p1 :: Vector).
 ALL (p2 :: Vector).
 VLine ((p1 :: Vector), (p2 :: Vector)) =
 X_image
 (% (y :: Real). (p1 :: Vector) +_4
                 ((y :: Real) *_3 ((p2 :: Vector) -'' (p1 :: Vector))),
  closedinterval (0'', gn_inj(1')))"

VWithLength_constr [rule_format] :
"ALL (s :: Real).
 ALL (v :: Vector).
 makePartial (VWithLength((v :: Vector), (s :: Real))) =
 (if (v :: Vector) = 0_3 then makePartial (v :: Vector)
     else restrictOp
          (makePartial
           (((s :: Real) /'
             makeTotal
             ((X_gn_proj :: Real => NonZero partial) ( || (v :: Vector) || )))
            *_3 (v :: Vector)))
          (defOp
           ((X_gn_proj :: Real => NonZero partial) ( || (v :: Vector) || ))))"

VPlane_constr [rule_format] :
"ALL (normal :: Vector).
 VPlane (normal :: Vector) =
 (% (y :: Vector). orth((y :: Vector), (normal :: Vector)))"

VPlane2_constr [rule_format] :
"ALL (axis1 :: Vector).
 ALL (axis2 :: Vector).
 VPlane2 ((axis1 :: Vector), (axis2 :: Vector)) =
 VPlane ((axis1 :: Vector) #' (axis2 :: Vector))"

VConnected_constr [rule_format] :
"ALL (frontier :: Vector => bool).
 ALL (point :: Vector).
 VConnected ((frontier :: Vector => bool), (point :: Vector)) =
 (if (frontier :: Vector => bool) (point :: Vector)
     then (frontier :: Vector => bool)
     else % (y :: Vector). X__intersection__X
                           (VLine ((point :: Vector), (y :: Vector)),
                            (frontier :: Vector => bool)) =
                           X_emptySet)"

VHalfSpace_constr [rule_format] :
"ALL (normal :: Vector).
 VHalfSpace (normal :: Vector) =
 VConnected (VPlane (normal :: Vector), (normal :: Vector))"

VHalfSpace2_constr [rule_format] :
"ALL (normal :: Vector).
 VHalfSpace2 (normal :: Vector) =
 X__union__X
 (VConnected (VPlane (normal :: Vector), (normal :: Vector)),
  VPlane (normal :: Vector))"

VBall_constr [rule_format] :
"ALL (r :: Real).
 VBall (r :: Real) =
 (% (y :: Vector). || (y :: Vector) || <=' (r :: Real))"

VCircle_constr [rule_format] :
"ALL (axis :: Vector).
 ALL (r :: Real).
 VCircle ((r :: Real), (axis :: Vector)) =
 X__intersection__X (VPlane (axis :: Vector), VBall (r :: Real))"

ActAttach_constr [rule_format] :
"ALL (point :: Point).
 ALL (vectors :: Vector => bool).
 ActAttach ((point :: Point), (vectors :: Vector => bool)) =
 X__XPlus__XX2 ((point :: Point), (vectors :: Vector => bool))"

ActExtrude_constr [rule_format] :
"ALL (axis :: Vector).
 ALL (points :: Point => bool).
 ActExtrude ((axis :: Vector), (points :: Point => bool)) =
 (% (x :: Point). EX (l :: Real).
                  EX (y :: Point).
                  ((l :: Real) isIn closedinterval (0'', gn_inj(1')) &
                   (y :: Point) isIn (points :: Point => bool)) &
                  (x :: Point) =
                  (y :: Point) +' ((l :: Real) *_3 (axis :: Vector)))"

vwl_identity [rule_format] :
"ALL (s :: Real).
 ALL (v :: Vector).
 || (v :: Vector) || = (s :: Real) -->
 VWithLength((v :: Vector), (s :: Real)) = (v :: Vector)"

vwl_length [rule_format] :
"ALL (s :: Real).
 ALL (v :: Vector).
 ~ (v :: Vector) = 0_3 -->
 || VWithLength((v :: Vector), (s :: Real)) || =
 gn_inj(abs'((s :: Real)))"

vwl_lindep [rule_format] :
"ALL (s :: Real).
 ALL (v :: Vector).
 lindep((v :: Vector), VWithLength((v :: Vector), (s :: Real)))"

semantics_for_Planes [rule_format] :
"ALL (ics :: Vector).
 ALL (X_n :: VectorStar).
 ALL (X_o :: Point).
 iX2
 (X_SWPlane (X_o :: Point) (X_n :: VectorStar) (ics :: Vector)) =
 ActAttach ((X_o :: Point), VPlane (gn_inj((X_n :: VectorStar))))"

semantics_for_SketchObject_listsXMinusBaseCase [rule_format] :
"ALL (plane :: SWPlane).
 X_isX2 (['], (plane :: SWPlane)) = X_emptySet"

semantics_for_SketchObject_listsXMinusRecursiveCase [rule_format] :
"ALL (plane :: SWPlane).
 ALL (sko :: SWSketchObject).
 ALL (skos :: SWSketchObject List).
 X_isX2
 ((sko :: SWSketchObject) ::' (skos :: SWSketchObject List),
  (plane :: SWPlane)) =
 X__union__X
 (X_isX1 ((sko :: SWSketchObject), (plane :: SWPlane)),
  X_isX2 ((skos :: SWSketchObject List), (plane :: SWPlane)))"

semantics_for_Arcs [rule_format] :
"ALL (plane :: SWPlane).
 ALL (x :: Point).
 ALL (y :: Point).
 ALL (z :: Point).
 X_isX1
 (gn_inj(X_SWArc (x :: Point) (y :: Point) (z :: Point)),
  (plane :: SWPlane)) =
 (let (r1 :: Vector) = vec((x :: Point), (y :: Point));
      (ball :: Point => bool) =
      ActAttach ((x :: Point), VBall ( || (r1 :: Vector) || ));
      (planeI :: Point => bool) = iX2 (plane :: SWPlane)
  in X__intersection__X
     ((ball :: Point => bool), (planeI :: Point => bool)))"

semantics_for_Sketches [rule_format] :
"ALL (plane :: SWPlane).
 ALL (skos :: SWSketchObject List).
 iX3 (X_SWSketch (skos :: SWSketchObject List) (plane :: SWPlane)) =
 X_isX2 ((skos :: SWSketchObject List), (plane :: SWPlane))"

semantics_for_ArcExtrusion [rule_format] :
"ALL (l :: Real).
 ALL (sk :: SWSketch).
 iX1 (gn_inj(X_SWExtrusion (sk :: SWSketch) (l :: Real))) =
 ActExtrude
 (VWithLength(gn_inj(NormalVector(Plane'((sk :: SWSketch)))),
  (l :: Real)),
  iX3 (sk :: SWSketch))"

plane_is_plane [rule_format] :
"ALL (plane :: SWPlane).
 iX2 (plane :: SWPlane) =
 PlaneX2
 (SpacePoint((plane :: SWPlane)), NormalVector((plane :: SWPlane)))"

-- "TODO: removed the partial encoding by hand!"
def_of_SWCylinder [rule_format] :
"ALL (axis :: VectorStar).
 ALL (boundarypoint :: Point).
 ALL (center :: Point).
 SWCylinder((center :: Point), (boundarypoint :: Point), (axis :: VectorStar)) =
 gn_inj(let (plane :: SWPlane) =
      X_SWPlane (center :: Point) (axis :: VectorStar)
      (V(0'', 0'', 0''));
      (arc :: SWArc) =
      X_SWArc (center :: Point) (boundarypoint :: Point)
      (boundarypoint :: Point);
      (height :: Real) = || gn_inj((axis :: VectorStar)) ||
  in X_SWExtrusion
     (X_SWSketch (gn_inj((arc :: SWArc)) ::' [']) (plane :: SWPlane))
     (height :: Real))"

affine_cylinder_constructible_in_SW [rule_format] :
"ALL (axis :: VectorStar).
 ALL (offset :: Point).
 ALL (r :: RealPos).
 Cylinder
 (((offset :: Point), (r :: RealPos)), (axis :: VectorStar)) =
 (let (boundary :: Point => bool) =
      % (p :: Point). let (v :: Vector) =
                          vec((offset :: Point), (p :: Point))
                      in orth((v :: Vector), gn_inj((axis :: VectorStar))) &
                         || (v :: Vector) || = gn_inj((r :: RealPos));
      (boundarypoint :: Point) = choose'((boundary :: Point => bool))
  in iX1
     (SWCylinder((offset :: Point), (boundarypoint :: Point),
      (axis :: VectorStar))))"

declare ga_subt_reflexive [simp]
declare ga_subt_NonZero_XLt_Real [simp]
declare ga_subt_RealNonNeg_XLt_Real [simp]
declare ga_subt_RealPos_XLt_Real [simp]
declare ga_subt_SWArc_XLt_SWSketchObject [simp]
declare ga_subt_SWExtrusion_XLt_SWFeature [simp]
declare ga_subt_SWFeature_XLt_SWObject [simp]
declare ga_subt_SWLine_XLt_SWSketchObject [simp]
declare ga_subt_SWPlane_XLt_SWObject [simp]
declare ga_subt_SWSketch_XLt_SWObject [simp]
declare ga_subt_SWSketchObject_XLt_SWObject [simp]
declare ga_subt_SWSpline_XLt_SWSketchObject [simp]
declare ga_subt_VectorStar_XLt_Vector [simp]
declare ga_subt_ZeroToNine_XLt_Real [simp]
declare ga_assoc___Xx__ [simp]
declare ga_right_unit___Xx__ [simp]
declare ga_left_unit___Xx__ [simp]
declare inv_Group [simp]
declare rinv_Group [simp]
declare ga_comm___Xx__ [simp]
declare ga_assoc___Xx___9 [simp]
declare ga_right_unit___Xx___7 [simp]
declare ga_left_unit___Xx___8 [simp]
declare left_zero [simp]
declare right_zero [simp]
declare ga_comm___Xx___14 [simp]
declare ga_assoc___Xx___22 [simp]
declare ga_right_unit___Xx___18 [simp]
declare ga_left_unit___Xx___20 [simp]
declare inv_Group_21 [simp]
declare rinv_Group_19 [simp]
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
declare RealNonNeg_type [simp]
declare RealPos_type [simp]
declare sqrt_def [simp]
declare ga_select_C1 [simp]
declare ga_select_C2 [simp]
declare ga_select_C3 [simp]
declare ga_select_C1_151 [simp]
declare ga_select_C2_152 [simp]
declare ga_select_C3_153 [simp]
declare VectorStar_type [simp]
declare ga_assoc___Xx___82 [simp]
declare ga_right_unit___Xx___76 [simp]
declare ga_left_unit___Xx___78 [simp]
declare inv_Group_79 [simp]
declare rinv_Group_77 [simp]
declare ga_comm___Xx___80 [simp]
declare unit [simp]
declare zero_by_left_zero [simp]
declare zero_by_right_zero [simp]
declare inverse_by_XMinus1 [simp]
declare lindep_reflexivity [simp]
declare lindep_symmetry [simp]
declare pos_definite_94 [simp]
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
declare ga_select_Objects_1 [simp]
declare ga_select_SkchCtrtStatus [simp]
declare ga_select_Objects_2 [simp]
declare ga_select_Sketch [simp]
declare ga_select_Depth [simp]
declare vwl_identity [simp]
declare vwl_lindep [simp]
declare semantics_for_SketchObject_listsXMinusBaseCase [simp]
declare semantics_for_Sketches [simp]




-- "SUBTYPE RULES"

axioms

-- "is used for derivation of subtypes:"
subtype_subsumption:
"[| X_gn_subt (x:: 'a) (y:: 'c); X_gn_subt (z:: 'b) (t:: 'c);
  (!!(z':: 'c). defOp(gn_proj(z'):: 'a partial) ==> defOp(gn_proj(z'):: 'b partial)) |]
  ==> (X_gn_subt (u:: 'a) (v:: 'b))"


lemma subtype_reflexive:
"X_gn_subt (x:: 'a) (y:: 'a)" by (simp only: ga_subt_reflexive)

lemma subtype_transitive:
"[| X_gn_subt (x:: 'a) (y:: 'b); X_gn_subt (z:: 'b) (t:: 'c) |]  ==> X_gn_subt (u:: 'a) (v:: 'c)"
proof-
  assume hypAB: "X_gn_subt (x:: 'a) (y:: 'b)"
  assume hypBC: "X_gn_subt (z:: 'b) (t:: 'c)"
  have A: "X_gn_subt u y" by (rule ga_subt_transitive [of u x y], simp add: ga_subt_reflexive hypAB)
  have B: "X_gn_subt y t" by (rule ga_subt_transitive [of y z t], simp add: ga_subt_reflexive hypBC)
  have C: "X_gn_subt u t" by (rule ga_subt_transitive [of u y t], simp add: A B)
  show "X_gn_subt u v" by (rule ga_subt_transitive [of u t v], simp add: ga_subt_reflexive C)
qed

-- "necessary when omitting the quantifiers in the axioms below"
lemma subtype_constant:
"X_gn_subt (x:: 'a) (y:: 'b) ==> (!!(u:: 'a) v:: 'b. X_gn_subt u v)"
proof-
  assume hyp: "X_gn_subt x y"
  fix u:: 'a
  fix v:: 'b
  show "X_gn_subt u v" by (rule subtype_transitive [of x x x y u v], simp add: ga_subt_reflexive hyp)
qed




-- "INJECTION PROJECTION RULES"

-- "is used to derive defining predicate P for a subtype A, P(gn_inj(x::A))"
lemma gn_proj_def:
"X_gn_subt (x:: 'a) (y:: 'b) ==> defOp(gn_proj(gn_inj(x):: 'b):: 'a partial)"

lemma gn_proj_inj:
"X_gn_subt (x:: 'a) (y:: 'b) ==> (!!(z:: 'a). makeTotal(gn_proj(gn_inj(z):: 'b)) = z)"

lemma gn_inj_proj:
"X_gn_subt (x:: 'a) (y:: 'b) ==> (!!(z:: 'b). defOp(gn_proj(z):: 'a partial) ==>
  gn_inj(makeTotal(gn_proj(z):: 'a partial)) = z)"

lemma gn_inj_diagram:
"[| X_gn_subt (x:: 'a) (y:: 'b); X_gn_subt (t:: 'b) (z:: 'c) |]
  ==> (!!(x':: 'a). (gn_inj(x'):: 'c) = gn_inj(gn_inj(x'):: 'b))"

--   "X_gn_subt (u:: 'a) (v:: 'b) ==> inj (gn_inj:: 'a => 'b)"

lemma gn_inj_injective :
  "X_gn_subt (u :: 'a) (v:: 'b) ==> inj (X_gn_inj :: 'a => 'b)"
  proof (rule injI)
    fix x:: 'a
    fix y:: 'a
    assume hyp1: "X_gn_subt (u:: 'a) (v:: 'b)"
      and hyp2: "(X_gn_inj x :: 'b) = X_gn_inj y"

    from hyp1 subtype_constant 
    have fact: "!!(z:: 'a). makeTotal(gn_proj(gn_inj(z):: 'b)) = z"
      by (rule_tac gn_proj_inj, blast)

    hence "x = makeTotal(gn_proj(gn_inj(x):: 'b))" ..
    also from hyp2 have "... = makeTotal(gn_proj(gn_inj(y):: 'b))" by simp
    also from fact have "... = y" by simp
    finally show "x = y" by simp
  qed

lemma gn_inj_identity :
"!!x:: 'a. (gn_inj(x):: 'a) = x"
proof-
  fix x:: 'a
  have fact: "(gn_inj(x):: 'a) = gn_inj(gn_inj(x):: 'a)"
    by (simp_all add: gn_inj_diagram subtype_reflexive)
  thus "(gn_inj(x):: 'a) = x"
    by (subst injD [of "(X_gn_inj:: 'a=>'a)" "(gn_inj(x):: 'a)" x],
      simp_all only: gn_inj_injective subtype_reflexive fact [symmetric])
qed



axioms

kga_subt_inj_proj [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'b).
 gn_subt((x :: 'a), (y :: 'b)) -->
 (y :: 'b) = gn_inj((x :: 'a)) =
 (makePartial (x :: 'a) =
  (X_gn_proj :: 'b => 'a partial) (y :: 'b))"

kga_inj_transitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'b).
 ALL (z :: 'c).
 gn_subt((x :: 'a), (y :: 'b)) & gn_subt((y :: 'b), (z :: 'c)) -->
 (z :: 'c) = gn_inj((x :: 'a)) ==
 ((y :: 'b) = gn_inj((x :: 'a)) & (z :: 'c) = gn_inj((y :: 'b)))"


-- "TODO: this should be already available by the encoding"
axioms oneone: "1'' = gn_inj(1')"

lemmas PO_simps = 
  geq_def_ExtPartialOrder
  less_def_ExtPartialOrder 
  greater_def_ExtPartialOrder


(*

 TODO: 1. auto-generated axioms need to be bound, it is bad to rely on arbitrary numbers
       Proposal: identify the theorems by operator name and keyword
                 , e.g., ("assoc", +_4)
                 , we have bad luck and point_vector_plus_associative
                 would also match, but we should probably constrain the search
                 to auto-generated names.

       2. sometimes its nice to have global equalities which should be always considered
          , e.g., 1'' = gn_inj(1') and in all reasoning steps we want to have this fact
          without mentioning it explicitly. One could have that by internally
          automatically rewrite by this global equalities.

*)

theorem def_of_Cylinder :
"ALL (axis :: VectorStar).
 ALL (offset :: Point).
 ALL (r :: RealPos).
 Cylinder
 (((offset :: Point), (r :: RealPos)), (axis :: VectorStar)) =
 (% (x :: Point). let (v :: Vector) =
                      vec((offset :: Point), (x :: Point))
                  in ( || proj((v :: Vector), gn_inj((axis :: VectorStar))) ||
                       <=' || gn_inj((axis :: VectorStar)) || &
                       || orthcomp((v :: Vector), gn_inj((axis :: VectorStar)))
                       ||
                       <=' gn_inj((r :: RealPos))) &
                     (v :: Vector) *_4 gn_inj((axis :: VectorStar)) >=' 0'')"
  -- "unfolding some initial definitions"
  unfolding affine_cylinder_constructible_in_SW
  unfolding def_of_SWCylinder

  proof (rule allI)+

    -- "I. SUBTYPE AND PARTIALITY LEMMAS"

    -- "need this to expand a term for application of lemmas"
    have partial_identity: "!!x. makeTotal(makePartial(x)) = x"
      by (simp add: makeTotal_def makePartial_def)

    -- "to infer knowledge of the form"
    -- "!!x::subtype. ?defining_predicate(gn_inj(x))"
    -- "where the ? emphasizes the fact, that we want the predicate to be expanded,"
    -- "we would need a tactic which retrieves for a given subtype the 3 rules:"
    -- "S_pred_def, Ax4(linking the defining predicate to the defOp) and subt_S_T"
    -- "As the subtype can be inferred from the context, no arguments would be"
    -- "required for this tactic"
    have RealPos_subtype: "!!x::RealPos. gn_inj(x) >' 0''"
      by (simp only: RealPos_pred_def [THEN sym], subst RealPos_type [THEN sym],
	simp only: gn_proj_def ga_subt_RealPos_XLt_Real)

    have VectorStar_subtype: "!!x::VectorStar. (~ gn_inj(x) = 0_3)"
      by (simp only: VectorStar_pred_def [THEN sym], subst VectorStar_type [THEN sym],
	simp only: gn_proj_def ga_subt_VectorStar_XLt_Vector)

    from RealPos_subtype have
      realpos_nonneg: "!!x::RealPos. 0'' <=' gn_inj(x)"
      by (simp only: PO_simps)

    from ga_subt_RealPos_XLt_Real
    have ga_subt_RealPos_XLt_RealNonNeg:
      "!!(x::RealPos) (y::RealNonNeg). X_gn_subt x y"
      by (rule_tac subtype_subsumption, blast,
	simp_all add: ga_subt_RealNonNeg_XLt_Real RealPos_pred_def RealNonNeg_pred_def PO_simps)

    from ga_subt_RealPos_XLt_RealNonNeg ga_subt_RealNonNeg_XLt_Real ga_subt_RealPos_XLt_Real
    have real_inj:
      "!!(x::RealPos). (gn_inj(x)\<Colon>Real) = gn_inj(gn_inj(x)\<Colon>RealNonNeg)"
      by (rule_tac gn_inj_diagram, simp)

    have realnonneg_identity:
      "!!x::RealNonNeg. makeTotal(gn_proj((X_gn_inj x)\<Colon>Real)) = x"
      by (simp only: gn_proj_inj ga_subt_RealNonNeg_XLt_Real)



    -- "II. GENERAL LEMMAS"

    from e1e2_nonlindep have space_at_least_2dim: "EX v w. \<not> lindep(v,w)" by blast

    have abs_on_realpos:
      "!!x::RealPos. abs'(gn_inj(x)) = X_gn_inj x"
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
	"|| VWithLength(v, X_gn_inj s) || = gn_inj(abs'(X_gn_inj s))" by blast
      also have "\<dots> = gn_inj(gn_inj(s)::RealNonNeg)" by (simp only: abs_on_realpos)
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
	by (subst restrictOp_def, subst if_P, subst NonZero_type, simp add: hyp, simp)
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
    def sketch: sketch == "X_SWSketch (gn_inj(arc) ::' XOSqBrXCSqBr) pln"

    -- "additional definitions, not stemming from let-vars"
    def I01: I01 == "closedinterval (0'', gn_inj(1'))"

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
        in iX1 (gn_inj
                (let plane = X_SWPlane offset axis (V(0'', 0'', 0''));
                     arc = X_SWArc offset boundarypoint boundarypoint;
                     height = || gn_inj(axis) ||
                 in X_SWExtrusion (X_SWSketch (gn_inj(arc) ::' [']) plane) height)))
          =
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
	  by (simp only: ga_comm___Xx___80)
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
	  have l_in_unitinterval: "0'' <=' l \<and> l <=' gn_inj(1')"
	    proof-
	      from main_knowledge I01 have "l isIn closedinterval(0'', gn_inj(1'))" by blast
	      with abbrev_of_interval have "XOSqBr__XPeriodXPeriodXPeriod__XCSqBr(0'', gn_inj(1')) l"
		by simp
	      thus ?thesis by (simp add: def_of_interval PO_simps)
	    qed

	  have subgoal1: "|| vp || <=' || axs ||"
	  proof-
	    from main_identity have "|| vp || = || l *_3 axs ||" by simp
	    also have "\<dots> = l *'' || axs ||"
	      by (simp only: PO_simps pos_homogeneous l_in_unitinterval)
	    also have "\<dots> <=' || axs ||"
	      by (subst ga_left_unit___Xx___8 [symmetric]
		, subst oneone
		, rule FWO_times_left
		, simp add: l_in_unitinterval pos_definite_94)
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

	    from pos_definite_94 have axs_norm_nonneg: "||axs|| >=' 0''"
	      by (simp only: PO_simps)

	    from v_mult_axs_simp main_knowledge l_def homogeneous
	    have "l *'' (axs *_4 axs) >=' 0''" by simp

	    with times_leq_nonneg_cond axs_sqr_nonneg PO_simps
	    have I01_first: "l >=' 0''" by blast

	    with main_knowledge l_def pos_homogeneous
	    have "l *'' || axs || <=' || axs ||"
	      -- "TODO: check whether this means only the logical rules"
	      by (simp only:)

	    with axs_norm_nonneg have I01_second: "l <=' gn_inj(1')"
	      by (subst (asm) ga_left_unit___Xx___8 [symmetric]
		, subst (asm) oneone
		, insert times_cancel_right_nonneg_leq [of l "||axs||"]
		, simp)

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
		, subst ga_comm___Xx___80
		, subst v_decomp [symmetric]
		, simp only: ga_comm___Xx___80 v vec_def)

	    with subgoal1 subgoal2 subgoal3 show ?thesis by blast
	  qed
	  thus "EX l y. ?G l y" by auto
	qed
      qed
    qed

ML "Header.record \"def_of_Cylinder\""

end
