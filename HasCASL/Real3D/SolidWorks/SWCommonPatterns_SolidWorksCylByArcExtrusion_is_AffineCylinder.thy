theory SWCommonPatterns_SolidWorksCylByArcExtrusion_is_AffineCylinder
imports "$HETS_ISABELLE_LIB/MainHC"
uses "$HETS_ISABELLE_LIB/prelude"
begin

ML "Header.initialize
    [\"ga_subt_reflexive\", \"ga_subt_transitive\",
     \"ga_subt_inj_proj\", \"ga_inj_transitive\",
     \"ga_subt_Int_XLt_Rat\", \"ga_subt_Nat_XLt_Int\",
     \"ga_subt_NonZero_XLt_Real\", \"ga_subt_Pos_XLt_Nat\",
     \"ga_subt_Rat_XLt_Real\", \"ga_subt_Real_XLt_Point\",
     \"ga_subt_Real_XLt_Vector\", \"ga_subt_RealNonNeg_XLt_Real\",
     \"ga_subt_RealPos_XLt_RealNonNeg\",
     \"ga_subt_SWArc_XLt_SWSketchObject\",
     \"ga_subt_SWExtrusion_XLt_SWFeature\",
     \"ga_subt_SWFeature_XLt_SWObject\",
     \"ga_subt_SWLine_XLt_SWSketchObject\",
     \"ga_subt_SWPlane_XLt_SWObject\",
     \"ga_subt_SWSketch_XLt_SWObject\",
     \"ga_subt_SWSketchObject_XLt_SWObject\",
     \"ga_subt_SWSpline_XLt_SWSketchObject\",
     \"ga_subt_VectorStar_XLt_Vector\", \"ga_assoc___Xx__\",
     \"ga_right_unit___Xx__\", \"ga_left_unit___Xx__\", \"inv_Group\",
     \"rinv_Group\", \"ga_comm___Xx__\", \"ga_assoc___Xx___9\",
     \"ga_right_unit___Xx___7\", \"ga_left_unit___Xx___8\",
     \"distr1_Ring\", \"distr2_Ring\", \"left_zero\", \"right_zero\",
     \"ga_comm___Xx___14\", \"noZeroDiv\", \"zeroNeqOne\",
     \"NonZero_type\", \"ga_assoc___Xx___22\",
     \"ga_right_unit___Xx___18\", \"ga_left_unit___Xx___20\",
     \"inv_Group_21\", \"rinv_Group_19\", \"binary_inverse\",
     \"binary_field_inverse\", \"refl\", \"trans\", \"antisym\",
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
     \"RealPos_pred_def\", \"RealNonNeg_type\", \"RealPos_type\",
     \"abs_def\", \"times_cancel_right_nonneg_leq\",
     \"times_leq_nonneg_cond\", \"sqr_def\", \"sqrt_def\", \"Pos_def\",
     \"ga_select_C1\", \"ga_select_C2\", \"ga_select_C3\",
     \"Zero_Point\", \"Point_choice\", \"ga_select_C1_131\",
     \"ga_select_C2_132\", \"ga_select_C3_133\", \"Zero_Vector\",
     \"VectorStar_pred_def\", \"VectorStar_type\",
     \"def_of_vector_addition\", \"def_of_minus_vector\",
     \"binary_inverse_72\", \"scalar_multiplication\",
     \"scalar_product\", \"vector_product\", \"ONB1\", \"ONB2\",
     \"ONB3\", \"cross_left_homogenity\",
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
     \"unique_orthogonal_decomposition\", \"ga_select_first\",
     \"ga_select_rest\", \"Ax4\", \"Ax5\", \"ga_assoc___Xx___83\",
     \"ga_right_unit___Xx___81\", \"ga_left_unit___Xx___82\",
     \"listop_basecase\", \"listop_reccase\",
     \"cross_product_orthogonal\", \"cross_product_zero_iff_lindep\",
     \"e1e2_nonlindep\", \"point_vector_map\", \"plus_injective\",
     \"plus_surjective\", \"point_vector_plus_associative\",
     \"vec_def\", \"transitivity_of_vec_plus\", \"plus_vec_identity\",
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
     \"plane_condition_for_point_and_vector\", \"ga_select_SpacePoint\",
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
     \"def_of_Cylinder\", \"def_of_given_arc\", \"cylinder_offset\",
     \"cylinder_radius\", \"cylinder_axis\", \"real_extrusion\",
     \"real_arc\", \"the_arc_is_wellformed\",
     \"extrusion_is_cylinder\"]"

typedecl NonZero
typedecl PointSet
typedecl Pos
typedecl Rat
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
typedecl X_Int
typedecl X_Nat

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
Pi :: "RealPos"
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
X0X1 :: "X_Int" ("0''")
X0X2 :: "X_Nat" ("0''''")
X0X3 :: "Point" ("0'_3")
X0X4 :: "Rat" ("0'_4")
X0X5 :: "Real" ("0'_5")
X0X6 :: "Vector" ("0'_6")
X1X1 :: "X_Int" ("1''")
X1X2 :: "X_Nat" ("1''''")
X1X3 :: "NonZero" ("1'_3")
X1X4 :: "Pos" ("1'_4")
X1X5 :: "Rat" ("1'_5")
X1X6 :: "Real" ("1'_6")
X2X1 :: "X_Int" ("2''")
X2X2 :: "X_Nat" ("2''''")
X2X3 :: "Rat" ("2'_3")
X3X1 :: "X_Int" ("3''")
X3X2 :: "X_Nat" ("3''''")
X3X3 :: "Rat" ("3'_3")
X4X1 :: "X_Int" ("4''")
X4X2 :: "X_Nat" ("4''''")
X4X3 :: "Rat" ("4'_3")
X5X1 :: "X_Int" ("5''")
X5X2 :: "X_Nat" ("5''''")
X5X3 :: "Rat" ("5'_3")
X6X1 :: "X_Int" ("6''")
X6X2 :: "X_Nat" ("6''''")
X6X3 :: "Rat" ("6'_3")
X7X1 :: "X_Int" ("7''")
X7X2 :: "X_Nat" ("7''''")
X7X3 :: "Rat" ("7'_3")
X8X1 :: "X_Int" ("8''")
X8X2 :: "X_Nat" ("8''''")
X8X3 :: "Rat" ("8'_3")
X9X1 :: "X_Int" ("9''")
X9X2 :: "X_Nat" ("9''''")
X9X3 :: "Rat" ("9'_3")
XLBrace__XRBrace :: "('S => bool) => 'S => bool"
XMinus__XX1 :: "X_Int => X_Int" ("(-''/ _)" [56] 56)
XMinus__XX2 :: "Rat => Rat" ("(-''''/ _)" [56] 56)
XMinus__XX3 :: "Real => Real" ("(-'_3/ _)" [56] 56)
XMinus__XX4 :: "Vector => Vector" ("(-'_4/ _)" [56] 56)
XOSqBr__XPeriodXPeriodXPeriod__XCSqBr :: "Real * Real => Real => bool"
XVBarXVBar__XVBarXVBar :: "Vector => Real" ("(||/ _/ ||)" [10] 999)
X_Center :: "SWArc => Point" ("Center/'(_')" [3] 999)
X_Depth :: "SWExtrusion => Real" ("Depth/'(_')" [3] 999)
X_End :: "SWArc => Point" ("End/'(_')" [3] 999)
X_From :: "SWLine => Point" ("From/'(_')" [3] 999)
X_InnerCS :: "SWPlane => Vector" ("InnerCS/'(_')" [3] 999)
X_NormalVector :: "SWPlane => VectorStar" ("NormalVector/'(_')" [3] 999)
X_Points :: "SWSpline => Point List" ("Points/'(_')" [3] 999)
X_Pos :: "Real => bool"
X_RealNonNeg_pred :: "Real => bool" ("RealNonNeg'_pred/'(_')" [3] 999)
X_RealPos_pred :: "Real => bool" ("RealPos'_pred/'(_')" [3] 999)
X_SkchCtrtStatus :: "SWSkchCtrts => SWSkchCtrtStatus" ("SkchCtrtStatus/'(_')" [3] 999)
X_Sketch :: "SWExtrusion => SWSketch" ("Sketch/'(_')" [3] 999)
X_SpacePoint :: "SWPlane => Point" ("SpacePoint/'(_')" [3] 999)
X_Start :: "SWArc => Point" ("Start/'(_')" [3] 999)
X_To :: "SWLine => Point" ("To/'(_')" [3] 999)
X_VWithLength :: "Vector => Real => Vector" ("VWithLength/'(_,/ _')" [3,3] 999)
X_VectorStar_pred :: "Vector => bool" ("VectorStar'_pred/'(_')" [3] 999)
X__E__X :: "Rat => X_Int => Rat" ("(_/ E/ _)" [54,54] 52)
X__XAtXAt__X :: "X_Nat => X_Nat => X_Nat" ("(_/ @@/ _)" [54,54] 52)
X__XBslashXBslash__X :: "('S => bool) * ('S => bool) => 'S => bool"
X__XCaret__XX1 :: "X_Int => X_Nat => X_Int" ("(_/ ^''/ _)" [54,54] 52)
X__XCaret__XX2 :: "X_Nat => X_Nat => X_Nat" ("(_/ ^''''/ _)" [54,54] 52)
X__XCaret__XX3 :: "Rat => X_Int => Rat partial" ("(_/ ^'_3/ _)" [54,54] 52)
X__XColonXColonXColon__X :: "X_Nat => X_Nat => Rat" ("(_/ :::/ _)" [54,54] 52)
X__XExclam :: "X_Nat => X_Nat" ("(_/ !'')" [58] 58)
X__XGtXEq__XX1 :: "X_Int => X_Int => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XGtXEq__XX2 :: "X_Nat => X_Nat => bool" ("(_/ >=''''/ _)" [44,44] 42)
X__XGtXEq__XX3 :: "Rat => Rat => bool" ("(_/ >='_3/ _)" [44,44] 42)
X__XGtXEq__XX4 :: "Real => Real => bool" ("(_/ >='_4/ _)" [44,44] 42)
X__XGt__XX1 :: "X_Int => X_Int => bool" ("(_/ >''/ _)" [44,44] 42)
X__XGt__XX2 :: "X_Nat => X_Nat => bool" ("(_/ >''''/ _)" [44,44] 42)
X__XGt__XX3 :: "Rat => Rat => bool" ("(_/ >'_3/ _)" [44,44] 42)
X__XGt__XX4 :: "Real => Real => bool" ("(_/ >'_4/ _)" [44,44] 42)
X__XHash__X :: "Vector => Vector => Vector" ("(_/ #''/ _)" [54,54] 52)
X__XLtXEq__XX1 :: "X_Int => X_Int => bool" ("(_/ <=''/ _)" [44,44] 42)
X__XLtXEq__XX2 :: "X_Nat => X_Nat => bool" ("(_/ <=''''/ _)" [44,44] 42)
X__XLtXEq__XX3 :: "Rat => Rat => bool" ("(_/ <='_3/ _)" [44,44] 42)
X__XLtXEq__XX4 :: "Real => Real => bool" ("(_/ <='_4/ _)" [44,44] 42)
X__XLt__XX1 :: "X_Int => X_Int => bool" ("(_/ <''/ _)" [44,44] 42)
X__XLt__XX2 :: "X_Nat => X_Nat => bool" ("(_/ <''''/ _)" [44,44] 42)
X__XLt__XX3 :: "Rat => Rat => bool" ("(_/ <'_3/ _)" [44,44] 42)
X__XLt__XX4 :: "Real => Real => bool" ("(_/ <'_4/ _)" [44,44] 42)
X__XMinusXExclam__X :: "X_Nat => X_Nat => X_Nat" ("(_/ -!/ _)" [54,54] 52)
X__XMinusXQuest__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ -?/ _)" [54,54] 52)
X__XMinus__XX1 :: "X_Int => X_Int => X_Int" ("(_/ -''/ _)" [54,54] 52)
X__XMinus__XX2 :: "X_Nat => X_Nat => X_Int" ("(_/ -''''/ _)" [54,54] 52)
X__XMinus__XX3 :: "Rat => Rat => Rat" ("(_/ -'_3/ _)" [54,54] 52)
X__XMinus__XX4 :: "Real => Real => Real" ("(_/ -'_4/ _)" [54,54] 52)
X__XMinus__XX5 :: "Vector => Vector => Vector" ("(_/ -'_5/ _)" [54,54] 52)
X__XPlus__XX1 :: "X_Int => X_Int => X_Int" ("(_/ +''/ _)" [54,54] 52)
X__XPlus__XX10 :: "(Point => bool) * Vector => Point => bool"
X__XPlus__XX11 :: "(Point => bool) * (Vector => bool) => Point => bool"
X__XPlus__XX2 :: "X_Nat => X_Nat => X_Nat" ("(_/ +''''/ _)" [54,54] 52)
X__XPlus__XX3 :: "X_Nat => Pos => Pos" ("(_/ +'_3/ _)" [54,54] 52)
X__XPlus__XX4 :: "Point => Vector => Point" ("(_/ +'_4/ _)" [54,54] 52)
X__XPlus__XX5 :: "Point * (Vector => bool) => Point => bool"
X__XPlus__XX6 :: "Pos => X_Nat => Pos" ("(_/ +'_6/ _)" [54,54] 52)
X__XPlus__XX7 :: "Rat => Rat => Rat" ("(_/ +'_7/ _)" [54,54] 52)
X__XPlus__XX8 :: "Real => Real => Real" ("(_/ +'_8/ _)" [54,54] 52)
X__XPlus__XX9 :: "Vector => Vector => Vector" ("(_/ +'_9/ _)" [54,54] 52)
X__XSlashXQuest__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ '/?''/ _)" [54,54] 52)
X__XSlashXQuest__XX2 :: "X_Nat => X_Nat => X_Nat partial" ("(_/ '/?''''/ _)" [54,54] 52)
X__XSlash__XX1 :: "X_Int => Pos => Rat" ("(_/ '/''/ _)" [54,54] 52)
X__XSlash__XX2 :: "Real => NonZero => Real" ("(_/ '/''''/ _)" [54,54] 52)
X__XSlash__XX3 :: "Rat => Rat => Rat partial" ("(_/ '/'_3/ _)" [54,54] 52)
X__Xx__XX1 :: "X_Int => X_Int => X_Int" ("(_/ *''/ _)" [54,54] 52)
X__Xx__XX10 :: "('S => bool) * ('T => bool) => 'S * 'T => bool"
X__Xx__XX2 :: "X_Nat => X_Nat => X_Nat" ("(_/ *''''/ _)" [54,54] 52)
X__Xx__XX3 :: "NonZero => NonZero => NonZero" ("(_/ *'_3/ _)" [54,54] 52)
X__Xx__XX4 :: "Pos => Pos => Pos" ("(_/ *'_4/ _)" [54,54] 52)
X__Xx__XX5 :: "Rat => Rat => Rat" ("(_/ *'_5/ _)" [54,54] 52)
X__Xx__XX6 :: "Real => Real => Real" ("(_/ *'_6/ _)" [54,54] 52)
X__Xx__XX7 :: "Real => Vector => Vector" ("(_/ *'_7/ _)" [54,54] 52)
X__Xx__XX8 :: "Vector => Vector => Real" ("(_/ *'_8/ _)" [54,54] 52)
X__Xx__XX9 :: "Vector => Vector => Vector" ("(_/ *'_9/ _)" [54,54] 52)
X__disjoint__X :: "('S => bool) => ('S => bool) => bool" ("(_/ disjoint/ _)" [44,44] 42)
X__div__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ div''/ _)" [54,54] 52)
X__div__XX2 :: "X_Nat => X_Nat => X_Nat partial" ("(_/ div''''/ _)" [54,54] 52)
X__dvd__X :: "X_Nat => X_Nat => bool" ("(_/ dvd''/ _)" [44,44] 42)
X__intersection__X :: "('S => bool) * ('S => bool) => 'S => bool"
X__isIn__X :: "'S => ('S => bool) => bool" ("(_/ isIn/ _)" [44,44] 42)
X__mod__XX1 :: "X_Int => X_Int => X_Nat partial" ("(_/ mod''/ _)" [54,54] 52)
X__mod__XX2 :: "X_Nat => X_Nat => X_Nat partial" ("(_/ mod''''/ _)" [54,54] 52)
X__quot__X :: "X_Int => X_Int => X_Int partial" ("(_/ quot/ _)" [54,54] 52)
X__rem__X :: "X_Int => X_Int => X_Int partial" ("(_/ rem/ _)" [54,54] 52)
X__subset__X :: "('S => bool) => ('S => bool) => bool" ("(_/ subset/ _)" [44,44] 42)
X__union__X :: "('S => bool) * ('S => bool) => 'S => bool"
X_absX1 :: "X_Int => X_Nat" ("abs''/'(_')" [3] 999)
X_absX2 :: "Rat => Rat" ("abs''''/'(_')" [3] 999)
X_absX3 :: "Real => RealNonNeg" ("abs'_3/'(_')" [3] 999)
X_allSet :: "'S => bool" ("allSet/'(_')" [3] 999)
X_choose :: "(Point => bool) => Point" ("choose''/'(_')" [3] 999)
X_emptySet :: "'S => bool" ("emptySet/'(_')" [3] 999)
X_evenX1 :: "X_Int => bool" ("even''/'(_')" [3] 999)
X_evenX2 :: "X_Nat => bool" ("even''''/'(_')" [3] 999)
X_first :: "'a List => 'a partial" ("first/'(_')" [3] 999)
X_gn_inj :: "'a => 'b" ("gn'_inj/'(_')" [3] 999)
X_gn_proj :: "'a => 'b partial" ("gn'_proj/'(_')" [3] 999)
X_gn_subt :: "'a => 'b => bool" ("gn'_subt/'(_,/ _')" [3,3] 999)
X_image :: "('S => 'T) * ('S => bool) => 'T => bool"
X_inv :: "NonZero => NonZero" ("inv''/'(_')" [3] 999)
X_isX1 :: "SWSketchObject * SWPlane => Point => bool"
X_isX2 :: "SWSketchObject List * SWPlane => Point => bool"
X_lindep :: "Vector => Vector => bool" ("lindep/'(_,/ _')" [3,3] 999)
X_map :: "('a => 'b) => 'a List => 'b List"
X_maxX1 :: "X_Int => X_Int => X_Int" ("max''/'(_,/ _')" [3,3] 999)
X_maxX2 :: "X_Nat => X_Nat => X_Nat" ("max''''/'(_,/ _')" [3,3] 999)
X_maxX3 :: "Rat => Rat => Rat" ("max'_3/'(_,/ _')" [3,3] 999)
X_maxX4 :: "Real => Real => Real" ("max'_4/'(_,/ _')" [3,3] 999)
X_minX1 :: "X_Int => X_Int => X_Int" ("min''/'(_,/ _')" [3,3] 999)
X_minX2 :: "X_Nat => X_Nat => X_Nat" ("min''''/'(_,/ _')" [3,3] 999)
X_minX3 :: "Rat => Rat => Rat" ("min'_3/'(_,/ _')" [3,3] 999)
X_minX4 :: "Real => Real => Real" ("min'_4/'(_,/ _')" [3,3] 999)
X_oddX1 :: "X_Int => bool" ("odd''/'(_')" [3] 999)
X_oddX2 :: "X_Nat => bool" ("odd''''/'(_')" [3] 999)
X_orth :: "Vector => Vector => bool" ("orth/'(_,/ _')" [3,3] 999)
X_orthcomp :: "Vector => Vector => Vector" ("orthcomp/'(_,/ _')" [3,3] 999)
X_pre :: "X_Nat => X_Nat partial" ("pre/'(_')" [3] 999)
X_proj :: "Vector => Vector => Vector" ("proj/'(_,/ _')" [3,3] 999)
X_rest :: "'a List => 'a List partial" ("rest/'(_')" [3] 999)
X_sign :: "X_Int => X_Int" ("sign/'(_')" [3] 999)
X_sqr :: "Real => RealNonNeg" ("sqr/'(_')" [3] 999)
X_sqrt :: "RealNonNeg => RealNonNeg" ("sqrt/'(_')" [3] 999)
X_sum :: "Vector List => Vector" ("sum/'(_')" [3] 999)
X_sup :: "Real => Real => Real partial" ("sup/'(_,/ _')" [3,3] 999)
X_vec :: "Point => Point => Vector" ("vec/'(_,/ _')" [3,3] 999)
arc :: "SWArc"
axis :: "VectorStar"
b1 :: "bool"
b2 :: "bool"
b3 :: "bool"
b4 :: "bool"
b5 :: "bool"
bigunion :: "(('S => bool) => bool) => 'S => bool"
boundarypoint :: "Point"
center :: "Point"
closedinterval :: "Real * Real => Real => bool"
e1 :: "Vector"
e2 :: "Vector"
e3 :: "Vector"
height :: "RealPos"
iX1 :: "SWFeature => Point => bool"
iX2 :: "SWPlane => Point => bool"
iX3 :: "SWSketch => Point => bool"
infX1 :: "Real => Real => Real partial" ("inf''/'(_,/ _')" [3,3] 999)
infX2 :: "(Real => bool) => Real partial" ("inf''''/'(_')" [3] 999)
offset :: "Point"
plane :: "SWPlane"
radius :: "RealPos"
setFromProperty :: "('S => bool) => 'S => bool"
sucX1 :: "X_Nat => X_Nat" ("suc''/'(_')" [3] 999)
sucX2 :: "X_Nat => Pos" ("suc''''/'(_')" [3] 999)
x1 :: "Real"
x2 :: "Real"
x3 :: "Real"

axioms
ga_subt_reflexive [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). gn_subt(x, y)"

ga_subt_transitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'b).
 ALL (z :: 'c). gn_subt(x, y) & gn_subt(y, z) --> gn_subt(x, z)"

ga_subt_inj_proj [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'b).
 gn_subt(x, y) -->
 y = (X_gn_inj :: 'a => 'b) x =
 (makePartial x = (X_gn_proj :: 'b => 'a partial) y)"

ga_inj_transitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'b).
 ALL (z :: 'c).
 gn_subt(x, y) & gn_subt(y, z) & y = (X_gn_inj :: 'a => 'b) x -->
 z = (X_gn_inj :: 'a => 'c) x = (z = (X_gn_inj :: 'b => 'c) y)"

ga_subt_Int_XLt_Rat [rule_format] :
"ALL (x :: X_Int). ALL (y :: Rat). gn_subt(x, y)"

ga_subt_Nat_XLt_Int [rule_format] :
"ALL (x :: X_Nat). ALL (y :: X_Int). gn_subt(x, y)"

ga_subt_NonZero_XLt_Real [rule_format] :
"ALL (x :: NonZero). ALL (y :: Real). gn_subt(x, y)"

ga_subt_Pos_XLt_Nat [rule_format] :
"ALL (x :: Pos). ALL (y :: X_Nat). gn_subt(x, y)"

ga_subt_Rat_XLt_Real [rule_format] :
"ALL (x :: Rat). ALL (y :: Real). gn_subt(x, y)"

ga_subt_Real_XLt_Point [rule_format] :
"ALL (x :: Real). ALL (y :: Point). gn_subt(x, y)"

ga_subt_Real_XLt_Vector [rule_format] :
"ALL (x :: Real). ALL (y :: Vector). gn_subt(x, y)"

ga_subt_RealNonNeg_XLt_Real [rule_format] :
"ALL (x :: RealNonNeg). ALL (y :: Real). gn_subt(x, y)"

ga_subt_RealPos_XLt_RealNonNeg [rule_format] :
"ALL (x :: RealPos). ALL (y :: RealNonNeg). gn_subt(x, y)"

ga_subt_SWArc_XLt_SWSketchObject [rule_format] :
"ALL (x :: SWArc). ALL (y :: SWSketchObject). gn_subt(x, y)"

ga_subt_SWExtrusion_XLt_SWFeature [rule_format] :
"ALL (x :: SWExtrusion). ALL (y :: SWFeature). gn_subt(x, y)"

ga_subt_SWFeature_XLt_SWObject [rule_format] :
"ALL (x :: SWFeature). ALL (y :: SWObject). gn_subt(x, y)"

ga_subt_SWLine_XLt_SWSketchObject [rule_format] :
"ALL (x :: SWLine). ALL (y :: SWSketchObject). gn_subt(x, y)"

ga_subt_SWPlane_XLt_SWObject [rule_format] :
"ALL (x :: SWPlane). ALL (y :: SWObject). gn_subt(x, y)"

ga_subt_SWSketch_XLt_SWObject [rule_format] :
"ALL (x :: SWSketch). ALL (y :: SWObject). gn_subt(x, y)"

ga_subt_SWSketchObject_XLt_SWObject [rule_format] :
"ALL (x :: SWSketchObject). ALL (y :: SWObject). gn_subt(x, y)"

ga_subt_SWSpline_XLt_SWSketchObject [rule_format] :
"ALL (x :: SWSpline). ALL (y :: SWSketchObject). gn_subt(x, y)"

ga_subt_VectorStar_XLt_Vector [rule_format] :
"ALL (x :: VectorStar). ALL (y :: Vector). gn_subt(x, y)"

ga_assoc___Xx__ [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real). (x +_8 y) +_8 z = x +_8 (y +_8 z)"

ga_right_unit___Xx__ [rule_format] :
"ALL (x :: Real). x +_8 0_5 = x"

ga_left_unit___Xx__ [rule_format] :
"ALL (x :: Real). 0_5 +_8 x = x"

inv_Group [rule_format] : "ALL (x :: Real). -_3 x +_8 x = 0_5"

rinv_Group [rule_format] : "ALL (x :: Real). x +_8 -_3 x = 0_5"

ga_comm___Xx__ [rule_format] :
"ALL (x :: Real). ALL (y :: Real). x +_8 y = y +_8 x"

ga_assoc___Xx___9 [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real). (x *_6 y) *_6 z = x *_6 (y *_6 z)"

ga_right_unit___Xx___7 [rule_format] :
"ALL (x :: Real). x *_6 1_6 = x"

ga_left_unit___Xx___8 [rule_format] :
"ALL (x :: Real). 1_6 *_6 x = x"

distr1_Ring [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real). (x +_8 y) *_6 z = (x *_6 z) +_8 (y *_6 z)"

distr2_Ring [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real). z *_6 (x +_8 y) = (z *_6 x) +_8 (z *_6 y)"

left_zero [rule_format] : "ALL (x :: Real). 0_5 *_6 x = 0_5"

right_zero [rule_format] : "ALL (x :: Real). x *_6 0_5 = 0_5"

ga_comm___Xx___14 [rule_format] :
"ALL (x :: Real). ALL (y :: Real). x *_6 y = y *_6 x"

noZeroDiv [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real). x *_6 y = 0_5 --> x = 0_5 | y = 0_5"

zeroNeqOne [rule_format] : "~ 1_6 = 0_5"

NonZero_type [rule_format] :
"ALL (x :: Real).
 defOp ((X_gn_proj :: Real => NonZero partial) x) = (~ x = 0_5)"

ga_assoc___Xx___22 [rule_format] :
"ALL (x :: NonZero).
 ALL (y :: NonZero).
 ALL (z :: NonZero). (x *_3 y) *_3 z = x *_3 (y *_3 z)"

ga_right_unit___Xx___18 [rule_format] :
"ALL (x :: NonZero). x *_3 1_3 = x"

ga_left_unit___Xx___20 [rule_format] :
"ALL (x :: NonZero). 1_3 *_3 x = x"

inv_Group_21 [rule_format] :
"ALL (x :: NonZero). inv'(x) *_3 x = 1_3"

rinv_Group_19 [rule_format] :
"ALL (x :: NonZero). x *_3 inv'(x) = 1_3"

binary_inverse [rule_format] :
"ALL (x :: Real). ALL (y :: Real). x -_4 y = x +_8 -_3 y"

binary_field_inverse [rule_format] :
"ALL (x :: Real).
 ALL (y :: NonZero).
 x /'' y = x *_6 (X_gn_inj :: NonZero => Real) (inv'(y))"

refl [rule_format] : "ALL (x :: Real). x <=_4 x"

trans [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real). ALL (z :: Real). x <=_4 y & y <=_4 z --> x <=_4 z"

antisym [rule_format] :
"ALL (x :: Real). ALL (y :: Real). x <=_4 y & y <=_4 x --> x = y"

dichotomy_TotalOrder [rule_format] :
"ALL (x :: Real). ALL (y :: Real). x <=_4 y | y <=_4 x"

FWO_plus_left [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real). a <=_4 b --> a +_8 c <=_4 b +_8 c"

FWO_times_left [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real). a <=_4 b & 0_5 <=_4 c --> a *_6 c <=_4 b *_6 c"

FWO_plus_right [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real). b <=_4 c --> a +_8 b <=_4 a +_8 c"

FWO_times_right [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real). b <=_4 c & 0_5 <=_4 a --> a *_6 b <=_4 a *_6 c"

FWO_plus [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real).
 ALL (d :: Real). a <=_4 c & b <=_4 d --> a +_8 b <=_4 c +_8 d"

inf_def [rule_format] :
"ALL (S :: Real => bool).
 ALL (m :: Real).
 inf''(S) = makePartial m =
 (ALL (m2 :: Real).
  (ALL (x :: Real). S x --> x <=_4 m2) --> m <=_4 m2)"

Real_completeness [rule_format] :
"ALL (S :: Real => bool).
 (EX (x :: Real). S x) &
 (EX (B :: Real). ALL (x :: Real). S x --> x <=_4 B) -->
 (EX (m :: Real). makePartial m = inf''(S))"

geq_def_ExtPartialOrder [rule_format] :
"ALL (x :: Real). ALL (y :: Real). (x >=_4 y) = (y <=_4 x)"

less_def_ExtPartialOrder [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real). (x <_4 y) = (x <=_4 y & ~ x = y)"

greater_def_ExtPartialOrder [rule_format] :
"ALL (x :: Real). ALL (y :: Real). (x >_4 y) = (y <_4 x)"

ga_comm_inf [rule_format] :
"ALL (x :: Real). ALL (y :: Real). inf'(x, y) = inf'(y, x)"

ga_comm_sup [rule_format] :
"ALL (x :: Real). ALL (y :: Real). sup(x, y) = sup(y, x)"

inf_def_ExtPartialOrder [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real).
 inf'(x, y) = makePartial z =
 (z <=_4 x &
  z <=_4 y & (ALL (t :: Real). t <=_4 x & t <=_4 y --> t <=_4 z))"

sup_def_ExtPartialOrder [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real).
 sup(x, y) = makePartial z =
 (x <=_4 z &
  y <=_4 z & (ALL (t :: Real). x <=_4 t & y <=_4 t --> z <=_4 t))"

ga_comm_min [rule_format] :
"ALL (x :: Real). ALL (y :: Real). min_4(x, y) = min_4(y, x)"

ga_comm_max [rule_format] :
"ALL (x :: Real). ALL (y :: Real). max_4(x, y) = max_4(y, x)"

ga_assoc_min [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real). min_4(min_4(x, y), z) = min_4(x, min_4(y, z))"

ga_assoc_max [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real). max_4(max_4(x, y), z) = max_4(x, max_4(y, z))"

ga_left_comm_min [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real). min_4(x, min_4(y, z)) = min_4(y, min_4(x, z))"

ga_left_comm_max [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real).
 ALL (z :: Real). max_4(x, max_4(y, z)) = max_4(y, max_4(x, z))"

min_def_ExtTotalOrder [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real). min_4(x, y) = (if x <=_4 y then x else y)"

max_def_ExtTotalOrder [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real). max_4(x, y) = (if x <=_4 y then y else x)"

min_inf_relation [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real). makePartial (min_4(x, y)) = inf'(x, y)"

max_sup_relation [rule_format] :
"ALL (x :: Real).
 ALL (y :: Real). makePartial (max_4(x, y)) = sup(x, y)"

RealNonNeg_pred_def [rule_format] :
"ALL (x :: Real). RealNonNeg_pred(x) = (x >=_4 0_5)"

RealPos_pred_def [rule_format] :
"ALL (x :: Real). RealPos_pred(x) = (x >_4 0_5)"

RealNonNeg_type [rule_format] :
"ALL (x :: Real).
 defOp ((X_gn_proj :: Real => RealNonNeg partial) x) =
 RealNonNeg_pred(x)"

RealPos_type [rule_format] :
"ALL (x :: Real).
 defOp ((X_gn_proj :: Real => RealPos partial) x) = RealPos_pred(x)"

abs_def [rule_format] :
"ALL (x :: Real).
 makePartial (abs_3(x)) =
 (if 0_5 <=_4 x then (X_gn_proj :: Real => RealNonNeg partial) x
     else (X_gn_proj :: Real => RealNonNeg partial) (-_3 x))"

times_cancel_right_nonneg_leq [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 ALL (c :: Real). a *_6 b <=_4 c *_6 b & b >=_4 0_5 --> a <=_4 c"

times_leq_nonneg_cond [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real). 0_5 <=_4 a *_6 b & b >=_4 0_5 --> 0_5 <=_4 a"

sqr_def [rule_format] :
"ALL (r :: Real).
 (X_gn_inj :: RealNonNeg => Real) (sqr(r)) = r *_6 r"

sqrt_def [rule_format] :
"ALL (q :: RealNonNeg).
 sqr((X_gn_inj :: RealNonNeg => Real) (sqrt(q))) = q"

Pos_def [rule_format] : "ALL (x :: Real). X_Pos x = (0_5 <=_4 x)"

ga_select_C1 [rule_format] :
"ALL (x_1 :: Real).
 ALL (x_2 :: Real). ALL (x_3 :: Real). C1'(P(x_1, x_2, x_3)) = x_1"

ga_select_C2 [rule_format] :
"ALL (x_1 :: Real).
 ALL (x_2 :: Real). ALL (x_3 :: Real). C2'(P(x_1, x_2, x_3)) = x_2"

ga_select_C3 [rule_format] :
"ALL (x_1 :: Real).
 ALL (x_2 :: Real). ALL (x_3 :: Real). C3'(P(x_1, x_2, x_3)) = x_3"

Zero_Point [rule_format] :
"0_3 =
 P((X_gn_inj :: X_Nat => Real) 0'', (X_gn_inj :: X_Nat => Real) 0'',
 (X_gn_inj :: X_Nat => Real) 0'')"

Point_choice [rule_format] :
"ALL (X_P :: Point => bool).
 (EX (y :: Point). X_P y) --> X_P (choose'(X_P))"

ga_select_C1_131 [rule_format] :
"ALL (x_1 :: Real).
 ALL (x_2 :: Real). ALL (x_3 :: Real). C1''(V(x_1, x_2, x_3)) = x_1"

ga_select_C2_132 [rule_format] :
"ALL (x_1 :: Real).
 ALL (x_2 :: Real). ALL (x_3 :: Real). C2''(V(x_1, x_2, x_3)) = x_2"

ga_select_C3_133 [rule_format] :
"ALL (x_1 :: Real).
 ALL (x_2 :: Real). ALL (x_3 :: Real). C3''(V(x_1, x_2, x_3)) = x_3"

Zero_Vector [rule_format] :
"0_6 =
 V((X_gn_inj :: X_Nat => Real) 0'', (X_gn_inj :: X_Nat => Real) 0'',
 (X_gn_inj :: X_Nat => Real) 0'')"

VectorStar_pred_def [rule_format] :
"ALL (x :: Vector).
 VectorStar_pred(x) = (~ x = (X_gn_inj :: X_Nat => Vector) 0'')"

VectorStar_type [rule_format] :
"ALL (x :: Vector).
 defOp ((X_gn_proj :: Vector => VectorStar partial) x) =
 VectorStar_pred(x)"

def_of_vector_addition [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 x +_9 y =
 V(C1''(x) +_8 C1''(y), C2''(x) +_8 C2''(y), C3''(x) +_8 C3''(y))"

def_of_minus_vector [rule_format] :
"ALL (x :: Vector).
 -_4 x = V(-_3 C1''(x), -_3 C2''(x), -_3 C3''(x))"

binary_inverse_72 [rule_format] :
"ALL (x :: Vector). ALL (y :: Vector). x -_5 y = x +_9 -_4 y"

scalar_multiplication [rule_format] :
"ALL (x :: Real).
 ALL (y :: Vector).
 x *_7 y = V(x *_6 C1''(y), x *_6 C2''(y), x *_6 C3''(y))"

scalar_product [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 x *_8 y =
 ((C1''(x) *_6 C1''(y)) +_8 (C2''(x) *_6 C2''(y))) +_8
 (C3''(x) *_6 C3''(y))"

vector_product [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 x #' y =
 V(((X_gn_inj :: Real => Vector) (C2''(x)) *_8
    (X_gn_inj :: Real => Vector) (C3''(y)))
   -_4
   ((X_gn_inj :: Real => Vector) (C2''(y)) *_8
    (X_gn_inj :: Real => Vector) (C3''(x))),
 ((X_gn_inj :: Real => Vector) (C3''(x)) *_8
  (X_gn_inj :: Real => Vector) (C1''(y)))
 -_4
 ((X_gn_inj :: Real => Vector) (C3''(y)) *_8
  (X_gn_inj :: Real => Vector) (C1''(x))),
 ((X_gn_inj :: Real => Vector) (C1''(x)) *_8
  (X_gn_inj :: Real => Vector) (C2''(y)))
 -_4
 ((X_gn_inj :: Real => Vector) (C1''(y)) *_8
  (X_gn_inj :: Real => Vector) (C2''(x))))"

ONB1 [rule_format] :
"e1 =
 V((X_gn_inj :: NonZero => Real) 1_3,
 (X_gn_inj :: X_Nat => Real) 0'', (X_gn_inj :: X_Nat => Real) 0'')"

ONB2 [rule_format] :
"e2 =
 V((X_gn_inj :: X_Nat => Real) 0'',
 (X_gn_inj :: NonZero => Real) 1_3,
 (X_gn_inj :: X_Nat => Real) 0'')"

ONB3 [rule_format] :
"e3 =
 V((X_gn_inj :: X_Nat => Real) 0'', (X_gn_inj :: X_Nat => Real) 0'',
 (X_gn_inj :: NonZero => Real) 1_3)"

cross_left_homogenity [rule_format] :
"ALL (r :: Real).
 ALL (x :: Vector).
 ALL (y :: Vector).
 (X_gn_inj :: Real => Vector)
 ((X_gn_inj :: Real => Vector) r *_8 (x #' y)) =
 (X_gn_inj :: Real => Vector) ((X_gn_inj :: Real => Vector) r *_8 x)
 #' y"

cross_product_antisymmetric [rule_format] :
"ALL (x :: Vector). ALL (y :: Vector). x #' y = -_4 (y #' x)"

ga_assoc___Xx___82 [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 ALL (z :: Vector). (x +_9 y) +_9 z = x +_9 (y +_9 z)"

ga_right_unit___Xx___76 [rule_format] :
"ALL (x :: Vector). x +_9 0_6 = x"

ga_left_unit___Xx___78 [rule_format] :
"ALL (x :: Vector). 0_6 +_9 x = x"

inv_Group_79 [rule_format] : "ALL (x :: Vector). -_4 x +_9 x = 0_6"

rinv_Group_77 [rule_format] :
"ALL (x :: Vector). x +_9 -_4 x = 0_6"

ga_comm___Xx___80 [rule_format] :
"ALL (x :: Vector). ALL (y :: Vector). x +_9 y = y +_9 x"

unit [rule_format] :
"ALL (x :: Vector). (X_gn_inj :: NonZero => Real) 1_3 *_7 x = x"

mix_assoc [rule_format] :
"ALL (r :: Real).
 ALL (s :: Real).
 ALL (x :: Vector). (r *_6 s) *_7 x = r *_7 (s *_7 x)"

distr_Field [rule_format] :
"ALL (r :: Real).
 ALL (s :: Real).
 ALL (x :: Vector). (r +_8 s) *_7 x = (r *_7 x) +_9 (s *_7 x)"

distr_Space [rule_format] :
"ALL (r :: Real).
 ALL (x :: Vector).
 ALL (y :: Vector). r *_7 (x +_9 y) = (r *_7 x) +_9 (r *_7 y)"

zero_by_left_zero [rule_format] :
"ALL (x :: Vector). 0_5 *_7 x = 0_6"

zero_by_right_zero [rule_format] :
"ALL (r :: Real). r *_7 0_6 = 0_6"

inverse_by_XMinus1 [rule_format] :
"ALL (x :: Vector).
 -_3 (X_gn_inj :: NonZero => Real) 1_3 *_7 x = -_4 x"

no_zero_divisor [rule_format] :
"ALL (r :: Real).
 ALL (x :: Vector). ~ r = 0_5 & ~ x = 0_6 --> ~ r *_7 x = 0_6"

distributive [rule_format] :
"ALL (v :: Vector).
 ALL (v' :: Vector).
 ALL (w :: Vector). (v +_9 v') *_8 w = (v *_8 w) +_8 (v' *_8 w)"

homogeneous [rule_format] :
"ALL (a :: Real).
 ALL (v :: Vector).
 ALL (w :: Vector). (a *_7 v) *_8 w = a *_6 (v *_8 w)"

symmetric [rule_format] :
"ALL (v :: Vector). ALL (w :: Vector). v *_8 w = w *_8 v"

pos_definite [rule_format] :
"ALL (v :: Vector). ~ v = 0_6 --> v *_8 v >_4 0_5"

right_distributive [rule_format] :
"ALL (v :: Vector).
 ALL (v' :: Vector).
 ALL (w :: Vector). w *_8 (v +_9 v') = (w *_8 v) +_8 (w *_8 v')"

right_homogeneous [rule_format] :
"ALL (a :: Real).
 ALL (v :: Vector).
 ALL (w :: Vector). v *_8 (a *_7 w) = a *_6 (v *_8 w)"

non_degenerate [rule_format] :
"ALL (v :: Vector). v *_8 v = 0_5 --> v = 0_6"

lindep_def [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 lindep(x, y) = (y = 0_6 | (EX (r :: Real). x = r *_7 y))"

lindep_reflexivity [rule_format] :
"ALL (x :: Vector). lindep(x, x)"

lindep_symmetry [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector). lindep(x, y) --> lindep(y, x)"

simple_lindep_condition [rule_format] :
"ALL (r :: Real).
 ALL (x :: Vector). ALL (y :: Vector). x = r *_7 y --> lindep(x, y)"

lindep_nonlindep_transitivity [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 ALL (z :: Vector).
 (~ x = 0_6 & lindep(x, y)) & ~ lindep(y, z) --> ~ lindep(x, z)"

norm_from_inner_prod_def [rule_format] :
"ALL (x :: Vector).
 makePartial ( || x || ) =
 restrictOp
 (makePartial
  ((X_gn_inj :: RealNonNeg => Real)
   (sqrt(makeTotal
         ((X_gn_proj :: Real => RealNonNeg partial) (x *_8 x))))))
 (defOp ((X_gn_proj :: Real => RealNonNeg partial) (x *_8 x)))"

proj_def [rule_format] :
"ALL (v :: Vector).
 ALL (w :: Vector).
 makePartial (proj(v, w)) =
 (if w = 0_6 then makePartial 0_6
     else restrictOp
          (makePartial
           (((v *_8 w) /''
             makeTotal ((X_gn_proj :: Real => NonZero partial) (w *_8 w)))
            *_7 w))
          (defOp ((X_gn_proj :: Real => NonZero partial) (w *_8 w))))"

orthcomp_def [rule_format] :
"ALL (v :: Vector).
 ALL (w :: Vector). orthcomp(v, w) = v -_5 proj(v, w)"

orthogonal_def [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector). orth(x, y) = (x *_8 y = 0_5)"

homogeneous_93 [rule_format] :
"ALL (r :: Real).
 ALL (v :: Vector).
 || r *_7 v || =
 (X_gn_inj :: RealNonNeg => Real) (abs_3(r)) *_6 || v ||"

definite [rule_format] :
"ALL (v :: Vector). || v || = 0_5 = (v = 0_6)"

pos_definite_94 [rule_format] :
"ALL (v :: Vector). 0_5 <=_4 || v ||"

pos_homogeneous [rule_format] :
"ALL (r :: Real).
 ALL (v :: Vector). r >=_4 0_5 --> || r *_7 v || = r *_6 || v ||"

orth_symmetric [rule_format] :
"ALL (x :: Vector). ALL (y :: Vector). orth(x, y) --> orth(y, x)"

lindep_orth_transitive [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 ALL (z :: Vector). lindep(x, y) & orth(y, z) --> orth(x, z)"

orthogonal_existence_theorem [rule_format] :
"ALL (x :: Vector).
 (EX (a :: Vector). EX (b :: Vector). ~ lindep(a, b)) -->
 (EX (c :: Vector). ~ c = 0_6 & orth(c, x))"

orthogonal_on_zero_projection [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector). proj(x, y) = 0_6 --> orth(x, y)"

orthogonal_projection_theorem [rule_format] :
"ALL (x :: Vector). ALL (y :: Vector). orth(orthcomp(x, y), y)"

orthogonal_decomposition_theorem [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector). proj(x, y) +_9 orthcomp(x, y) = x"

unique_orthogonal_decomposition [rule_format] :
"ALL (v :: Vector).
 ALL (w :: Vector).
 ALL (x :: Vector).
 ALL (y :: Vector).
 ALL (z :: Vector).
 ((((~ z = 0_6 & x +_9 y = v +_9 w) & lindep(x, z)) &
   lindep(v, z)) &
  orth(z, y)) &
 orth(z, w) -->
 x = v & y = w"

ga_select_first [rule_format] :
"ALL (x_1 :: 'a).
 ALL (x_2 :: 'a List). first(x_1 ::' x_2) = makePartial x_1"

ga_select_rest [rule_format] :
"ALL (x_1 :: 'a).
 ALL (x_2 :: 'a List). rest(x_1 ::' x_2) = makePartial x_2"

Ax4 [rule_format] : "ALL (f :: 'a => 'b). X_map f ['] = [']"

Ax5 [rule_format] :
"ALL (f :: 'a => 'b).
 ALL (l :: 'a List).
 ALL (x :: 'a). X_map f (x ::' l) = f x ::' X_map f l"

ga_assoc___Xx___83 [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 ALL (z :: Vector). (x *_9 y) *_9 z = x *_9 (y *_9 z)"

ga_right_unit___Xx___81 [rule_format] :
"ALL (x :: Vector). x *_9 0_6 = x"

ga_left_unit___Xx___82 [rule_format] :
"ALL (x :: Vector). 0_6 *_9 x = x"

listop_basecase [rule_format] : "sum([']) = 0_6"

listop_reccase [rule_format] :
"ALL (l :: Vector List).
 ALL (x :: Vector). sum(x ::' l) = x *_9 sum(l)"

cross_product_orthogonal [rule_format] :
"ALL (x :: Vector). ALL (y :: Vector). orth(x, x #' y)"

cross_product_zero_iff_lindep [rule_format] :
"ALL (x :: Vector).
 ALL (y :: Vector).
 lindep(x, y) = (x #' y = (X_gn_inj :: X_Nat => Vector) 0'')"

e1e2_nonlindep [rule_format] : "~ lindep(e1, e2)"

point_vector_map [rule_format] :
"ALL (p :: Point).
 ALL (v :: Vector).
 p +_4 v =
 P(C1'(p) +_8 C1''(v), C2'(p) +_8 C2''(v), C3'(p) +_8 C3''(v))"

plus_injective [rule_format] :
"ALL (p :: Point).
 ALL (v :: Vector). ALL (w :: Vector). p +_4 v = p +_4 w --> v = w"

plus_surjective [rule_format] :
"ALL (p :: Point). ALL (q :: Point). EX (y :: Vector). p +_4 y = q"

point_vector_plus_associative [rule_format] :
"ALL (p :: Point).
 ALL (v :: Vector).
 ALL (w :: Vector). p +_4 (v +_9 w) = (p +_4 v) +_4 w"

vec_def [rule_format] :
"ALL (p :: Point). ALL (q :: Point). p +_4 vec(p, q) = q"

transitivity_of_vec_plus [rule_format] :
"ALL (p :: Point).
 ALL (q :: Point).
 ALL (r :: Point). vec(p, q) +_9 vec(q, r) = vec(p, r)"

plus_vec_identity [rule_format] :
"ALL (p :: Point).
 ALL (q :: Point). ALL (v :: Vector). p +_4 v = q --> v = vec(p, q)"

set_comprehension [rule_format] :
"ALL (s :: 'S => bool). XLBrace__XRBrace s = s"

abbrev_of_set_comprehension [rule_format] :
"setFromProperty = XLBrace__XRBrace"

function_image [rule_format] :
"ALL (XX :: 'S => bool).
 ALL (f :: 'S => 'T).
 X_image (f, XX) = (% x. EX (y :: 'S). y isIn XX & f y = x)"

emptySet_empty [rule_format] : "ALL (x :: 'S). ~ x isIn X_emptySet"

allSet_contains_all [rule_format] :
"ALL (x :: 'S). x isIn X_allSet"

def_of_isIn [rule_format] :
"ALL (s :: 'S => bool). ALL (x :: 'S). (x isIn s) = s x"

def_of_subset [rule_format] :
"ALL (s :: 'S => bool).
 ALL (s' :: 'S => bool).
 (s subset s') = (ALL (x :: 'S). x isIn s --> x isIn s')"

def_of_union [rule_format] :
"ALL (s :: 'S => bool).
 ALL (s' :: 'S => bool).
 ALL (x :: 'S).
 (x isIn X__union__X (s, s')) = (x isIn s | x isIn s')"

def_of_bigunion [rule_format] :
"ALL (XXXX :: ('S => bool) => bool).
 ALL (x :: 'S).
 (x isIn bigunion XXXX) =
 (EX (XX :: 'S => bool). XX isIn XXXX & x isIn XX)"

def_of_intersection [rule_format] :
"ALL (s :: 'S => bool).
 ALL (s' :: 'S => bool).
 ALL (x :: 'S).
 (x isIn X__intersection__X (s, s')) = (x isIn s & x isIn s')"

def_of_difference [rule_format] :
"ALL (s :: 'S => bool).
 ALL (s' :: 'S => bool).
 ALL (x :: 'S).
 (x isIn X__XBslashXBslash__X (s, s')) = (x isIn s & ~ x isIn s')"

def_of_disjoint [rule_format] :
"ALL (s :: 'S => bool).
 ALL (s' :: 'S => bool).
 (s disjoint s') = (X__intersection__X (s, s') = X_emptySet)"

def_of_productset [rule_format] :
"ALL (s :: 'S => bool).
 ALL (t :: 'T => bool).
 ALL (x :: 'S).
 ALL (y :: 'T).
 ((x, y) isIn X__Xx__XX10 (s, t)) = (x isIn s & y isIn t)"

emptySet_union_right_unit [rule_format] :
"ALL (a :: 'S => bool). X__union__X (a, X_emptySet) = a"

function_image_structure [rule_format] :
"ALL (a :: 'S => bool).
 ALL (f :: 'S => 'T).
 ALL (x :: 'T).
 (x isIn X_image (f, a)) = (EX (y :: 'S). y isIn a & f y = x)"

def_of_interval [rule_format] :
"ALL (a :: Real).
 ALL (b :: Real).
 XOSqBr__XPeriodXPeriodXPeriod__XCSqBr (a, b) =
 (% r. r >=_4 a & r <=_4 b)"

abbrev_of_interval [rule_format] :
"closedinterval = XOSqBr__XPeriodXPeriodXPeriod__XCSqBr"

plus_PointSet_Vector [rule_format] :
"ALL (X_P :: Point => bool).
 ALL (v :: Vector).
 X__XPlus__XX10 (X_P, v) = X_image (% x. x +_4 v, X_P)"

plus_Point_VectorSet [rule_format] :
"ALL (X_V :: Vector => bool).
 ALL (p :: Point).
 X__XPlus__XX5 (p, X_V) = X_image (% x. p +_4 x, X_V)"

plus_PointSet_VectorSet [rule_format] :
"ALL (X_P :: Point => bool).
 ALL (X_V :: Vector => bool).
 X__XPlus__XX11 (X_P, X_V) =
 bigunion (X_image (% x. X__XPlus__XX10 (X_P, x), X_V))"

def_of_Plane [rule_format] :
"ALL (normal :: VectorStar).
 ALL (X_offset :: Point).
 PlaneX2 (X_offset, normal) =
 (% x. orth(vec(x, X_offset),
       (X_gn_inj :: VectorStar => Vector) normal))"

plane_condition_for_2_points [rule_format] :
"ALL (normal :: VectorStar).
 ALL (X_offset :: Point).
 ALL (x :: Point).
 ALL (y :: Point).
 let X_plane = PlaneX2 (X_offset, normal)
 in x isIn X_plane & y isIn X_plane -->
    orth(vec(x, y), (X_gn_inj :: VectorStar => Vector) normal)"

plane_condition_for_point_and_vector [rule_format] :
"ALL (normal :: VectorStar).
 ALL (X_offset :: Point).
 ALL (v :: Vector).
 ALL (x :: Point).
 let X_plane = PlaneX2 (X_offset, normal)
 in x isIn X_plane &
    orth(v, (X_gn_inj :: VectorStar => Vector) normal) -->
    x +_4 v isIn X_plane"

ga_select_SpacePoint [rule_format] :
"ALL (x_1 :: Point).
 ALL (x_2 :: VectorStar).
 ALL (x_3 :: Vector). SpacePoint(X_SWPlane x_1 x_2 x_3) = x_1"

ga_select_NormalVector [rule_format] :
"ALL (x_1 :: Point).
 ALL (x_2 :: VectorStar).
 ALL (x_3 :: Vector). NormalVector(X_SWPlane x_1 x_2 x_3) = x_2"

ga_select_InnerCS [rule_format] :
"ALL (x_1 :: Point).
 ALL (x_2 :: VectorStar).
 ALL (x_3 :: Vector). InnerCS(X_SWPlane x_1 x_2 x_3) = x_3"

ga_select_Center [rule_format] :
"ALL (x_1 :: Point).
 ALL (x_2 :: Point).
 ALL (x_3 :: Point). Center(X_SWArc x_1 x_2 x_3) = x_1"

ga_select_Start [rule_format] :
"ALL (x_1 :: Point).
 ALL (x_2 :: Point).
 ALL (x_3 :: Point). Start(X_SWArc x_1 x_2 x_3) = x_2"

ga_select_End [rule_format] :
"ALL (x_1 :: Point).
 ALL (x_2 :: Point).
 ALL (x_3 :: Point). End(X_SWArc x_1 x_2 x_3) = x_3"

ga_select_From [rule_format] :
"ALL (x_1 :: Point).
 ALL (x_2 :: Point). From(X_SWLine x_1 x_2) = x_1"

ga_select_To [rule_format] :
"ALL (x_1 :: Point).
 ALL (x_2 :: Point). To(X_SWLine x_1 x_2) = x_2"

ga_select_Points [rule_format] :
"ALL (x_1 :: Point List). Points(X_SWSpline x_1) = x_1"

ga_select_Objects [rule_format] :
"ALL (x_1 :: SWSketchObject List).
 ALL (x_2 :: SWPlane). Objects_3(X_SWSketch x_1 x_2) = x_1"

ga_select_Plane [rule_format] :
"ALL (x_1 :: SWSketchObject List).
 ALL (x_2 :: SWPlane). Plane'(X_SWSketch x_1 x_2) = x_2"

ga_select_Objects_1 [rule_format] :
"ALL (x_1 :: SWSkchCtrtParam List).
 Objects'(X_SWSkchCtrtObject x_1) = x_1"

ga_select_SkchCtrtStatus [rule_format] :
"ALL (x_1 :: SWSkchCtrtStatus).
 ALL (x_2 :: SWSkchCtrtObject List).
 SkchCtrtStatus(X_SWSkchCtrts x_1 x_2) = x_1"

ga_select_Objects_2 [rule_format] :
"ALL (x_1 :: SWSkchCtrtStatus).
 ALL (x_2 :: SWSkchCtrtObject List).
 Objects''(X_SWSkchCtrts x_1 x_2) = x_2"

ga_select_Sketch [rule_format] :
"ALL (x_1 :: SWSketch).
 ALL (x_2 :: Real). Sketch(X_SWExtrusion x_1 x_2) = x_1"

ga_select_Depth [rule_format] :
"ALL (x_1 :: SWSketch).
 ALL (x_2 :: Real). Depth(X_SWExtrusion x_1 x_2) = x_2"

E1_def [rule_format] :
"makePartial E1 =
 restrictOp
 (makePartial
  (X_SWPlane
   (P((X_gn_inj :: X_Nat => Real) 0'',
    (X_gn_inj :: X_Nat => Real) 0'', (X_gn_inj :: X_Nat => Real) 0''))
   (makeTotal
    ((X_gn_proj :: Vector => VectorStar partial)
     (V((X_gn_inj :: X_Nat => Real) 0'',
      (X_gn_inj :: X_Nat => Real) 0'',
      (X_gn_inj :: NonZero => Real) 1_3))))
   (V((X_gn_inj :: NonZero => Real) 1_3,
    (X_gn_inj :: X_Nat => Real) 0'',
    (X_gn_inj :: X_Nat => Real) 0''))))
 (defOp
  ((X_gn_proj :: Vector => VectorStar partial)
   (V((X_gn_inj :: X_Nat => Real) 0'',
    (X_gn_inj :: X_Nat => Real) 0'',
    (X_gn_inj :: NonZero => Real) 1_3))))"

E2_def [rule_format] :
"makePartial E2 =
 restrictOp
 (makePartial
  (X_SWPlane
   (P((X_gn_inj :: X_Nat => Real) 0'',
    (X_gn_inj :: X_Nat => Real) 0'', (X_gn_inj :: X_Nat => Real) 0''))
   (makeTotal
    ((X_gn_proj :: Vector => VectorStar partial)
     (V((X_gn_inj :: X_Nat => Real) 0'',
      (X_gn_inj :: NonZero => Real) 1_3,
      (X_gn_inj :: X_Nat => Real) 0''))))
   (V((X_gn_inj :: NonZero => Real) 1_3,
    (X_gn_inj :: X_Nat => Real) 0'',
    (X_gn_inj :: X_Nat => Real) 0''))))
 (defOp
  ((X_gn_proj :: Vector => VectorStar partial)
   (V((X_gn_inj :: X_Nat => Real) 0'',
    (X_gn_inj :: NonZero => Real) 1_3,
    (X_gn_inj :: X_Nat => Real) 0''))))"

E3_def [rule_format] :
"makePartial E3 =
 restrictOp
 (makePartial
  (X_SWPlane
   (P((X_gn_inj :: X_Nat => Real) 0'',
    (X_gn_inj :: X_Nat => Real) 0'', (X_gn_inj :: X_Nat => Real) 0''))
   (makeTotal
    ((X_gn_proj :: Vector => VectorStar partial)
     (V((X_gn_inj :: NonZero => Real) 1_3,
      (X_gn_inj :: X_Nat => Real) 0'',
      (X_gn_inj :: X_Nat => Real) 0''))))
   (V((X_gn_inj :: X_Nat => Real) 0'',
    (X_gn_inj :: NonZero => Real) 1_3,
    (X_gn_inj :: X_Nat => Real) 0''))))
 (defOp
  ((X_gn_proj :: Vector => VectorStar partial)
   (V((X_gn_inj :: NonZero => Real) 1_3,
    (X_gn_inj :: X_Nat => Real) 0'',
    (X_gn_inj :: X_Nat => Real) 0''))))"

VLine_constr [rule_format] :
"ALL (p1 :: Vector).
 ALL (p2 :: Vector).
 VLine (p1, p2) =
 X_image
 (% y. p1 +_9
       (X_gn_inj :: Real => Vector)
       ((X_gn_inj :: Real => Vector) y *_8 (p2 -_5 p1)),
  closedinterval
  ((X_gn_inj :: X_Nat => Real) 0'',
   (X_gn_inj :: NonZero => Real) 1_3))"

VWithLength_constr [rule_format] :
"ALL (s :: Real).
 ALL (v :: Vector).
 makePartial (VWithLength(v, s)) =
 (if v = (X_gn_inj :: X_Nat => Vector) 0'' then makePartial v
     else restrictOp
          (makePartial
           ((X_gn_inj :: Real => Vector)
            ((X_gn_inj :: Real => Vector)
             (s /''
              makeTotal ((X_gn_proj :: Real => NonZero partial) ( || v || )))
             *_8 v)))
          (defOp ((X_gn_proj :: Real => NonZero partial) ( || v || ))))"

VPlane_constr [rule_format] :
"ALL (normal :: Vector). VPlane normal = (% y. orth(y, normal))"

VPlane2_constr [rule_format] :
"ALL (axis1 :: Vector).
 ALL (axis2 :: Vector).
 VPlane2 (axis1, axis2) = VPlane (axis1 #' axis2)"

VConnected_constr [rule_format] :
"ALL (frontier :: Vector => bool).
 ALL (point :: Vector).
 VConnected (frontier, point) =
 (if frontier point then frontier
     else % y. X__intersection__X (VLine (point, y), frontier) =
               X_emptySet)"

VHalfSpace_constr [rule_format] :
"ALL (normal :: Vector).
 VHalfSpace normal = VConnected (VPlane normal, normal)"

VHalfSpace2_constr [rule_format] :
"ALL (normal :: Vector).
 VHalfSpace2 normal =
 X__union__X (VConnected (VPlane normal, normal), VPlane normal)"

VBall_constr [rule_format] :
"ALL (r :: Real). VBall r = (% y. || y || <=_4 r)"

VCircle_constr [rule_format] :
"ALL (X_axis :: Vector).
 ALL (r :: Real).
 VCircle (r, X_axis) = X__intersection__X (VPlane X_axis, VBall r)"

ActAttach_constr [rule_format] :
"ALL (point :: Point).
 ALL (vectors :: Vector => bool).
 ActAttach (point, vectors) = X__XPlus__XX5 (point, vectors)"

ActExtrude_constr [rule_format] :
"ALL (X_axis :: Vector).
 ALL (points :: Point => bool).
 ActExtrude (X_axis, points) =
 (% x. EX (l :: Real).
       EX (y :: Point).
       (l isIn
        closedinterval
        ((X_gn_inj :: X_Nat => Real) 0'',
         (X_gn_inj :: NonZero => Real) 1_3) &
        y isIn points) &
       x =
       y +_4
       (X_gn_inj :: Real => Vector)
       ((X_gn_inj :: Real => Vector) l *_8 X_axis))"

vwl_identity [rule_format] :
"ALL (s :: Real).
 ALL (v :: Vector). || v || = s --> VWithLength(v, s) = v"

vwl_length [rule_format] :
"ALL (s :: Real).
 ALL (v :: Vector).
 ~ v = (X_gn_inj :: X_Nat => Vector) 0'' -->
 || VWithLength(v, s) || =
 (X_gn_inj :: RealNonNeg => Real) (abs_3(s))"

vwl_lindep [rule_format] :
"ALL (s :: Real). ALL (v :: Vector). lindep(v, VWithLength(v, s))"

semantics_for_Planes [rule_format] :
"ALL (ics :: Vector).
 ALL (X_n :: VectorStar).
 ALL (X_o :: Point).
 iX2 (X_SWPlane X_o X_n ics) =
 ActAttach (X_o, VPlane ((X_gn_inj :: VectorStar => Vector) X_n))"

semantics_for_SketchObject_listsXMinusBaseCase [rule_format] :
"ALL (X_plane :: SWPlane). X_isX2 (['], X_plane) = X_emptySet"

semantics_for_SketchObject_listsXMinusRecursiveCase [rule_format] :
"ALL (X_plane :: SWPlane).
 ALL (sko :: SWSketchObject).
 ALL (skos :: SWSketchObject List).
 X_isX2 (sko ::' skos, X_plane) =
 X__union__X (X_isX1 (sko, X_plane), X_isX2 (skos, X_plane))"

semantics_for_Arcs [rule_format] :
"ALL (X_plane :: SWPlane).
 ALL (x :: Point).
 ALL (y :: Point).
 ALL (z :: Point).
 X_isX1
 ((X_gn_inj :: SWArc => SWSketchObject) (X_SWArc x y z), X_plane) =
 (let r1 = vec(x, y);
      ball = ActAttach (x, VBall ( || r1 || ));
      planeI = iX2 X_plane
  in X__intersection__X (ball, planeI))"

semantics_for_Sketches [rule_format] :
"ALL (X_plane :: SWPlane).
 ALL (skos :: SWSketchObject List).
 iX3 (X_SWSketch skos X_plane) = X_isX2 (skos, X_plane)"

semantics_for_ArcExtrusion [rule_format] :
"ALL (l :: Real).
 ALL (sk :: SWSketch).
 iX1 ((X_gn_inj :: SWExtrusion => SWFeature) (X_SWExtrusion sk l)) =
 ActExtrude
 (VWithLength((X_gn_inj :: VectorStar => Vector)
              (NormalVector(Plane'(sk))),
  l),
  iX3 sk)"

plane_is_plane [rule_format] :
"ALL (X_plane :: SWPlane).
 iX2 X_plane = PlaneX2 (SpacePoint(X_plane), NormalVector(X_plane))"

def_of_Cylinder [rule_format] :
"ALL (X_axis :: VectorStar).
 ALL (X_offset :: Point).
 ALL (r :: RealPos).
 Cylinder ((X_offset, r), X_axis) =
 (% x. let v = vec(X_offset, x)
       in ( || proj(v, (X_gn_inj :: VectorStar => Vector) X_axis) || <=_4
            || (X_gn_inj :: VectorStar => Vector) X_axis || &
            || orthcomp(v, (X_gn_inj :: VectorStar => Vector) X_axis) || <=_4
            (X_gn_inj :: RealPos => Real) r) &
          v *_8 (X_gn_inj :: VectorStar => Vector) X_axis >=_4
          (X_gn_inj :: X_Nat => Real) 0'')"

def_of_given_arc [rule_format] :
"arc = X_SWArc center boundarypoint boundarypoint"

cylinder_offset [rule_format] : "offset = center"

cylinder_radius [rule_format] :
"makePartial radius =
 (X_gn_proj :: Real => RealPos partial)
 ( || vec(center, boundarypoint) || )"

cylinder_axis [rule_format] :
"makePartial axis =
 (X_gn_proj :: Vector => VectorStar partial)
 (VWithLength((X_gn_inj :: VectorStar => Vector)
              (NormalVector(plane)),
  (X_gn_inj :: RealPos => Real) height))"

real_extrusion [rule_format] :
"(X_gn_inj :: RealPos => Real) height >_4
 (X_gn_inj :: X_Nat => Real) 0''"

real_arc [rule_format] : "~ center = boundarypoint"

the_arc_is_wellformed [rule_format] :
"let p = iX2 plane in center isIn p & boundarypoint isIn p"

declare ga_subt_reflexive [simp]
declare ga_subt_Int_XLt_Rat [simp]
declare ga_subt_Nat_XLt_Int [simp]
declare ga_subt_NonZero_XLt_Real [simp]
declare ga_subt_Pos_XLt_Nat [simp]
declare ga_subt_Rat_XLt_Real [simp]
declare ga_subt_Real_XLt_Point [simp]
declare ga_subt_Real_XLt_Vector [simp]
declare ga_subt_RealNonNeg_XLt_Real [simp]
declare ga_subt_RealPos_XLt_RealNonNeg [simp]
declare ga_subt_SWArc_XLt_SWSketchObject [simp]
declare ga_subt_SWExtrusion_XLt_SWFeature [simp]
declare ga_subt_SWFeature_XLt_SWObject [simp]
declare ga_subt_SWLine_XLt_SWSketchObject [simp]
declare ga_subt_SWPlane_XLt_SWObject [simp]
declare ga_subt_SWSketch_XLt_SWObject [simp]
declare ga_subt_SWSketchObject_XLt_SWObject [simp]
declare ga_subt_SWSpline_XLt_SWSketchObject [simp]
declare ga_subt_VectorStar_XLt_Vector [simp]
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
declare ga_select_C1_131 [simp]
declare ga_select_C2_132 [simp]
declare ga_select_C3_133 [simp]
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
declare ga_select_first [simp]
declare ga_select_rest [simp]
declare Ax4 [simp]
declare ga_assoc___Xx___83 [simp]
declare ga_right_unit___Xx___81 [simp]
declare ga_left_unit___Xx___82 [simp]
declare listop_basecase [simp]
declare cross_product_orthogonal [simp]
declare e1e2_nonlindep [simp]
declare vec_def [simp]
declare transitivity_of_vec_plus [simp]
declare emptySet_empty [simp]
declare allSet_contains_all [simp]
declare def_of_isIn [simp]
declare emptySet_union_right_unit [simp]
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
declare real_extrusion [simp]

theorem extrusion_is_cylinder :
"iX1
 ((X_gn_inj :: SWExtrusion => SWFeature)
  (X_SWExtrusion
   (X_SWSketch ((X_gn_inj :: SWArc => SWSketchObject) arc ::' ['])
    plane)
   ((X_gn_inj :: RealPos => Real) height))) =
 Cylinder ((offset, radius), axis)"
using binary_field_inverse inf_def RealNonNeg_pred_def
      RealPos_pred_def abs_def sqr_def sqrt_def Pos_def Zero_Point
      Zero_Vector VectorStar_pred_def scalar_multiplication
      scalar_product vector_product ONB1 ONB2 ONB3 lindep_def
      norm_from_inner_prod_def proj_def orthcomp_def orthogonal_def
      point_vector_map vec_def set_comprehension
      abbrev_of_set_comprehension function_image def_of_interval
      abbrev_of_interval plus_PointSet_Vector plus_Point_VectorSet
      plus_PointSet_VectorSet def_of_Plane E1_def E2_def E3_def
      VLine_constr VWithLength_constr VPlane_constr VPlane2_constr
      VConnected_constr VHalfSpace_constr VHalfSpace2_constr VBall_constr
      VCircle_constr ActAttach_constr ActExtrude_constr def_of_Cylinder
      def_of_given_arc cylinder_offset cylinder_radius cylinder_axis
by (auto)

ML "Header.record \"extrusion_is_cylinder\""

end
