theory Numbers_Int
imports "$HETS_LIB/Isabelle/MainHCPairs" "Primes" "Parity"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"ga_function_monotonicity\", \"ga_function_monotonicity_1\",
     \"ga_function_monotonicity_2\", \"ga_function_monotonicity_3\",
     \"ga_function_monotonicity_4\", \"ga_function_monotonicity_5\",
     \"ga_function_monotonicity_6\", \"ga_function_monotonicity_7\",
     \"ga_function_monotonicity_8\", \"ga_function_monotonicity_9\",
     \"ga_function_monotonicity_10\", \"ga_function_monotonicity_11\",
     \"ga_function_monotonicity_12\", \"ga_function_monotonicity_13\",
     \"ga_function_monotonicity_14\", \"ga_function_monotonicity_15\",
     \"ga_function_monotonicity_16\", \"ga_function_monotonicity_17\",
     \"ga_function_monotonicity_18\", \"ga_function_monotonicity_19\",
     \"ga_function_monotonicity_20\", \"ga_function_monotonicity_21\",
     \"ga_function_monotonicity_22\", \"ga_function_monotonicity_23\",
     \"ga_function_monotonicity_24\", \"ga_function_monotonicity_25\",
     \"ga_function_monotonicity_26\", \"ga_function_monotonicity_27\",
     \"ga_function_monotonicity_28\", \"ga_predicate_monotonicity\",
     \"ga_predicate_monotonicity_1\", \"ga_predicate_monotonicity_2\",
     \"ga_predicate_monotonicity_3\", \"ga_predicate_monotonicity_4\",
     \"ga_predicate_monotonicity_5\", \"ga_embedding_injectivity\",
     \"ga_projection_injectivity\", \"ga_projection\",
     \"ga_embedding_injectivity_1\", \"ga_projection_injectivity_1\",
     \"ga_projection_1\", \"ga_embedding_injectivity_2\",
     \"ga_projection_injectivity_2\", \"ga_projection_2\",
     \"ga_transitivity\", \"ga_selector_pre\", \"ga_injective_suc\",
     \"ga_disjoint_0_suc\", \"ga_selector_undef_pre_0\", \"X1_def_Nat\",
     \"X2_def_Nat\", \"X3_def_Nat\", \"X4_def_Nat\", \"X5_def_Nat\",
     \"X6_def_Nat\", \"X7_def_Nat\", \"X8_def_Nat\", \"X9_def_Nat\",
     \"decimal_def\", \"ga_comm___XPlus__\", \"ga_assoc___XPlus__\",
     \"ga_right_unit___XPlus__\", \"ga_left_unit___XPlus__\",
     \"ga_left_comm___XPlus__\", \"ga_comm___Xx__\",
     \"ga_assoc___Xx__\", \"ga_right_unit___Xx__\",
     \"ga_left_unit___Xx__\", \"ga_left_comm___Xx__\", \"ga_comm_min\",
     \"ga_assoc_min\", \"ga_left_comm_min\", \"ga_comm_max\",
     \"ga_assoc_max\", \"ga_right_unit_max\", \"ga_left_unit_max\",
     \"ga_left_comm_max\", \"leq_def1_Nat\", \"dvd_def_Nat\",
     \"leq_def2_Nat\", \"leq_def3_Nat\", \"geq_def_Nat\",
     \"less_def_Nat\", \"greater_def_Nat\", \"even_0_Nat\",
     \"even_suc_Nat\", \"odd_def_Nat\", \"factorial_0\",
     \"factorial_suc\", \"add_0_Nat\", \"add_suc_Nat\", \"mult_0_Nat\",
     \"mult_suc_Nat\", \"power_0_Nat\", \"power_suc_Nat\",
     \"min_def_Nat\", \"max_def_Nat\", \"subTotal_def1_Nat\",
     \"subTotal_def2_Nat\", \"sub_dom_Nat\", \"sub_def_Nat\",
     \"divide_dom_Nat\", \"divide_0_Nat\", \"divide_Pos_Nat\",
     \"div_dom_Nat\", \"div_Nat\", \"mod_dom_Nat\", \"mod_Nat\",
     \"distr1_Nat\", \"distr2_Nat\", \"Pos_def\", \"X1_as_Pos_def\",
     \"min_0\", \"div_mod_Nat\", \"power_Nat\", \"equality_Int\",
     \"Nat2Int_embedding\", \"ga_comm___XPlus___1\",
     \"ga_assoc___XPlus___1\", \"ga_right_unit___XPlus___1\",
     \"ga_left_unit___XPlus___1\", \"ga_left_comm___XPlus___1\",
     \"ga_comm___Xx___1\", \"ga_assoc___Xx___1\",
     \"ga_right_unit___Xx___1\", \"ga_left_unit___Xx___1\",
     \"ga_left_comm___Xx___1\", \"ga_comm_min_1\", \"ga_comm_max_1\",
     \"ga_assoc_min_1\", \"ga_assoc_max_1\", \"ga_left_comm_min_1\",
     \"ga_left_comm_max_1\", \"leq_def_Int\", \"geq_def_Int\",
     \"less_def_Int\", \"greater_def_Int\", \"even_def_Int\",
     \"odd_def_Int\", \"odd_alt_Int\", \"neg_def_Int\",
     \"sign_def_Int\", \"abs_def_Int\", \"add_def_Int\",
     \"mult_def_Int\", \"sub_def_Int\", \"min_def_Int\",
     \"max_def_Int\", \"power_neg1_Int\", \"power_others_Int\",
     \"divide_dom2_Int\", \"divide_alt_Int\", \"divide_Int\",
     \"div_dom_Int\", \"div_Int\", \"quot_dom_Int\", \"quot_neg_Int\",
     \"quot_nonneg_Int\", \"rem_dom_Int\", \"quot_rem_Int\",
     \"rem_nonneg_Int\", \"mod_dom_Int\", \"mod_Int\", \"distr1_Int\",
     \"distr2_Int\", \"Int_Nat_sub_compat\", \"abs_decomp_Int\",
     \"mod_abs_Int\", \"div_mod_Int\", \"quot_abs_Int\",
     \"rem_abs_Int\", \"quot_rem_Int_1\", \"power_Int\"]"

typedecl Pos
typedecl X_Int

datatype X_Nat = X0X2 ("0''''") | sucX1 "X_Nat" ("suc''/'(_')" [3] 999)

consts
X0X1 :: "X_Int" ("0''")
X1X1 :: "X_Int" ("1''")
X1X2 :: "X_Nat" ("1''''")
X1X3 :: "Pos" ("1'_3")
X2X1 :: "X_Int" ("2''")
X2X2 :: "X_Nat" ("2''''")
X3X1 :: "X_Int" ("3''")
X3X2 :: "X_Nat" ("3''''")
X4X1 :: "X_Int" ("4''")
X4X2 :: "X_Nat" ("4''''")
X5X1 :: "X_Int" ("5''")
X5X2 :: "X_Nat" ("5''''")
X6X1 :: "X_Int" ("6''")
X6X2 :: "X_Nat" ("6''''")
X7X1 :: "X_Int" ("7''")
X7X2 :: "X_Nat" ("7''''")
X8X1 :: "X_Int" ("8''")
X8X2 :: "X_Nat" ("8''''")
X9X1 :: "X_Int" ("9''")
X9X2 :: "X_Nat" ("9''''")
XMinus__X :: "X_Int => X_Int" ("(-''/ _)" [56] 56)
X__XAtXAt__X :: "X_Nat => X_Nat => X_Nat" ("(_/ @@/ _)" [54,54] 52)
X__XCaret__XX1 :: "X_Int => X_Nat => X_Int" ("(_/ ^''/ _)" [54,54] 52)
X__XCaret__XX2 :: "X_Nat => X_Nat => X_Nat" ("(_/ ^''''/ _)" [54,54] 52)
X__XExclam :: "X_Nat => X_Nat" ("(_/ !'')" [58] 58)
X__XGtXEq__XX1 :: "X_Int => X_Int => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XGtXEq__XX2 :: "X_Nat => X_Nat => bool" ("(_/ >=''''/ _)" [44,44] 42)
X__XGt__XX1 :: "X_Int => X_Int => bool" ("(_/ >''/ _)" [44,44] 42)
X__XGt__XX2 :: "X_Nat => X_Nat => bool" ("(_/ >''''/ _)" [44,44] 42)
X__XLtXEq__XX1 :: "X_Int => X_Int => bool" ("(_/ <=''/ _)" [44,44] 42)
X__XLtXEq__XX2 :: "X_Nat => X_Nat => bool" ("(_/ <=''''/ _)" [44,44] 42)
X__XLt__XX1 :: "X_Int => X_Int => bool" ("(_/ <''/ _)" [44,44] 42)
X__XLt__XX2 :: "X_Nat => X_Nat => bool" ("(_/ <''''/ _)" [44,44] 42)
X__XMinusXExclam__X :: "X_Nat => X_Nat => X_Nat" ("(_/ -!/ _)" [54,54] 52)
X__XMinusXQuest__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ -?/ _)" [54,54] 52)
X__XMinus__XX1 :: "X_Int => X_Int => X_Int" ("(_/ -''/ _)" [54,54] 52)
X__XMinus__XX2 :: "X_Nat => X_Nat => X_Int" ("(_/ -''''/ _)" [54,54] 52)
X__XPlus__XX1 :: "X_Int => X_Int => X_Int" ("(_/ +''/ _)" [54,54] 52)
X__XPlus__XX2 :: "X_Nat => X_Nat => X_Nat" ("(_/ +''''/ _)" [54,54] 52)
X__XPlus__XX3 :: "X_Nat => Pos => Pos" ("(_/ +'_3/ _)" [54,54] 52)
X__XPlus__XX4 :: "Pos => X_Nat => Pos" ("(_/ +'_4/ _)" [54,54] 52)
X__XSlashXQuest__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ '/?''/ _)" [54,54] 52)
X__XSlashXQuest__XX2 :: "X_Nat => X_Nat => X_Nat partial" ("(_/ '/?''''/ _)" [54,54] 52)
X__Xx__XX1 :: "X_Int => X_Int => X_Int" ("(_/ *''/ _)" [54,54] 52)
X__Xx__XX2 :: "X_Nat => X_Nat => X_Nat" ("(_/ *''''/ _)" [54,54] 52)
X__Xx__XX3 :: "Pos => Pos => Pos" ("(_/ *'_3/ _)" [54,54] 52)
X__div__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ div''/ _)" [54,54] 52)
X__div__XX2 :: "X_Nat => X_Nat => X_Nat partial" ("(_/ div''''/ _)" [54,54] 52)
X__dvd__X :: "X_Nat => X_Nat => bool" ("(_/ dvd''/ _)" [44,44] 42)
X__mod__XX1 :: "X_Int => X_Int => X_Nat partial" ("(_/ mod''/ _)" [54,54] 52)
X__mod__XX2 :: "X_Nat => X_Nat => X_Nat partial" ("(_/ mod''''/ _)" [54,54] 52)
X__quot__X :: "X_Int => X_Int => X_Int partial" ("(_/ quot/ _)" [54,54] 52)
X__rem__X :: "X_Int => X_Int => X_Int partial" ("(_/ rem/ _)" [54,54] 52)
X_abs :: "X_Int => X_Nat" ("abs''/'(_')" [3] 999)
X_evenX1 :: "X_Int => bool" ("even''/'(_')" [3] 999)
X_evenX2 :: "X_Nat => bool" ("even''''/'(_')" [3] 999)
X_gn_inj_Nat_Int :: "X_Nat => X_Int" ("gn'_inj'_Nat'_Int/'(_')" [3] 999)
X_gn_inj_Pos_Int :: "Pos => X_Int" ("gn'_inj'_Pos'_Int/'(_')" [3] 999)
X_gn_inj_Pos_Nat :: "Pos => X_Nat" ("gn'_inj'_Pos'_Nat/'(_')" [3] 999)
X_gn_proj_Int_Nat :: "X_Int => X_Nat partial" ("gn'_proj'_Int'_Nat/'(_')" [3] 999)
X_gn_proj_Int_Pos :: "X_Int => Pos partial" ("gn'_proj'_Int'_Pos/'(_')" [3] 999)
X_gn_proj_Nat_Pos :: "X_Nat => Pos partial" ("gn'_proj'_Nat'_Pos/'(_')" [3] 999)
X_maxX1 :: "X_Int => X_Int => X_Int" ("max''/'(_,/ _')" [3,3] 999)
X_maxX2 :: "X_Nat => X_Nat => X_Nat" ("max''''/'(_,/ _')" [3,3] 999)
X_minX1 :: "X_Int => X_Int => X_Int" ("min''/'(_,/ _')" [3,3] 999)
X_minX2 :: "X_Nat => X_Nat => X_Nat" ("min''''/'(_,/ _')" [3,3] 999)
X_oddX1 :: "X_Int => bool" ("odd''/'(_')" [3] 999)
X_oddX2 :: "X_Nat => bool" ("odd''''/'(_')" [3] 999)
X_pre :: "X_Nat => X_Nat partial" ("pre/'(_')" [3] 999)
X_sign :: "X_Int => X_Int" ("sign/'(_')" [3] 999)
sucX2 :: "X_Nat => Pos" ("suc''''/'(_')" [3] 999)

section "Extension of Naturals"
(* we introduce some new symbols *)
consts combine_nat :: "nat => nat => nat" ("(_/ @@@/ _)" [54,54] 52)
consts part_div :: "nat => nat => nat partial" ("(_/ '/??/ _)" [54,54] 52)
consts part_minus :: "nat => nat => nat partial" ("(_/ '-??/ _)" [54,54] 52)

primrec pre_nat
where
  pre_nat_0: "pre_nat 0 = noneOp"
  | pre_nat_suc: "pre_nat (Suc n) = makePartial n"


axioms
ga_function_monotonicity [rule_format] : "0' = gn_inj_Nat_Int(0'')"

ga_function_monotonicity_1 [rule_format] :
"1' = gn_inj_Nat_Int(1'')"

ga_function_monotonicity_2 [rule_format] :
"1' = gn_inj_Pos_Int(1_3)"

ga_function_monotonicity_3 [rule_format] :
"1'' = gn_inj_Pos_Nat(1_3)"

ga_function_monotonicity_4 [rule_format] :
"2' = gn_inj_Nat_Int(2'')"

ga_function_monotonicity_5 [rule_format] :
"3' = gn_inj_Nat_Int(3'')"

ga_function_monotonicity_6 [rule_format] :
"4' = gn_inj_Nat_Int(4'')"

ga_function_monotonicity_7 [rule_format] :
"5' = gn_inj_Nat_Int(5'')"

ga_function_monotonicity_8 [rule_format] :
"6' = gn_inj_Nat_Int(6'')"

ga_function_monotonicity_9 [rule_format] :
"7' = gn_inj_Nat_Int(7'')"

ga_function_monotonicity_10 [rule_format] :
"8' = gn_inj_Nat_Int(8'')"

ga_function_monotonicity_11 [rule_format] :
"9' = gn_inj_Nat_Int(9'')"

ga_function_monotonicity_12 [rule_format] :
"ALL x1.
 ALL x2.
 gn_inj_Nat_Int(x1) *' gn_inj_Nat_Int(x2) =
 gn_inj_Nat_Int(x1 *'' x2)"

ga_function_monotonicity_13 [rule_format] :
"ALL x1.
 ALL x2.
 gn_inj_Pos_Int(x1) *' gn_inj_Pos_Int(x2) =
 gn_inj_Pos_Int(x1 *_3 x2)"

ga_function_monotonicity_14 [rule_format] :
"ALL x1.
 ALL x2.
 gn_inj_Pos_Nat(x1) *'' gn_inj_Pos_Nat(x2) =
 gn_inj_Pos_Nat(x1 *_3 x2)"

ga_function_monotonicity_15 [rule_format] :
"ALL x1.
 ALL x2.
 gn_inj_Nat_Int(x1) +' gn_inj_Nat_Int(x2) =
 gn_inj_Nat_Int(x1 +'' x2)"

ga_function_monotonicity_16 [rule_format] :
"ALL x1.
 ALL x2.
 gn_inj_Nat_Int(x1) +' gn_inj_Pos_Int(x2) =
 gn_inj_Pos_Int(x1 +_3 x2)"

ga_function_monotonicity_17 [rule_format] :
"ALL x1.
 ALL x2.
 gn_inj_Pos_Int(x1) +' gn_inj_Nat_Int(x2) =
 gn_inj_Pos_Int(x1 +_4 x2)"

ga_function_monotonicity_18 [rule_format] :
"ALL x1.
 ALL x2. x1 +'' gn_inj_Pos_Nat(x2) = gn_inj_Pos_Nat(x1 +_3 x2)"

ga_function_monotonicity_19 [rule_format] :
"ALL x1.
 ALL x2. gn_inj_Pos_Nat(x1) +'' x2 = gn_inj_Pos_Nat(x1 +_4 x2)"

ga_function_monotonicity_20 [rule_format] :
"ALL x1.
 ALL x2. gn_inj_Pos_Nat(x1) +_3 x2 = x1 +_4 gn_inj_Pos_Nat(x2)"

ga_function_monotonicity_21 [rule_format] :
"ALL x1.
 ALL x2. gn_inj_Nat_Int(x1) -' gn_inj_Nat_Int(x2) = x1 -'' x2"

ga_function_monotonicity_22 [rule_format] :
"ALL x1.
 ALL x2.
 gn_inj_Nat_Int(x1) /?' gn_inj_Nat_Int(x2) =e=
 (let (Xb1, Xc0) = x1 /?'' x2
  in if Xb1 then makePartial (gn_inj_Nat_Int(Xc0)) else noneOp)"

ga_function_monotonicity_23 [rule_format] :
"ALL x1.
 ALL x2. gn_inj_Nat_Int(x1) ^' x2 = gn_inj_Nat_Int(x1 ^'' x2)"

ga_function_monotonicity_24 [rule_format] :
"ALL x1.
 ALL x2.
 gn_inj_Nat_Int(x1) div' gn_inj_Nat_Int(x2) =e=
 (let (Xb1, Xc0) = x1 div'' x2
  in if Xb1 then makePartial (gn_inj_Nat_Int(Xc0)) else noneOp)"

ga_function_monotonicity_25 [rule_format] :
"ALL x1.
 ALL x2. gn_inj_Nat_Int(x1) mod' gn_inj_Nat_Int(x2) =e= x1 mod'' x2"

ga_function_monotonicity_26 [rule_format] :
"ALL x1.
 ALL x2.
 max'(gn_inj_Nat_Int(x1), gn_inj_Nat_Int(x2)) =
 gn_inj_Nat_Int(max''(x1, x2))"

ga_function_monotonicity_27 [rule_format] :
"ALL x1.
 ALL x2.
 min'(gn_inj_Nat_Int(x1), gn_inj_Nat_Int(x2)) =
 gn_inj_Nat_Int(min''(x1, x2))"

ga_function_monotonicity_28 [rule_format] :
"ALL x1. suc'(x1) = gn_inj_Pos_Nat(suc''(x1))"

ga_predicate_monotonicity [rule_format] :
"ALL x1.
 ALL x2. (gn_inj_Nat_Int(x1) <' gn_inj_Nat_Int(x2)) = (x1 <'' x2)"

ga_predicate_monotonicity_1 [rule_format] :
"ALL x1.
 ALL x2. (gn_inj_Nat_Int(x1) <=' gn_inj_Nat_Int(x2)) = (x1 <='' x2)"

ga_predicate_monotonicity_2 [rule_format] :
"ALL x1.
 ALL x2. (gn_inj_Nat_Int(x1) >' gn_inj_Nat_Int(x2)) = (x1 >'' x2)"

ga_predicate_monotonicity_3 [rule_format] :
"ALL x1.
 ALL x2. (gn_inj_Nat_Int(x1) >=' gn_inj_Nat_Int(x2)) = (x1 >='' x2)"

ga_predicate_monotonicity_4 [rule_format] :
"ALL x1. even'(gn_inj_Nat_Int(x1)) = even''(x1)"

ga_predicate_monotonicity_5 [rule_format] :
"ALL x1. odd'(gn_inj_Nat_Int(x1)) = odd''(x1)"

ga_embedding_injectivity [rule_format] :
"ALL x. ALL y. gn_inj_Nat_Int(x) = gn_inj_Nat_Int(y) --> x = y"

ga_projection_injectivity [rule_format] :
"ALL x. ALL y. gn_proj_Int_Nat(x) =e= gn_proj_Int_Nat(y) --> x = y"

ga_projection [rule_format] :
"ALL x. gn_proj_Int_Nat(gn_inj_Nat_Int(x)) = makePartial x"

ga_embedding_injectivity_1 [rule_format] :
"ALL x. ALL y. gn_inj_Pos_Int(x) = gn_inj_Pos_Int(y) --> x = y"

ga_projection_injectivity_1 [rule_format] :
"ALL x. ALL y. gn_proj_Int_Pos(x) =e= gn_proj_Int_Pos(y) --> x = y"

ga_projection_1 [rule_format] :
"ALL x. gn_proj_Int_Pos(gn_inj_Pos_Int(x)) = makePartial x"

ga_embedding_injectivity_2 [rule_format] :
"ALL x. ALL y. gn_inj_Pos_Nat(x) = gn_inj_Pos_Nat(y) --> x = y"

ga_projection_injectivity_2 [rule_format] :
"ALL x. ALL y. gn_proj_Nat_Pos(x) =e= gn_proj_Nat_Pos(y) --> x = y"

ga_projection_2 [rule_format] :
"ALL x. gn_proj_Nat_Pos(gn_inj_Pos_Nat(x)) = makePartial x"

ga_transitivity [rule_format] :
"ALL x. gn_inj_Nat_Int(gn_inj_Pos_Nat(x)) = gn_inj_Pos_Int(x)"

ga_selector_pre [rule_format] :
"ALL XX1. pre(suc'(XX1)) = makePartial XX1"

ga_injective_suc [rule_format] :
"ALL XX1. ALL Y1. suc'(XX1) = suc'(Y1) = (XX1 = Y1)"

ga_disjoint_0_suc [rule_format] : "ALL Y1. ~ 0'' = suc'(Y1)"

ga_selector_undef_pre_0 [rule_format] : "~ defOp (pre(0''))"

X1_def_Nat [rule_format] : "1'' = suc'(0'')"

X2_def_Nat [rule_format] : "2'' = suc'(1'')"

X3_def_Nat [rule_format] : "3'' = suc'(2'')"

X4_def_Nat [rule_format] : "4'' = suc'(3'')"

X5_def_Nat [rule_format] : "5'' = suc'(4'')"

X6_def_Nat [rule_format] : "6'' = suc'(5'')"

X7_def_Nat [rule_format] : "7'' = suc'(6'')"

X8_def_Nat [rule_format] : "8'' = suc'(7'')"

X9_def_Nat [rule_format] : "9'' = suc'(8'')"

decimal_def [rule_format] :
"ALL m. ALL X_n. m @@ X_n = (m *'' suc'(9'')) +'' X_n"

ga_comm___XPlus__ [rule_format] : "ALL x. ALL y. x +'' y = y +'' x"

ga_assoc___XPlus__ [rule_format] :
"ALL x. ALL y. ALL z. (x +'' y) +'' z = x +'' (y +'' z)"

ga_right_unit___XPlus__ [rule_format] : "ALL x. x +'' 0'' = x"

ga_left_unit___XPlus__ [rule_format] : "ALL x. 0'' +'' x = x"

ga_left_comm___XPlus__ [rule_format] :
"ALL x. ALL y. ALL z. x +'' (y +'' z) = y +'' (x +'' z)"

ga_comm___Xx__ [rule_format] : "ALL x. ALL y. x *'' y = y *'' x"

ga_assoc___Xx__ [rule_format] :
"ALL x. ALL y. ALL z. (x *'' y) *'' z = x *'' (y *'' z)"

ga_right_unit___Xx__ [rule_format] : "ALL x. x *'' 1'' = x"

ga_left_unit___Xx__ [rule_format] : "ALL x. 1'' *'' x = x"

ga_left_comm___Xx__ [rule_format] :
"ALL x. ALL y. ALL z. x *'' (y *'' z) = y *'' (x *'' z)"

ga_comm_min [rule_format] :
"ALL x. ALL y. min''(x, y) = min''(y, x)"

ga_assoc_min [rule_format] :
"ALL x.
 ALL y. ALL z. min''(min''(x, y), z) = min''(x, min''(y, z))"

ga_left_comm_min [rule_format] :
"ALL x.
 ALL y. ALL z. min''(x, min''(y, z)) = min''(y, min''(x, z))"

ga_comm_max [rule_format] :
"ALL x. ALL y. max''(x, y) = max''(y, x)"

ga_assoc_max [rule_format] :
"ALL x.
 ALL y. ALL z. max''(max''(x, y), z) = max''(x, max''(y, z))"

ga_right_unit_max [rule_format] : "ALL x. max''(x, 0'') = x"

ga_left_unit_max [rule_format] : "ALL x. max''(0'', x) = x"

ga_left_comm_max [rule_format] :
"ALL x.
 ALL y. ALL z. max''(x, max''(y, z)) = max''(y, max''(x, z))"

leq_def1_Nat [rule_format] : "ALL X_n. 0'' <='' X_n"

dvd_def_Nat [rule_format] :
"ALL m. ALL X_n. (m dvd' X_n) = (EX k. X_n = m *'' k)"

leq_def2_Nat [rule_format] : "ALL X_n. ~ suc'(X_n) <='' 0''"

leq_def3_Nat [rule_format] :
"ALL m. ALL X_n. (suc'(m) <='' suc'(X_n)) = (m <='' X_n)"

geq_def_Nat [rule_format] :
"ALL m. ALL X_n. (m >='' X_n) = (X_n <='' m)"

less_def_Nat [rule_format] :
"ALL m. ALL X_n. (m <'' X_n) = (m <='' X_n & ~ m = X_n)"

greater_def_Nat [rule_format] :
"ALL m. ALL X_n. (m >'' X_n) = (X_n <'' m)"

even_0_Nat [rule_format] : "even''(0'')"

even_suc_Nat [rule_format] : "ALL m. even''(suc'(m)) = odd''(m)"

odd_def_Nat [rule_format] : "ALL m. odd''(m) = (~ even''(m))"

factorial_0 [rule_format] : "0'' !' = 1''"

factorial_suc [rule_format] :
"ALL X_n. suc'(X_n) !' = suc'(X_n) *'' X_n !'"

add_0_Nat [rule_format] : "ALL m. 0'' +'' m = m"

add_suc_Nat [rule_format] :
"ALL m. ALL X_n. suc'(X_n) +'' m = suc'(X_n +'' m)"

mult_0_Nat [rule_format] : "ALL m. 0'' *'' m = 0''"

mult_suc_Nat [rule_format] :
"ALL m. ALL X_n. suc'(X_n) *'' m = (X_n *'' m) +'' m"

power_0_Nat [rule_format] : "ALL m. m ^'' 0'' = 1''"

power_suc_Nat [rule_format] :
"ALL m. ALL X_n. m ^'' suc'(X_n) = m *'' (m ^'' X_n)"

min_def_Nat [rule_format] :
"ALL m. ALL X_n. min''(m, X_n) = (if m <='' X_n then m else X_n)"

max_def_Nat [rule_format] :
"ALL m. ALL X_n. max''(m, X_n) = (if m <='' X_n then X_n else m)"

subTotal_def1_Nat [rule_format] :
"ALL m. ALL X_n. m >'' X_n --> X_n -! m = 0''"

subTotal_def2_Nat [rule_format] :
"ALL m. ALL X_n. m <='' X_n --> makePartial (X_n -! m) = X_n -? m"

sub_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m -? X_n) = (m >='' X_n)"

sub_def_Nat [rule_format] :
"ALL m. ALL X_n. ALL r. m -? X_n = makePartial r = (m = r +'' X_n)"

divide_dom_Nat [rule_format] :
"ALL m.
 ALL X_n.
 defOp (m /?'' X_n) = (~ X_n = 0'' & m mod'' X_n = makePartial 0'')"

divide_0_Nat [rule_format] : "ALL m. ~ defOp (m /?'' 0'')"

divide_Pos_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 X_n >'' 0'' --> m /?'' X_n = makePartial r = (m = r *'' X_n)"

div_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m div'' X_n) = (~ X_n = 0'')"

div_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m div'' X_n = makePartial r =
 (EX s. m = (X_n *'' r) +'' s & s <'' X_n)"

mod_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m mod'' X_n) = (~ X_n = 0'')"

mod_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ALL s.
 m mod'' X_n = makePartial s =
 (EX r. m = (X_n *'' r) +'' s & s <'' X_n)"

distr1_Nat [rule_format] :
"ALL r. ALL s. ALL t. (r +'' s) *'' t = (r *'' t) +'' (s *'' t)"

distr2_Nat [rule_format] :
"ALL r. ALL s. ALL t. t *'' (r +'' s) = (t *'' r) +'' (t *'' s)"

Pos_def [rule_format] :
"ALL p. defOp (gn_proj_Nat_Pos(p)) = (p >'' 0'')"

X1_as_Pos_def [rule_format] : "1_3 = suc''(0'')"

min_0 [rule_format] : "ALL m. min''(m, 0'') = 0''"

div_mod_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ~ X_n = 0'' -->
 makePartial m =
 (let (Xb5, Xc0) =
      let (Xb4, Xc3) = m div'' X_n
      in if Xb4 then makePartial (Xc3 *'' X_n) else noneOp
  in if Xb5
        then let (Xb2, Xc1) = m mod'' X_n
             in if Xb2 then makePartial (Xc0 +'' Xc1) else noneOp
        else noneOp)"

power_Nat [rule_format] :
"ALL m. ALL r. ALL s. m ^'' (r +'' s) = (m ^'' r) *'' (m ^'' s)"

decimal_def_nat [rule_format] : 
"ALL m. ALL X_n. m @@@ X_n = (m * Suc(9)) + X_n"

equality_Int [rule_format] :
"ALL a.
 ALL b. ALL c. ALL d. a -'' b = c -'' d = (a +'' d = c +'' b)"

Nat2Int_embedding [rule_format] :
"ALL a. gn_inj_Nat_Int(a) = a -'' 0''"

ga_comm___XPlus___1 [rule_format] : "ALL x. ALL y. x +' y = y +' x"

ga_assoc___XPlus___1 [rule_format] :
"ALL x. ALL y. ALL z. (x +' y) +' z = x +' (y +' z)"

ga_right_unit___XPlus___1 [rule_format] :
"ALL x. x +' gn_inj_Nat_Int(0'') = x"

ga_left_unit___XPlus___1 [rule_format] :
"ALL x. gn_inj_Nat_Int(0'') +' x = x"

ga_left_comm___XPlus___1 [rule_format] :
"ALL x. ALL y. ALL z. x +' (y +' z) = y +' (x +' z)"

ga_comm___Xx___1 [rule_format] : "ALL x. ALL y. x *' y = y *' x"

ga_assoc___Xx___1 [rule_format] :
"ALL x. ALL y. ALL z. (x *' y) *' z = x *' (y *' z)"

ga_right_unit___Xx___1 [rule_format] :
"ALL x. x *' gn_inj_Pos_Int(1_3) = x"

ga_left_unit___Xx___1 [rule_format] :
"ALL x. gn_inj_Pos_Int(1_3) *' x = x"

ga_left_comm___Xx___1 [rule_format] :
"ALL x. ALL y. ALL z. x *' (y *' z) = y *' (x *' z)"

ga_comm_min_1 [rule_format] :
"ALL x. ALL y. min'(x, y) = min'(y, x)"

ga_comm_max_1 [rule_format] :
"ALL x. ALL y. max'(x, y) = max'(y, x)"

ga_assoc_min_1 [rule_format] :
"ALL x. ALL y. ALL z. min'(min'(x, y), z) = min'(x, min'(y, z))"

ga_assoc_max_1 [rule_format] :
"ALL x. ALL y. ALL z. max'(max'(x, y), z) = max'(x, max'(y, z))"

ga_left_comm_min_1 [rule_format] :
"ALL x. ALL y. ALL z. min'(x, min'(y, z)) = min'(y, min'(x, z))"

ga_left_comm_max_1 [rule_format] :
"ALL x. ALL y. ALL z. max'(x, max'(y, z)) = max'(y, max'(x, z))"

leq_def_Int [rule_format] :
"ALL m. ALL X_n. (m <=' X_n) = defOp (gn_proj_Int_Nat(X_n -' m))"

geq_def_Int [rule_format] :
"ALL m. ALL X_n. (m >=' X_n) = (X_n <=' m)"

less_def_Int [rule_format] :
"ALL m. ALL X_n. (m <' X_n) = (m <=' X_n & ~ m = X_n)"

greater_def_Int [rule_format] :
"ALL m. ALL X_n. (m >' X_n) = (X_n <' m)"

even_def_Int [rule_format] : "ALL m. even'(m) = even''(abs'(m))"

odd_def_Int [rule_format] : "ALL m. odd'(m) = (~ even'(m))"

odd_alt_Int [rule_format] : "ALL m. odd'(m) = odd''(abs'(m))"

neg_def_Int [rule_format] : "ALL a. ALL b. -' (a -'' b) = b -'' a"

sign_def_Int [rule_format] :
"ALL m.
 sign(m) =
 (if m = gn_inj_Nat_Int(0'') then gn_inj_Nat_Int(0'')
     else if m >' gn_inj_Nat_Int(0'') then gn_inj_Pos_Int(1_3)
             else -' gn_inj_Pos_Int(1_3))"

abs_def_Int [rule_format] :
"ALL m.
 gn_inj_Nat_Int(abs'(m)) =
 (if m <' gn_inj_Nat_Int(0'') then -' m else m)"

add_def_Int [rule_format] :
"ALL a.
 ALL b.
 ALL c. ALL d. (a -'' b) +' (c -'' d) = (a +'' c) -'' (b +'' d)"

mult_def_Int [rule_format] :
"ALL a.
 ALL b.
 ALL c.
 ALL d.
 (a -'' b) *' (c -'' d) =
 ((a *'' c) +'' (b *'' d)) -'' ((b *'' c) +'' (a *'' d))"

sub_def_Int [rule_format] :
"ALL m. ALL X_n. m -' X_n = m +' -' X_n"

min_def_Int [rule_format] :
"ALL m. ALL X_n. min'(m, X_n) = (if m <=' X_n then m else X_n)"

max_def_Int [rule_format] :
"ALL m. ALL X_n. max'(m, X_n) = (if m <=' X_n then X_n else m)"

power_neg1_Int [rule_format] :
"ALL a.
 -' gn_inj_Pos_Int(1_3) ^' a =
 (if even''(a) then gn_inj_Pos_Int(1_3)
     else -' gn_inj_Pos_Int(1_3))"

power_others_Int [rule_format] :
"ALL m.
 ALL a.
 ~ m = -' gn_inj_Pos_Int(1_3) -->
 m ^' a = (sign(m) ^' a) *' gn_inj_Nat_Int(abs'(m) ^'' a)"

divide_dom2_Int [rule_format] :
"ALL m.
 ALL X_n. defOp (m /?' X_n) = (m mod' X_n = makePartial 0'')"

divide_alt_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m /?' X_n = makePartial r =
 (~ X_n = gn_inj_Nat_Int(0'') & X_n *' r = m)"

divide_Int [rule_format] :
"ALL m.
 ALL X_n.
 m /?' X_n =s=
 (let (Xb3, Xc0) =
      let (Xb2, Xc1) = abs'(m) /?'' abs'(X_n)
      in if Xb2 then makePartial (gn_inj_Nat_Int(Xc1)) else noneOp
  in if Xb3 then makePartial ((sign(m) *' sign(X_n)) *' Xc0)
        else noneOp)"

div_dom_Int [rule_format] :
"ALL m.
 ALL X_n. defOp (m div' X_n) = (~ X_n = gn_inj_Nat_Int(0''))"

div_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m div' X_n = makePartial r =
 (EX a. m = (X_n *' r) +' gn_inj_Nat_Int(a) & a <'' abs'(X_n))"

quot_dom_Int [rule_format] :
"ALL m.
 ALL X_n. defOp (m quot X_n) = (~ X_n = gn_inj_Nat_Int(0''))"

quot_neg_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m <' gn_inj_Nat_Int(0'') -->
 m quot X_n = makePartial r =
 (EX s.
  m = (X_n *' r) +' s &
  gn_inj_Nat_Int(0'') >=' s & s >' -' gn_inj_Nat_Int(abs'(X_n)))"

quot_nonneg_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m >=' gn_inj_Nat_Int(0'') -->
 m quot X_n = makePartial r =
 (EX s.
  m = (X_n *' r) +' s &
  gn_inj_Nat_Int(0'') <=' s & s <' gn_inj_Nat_Int(abs'(X_n)))"

rem_dom_Int [rule_format] :
"ALL m. ALL X_n. defOp (m rem X_n) = (~ X_n = gn_inj_Nat_Int(0''))"

quot_rem_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL s.
 m <' gn_inj_Nat_Int(0'') -->
 m rem X_n = makePartial s =
 (EX r.
  m = (X_n *' r) +' s &
  gn_inj_Nat_Int(0'') >=' s & s >' -' gn_inj_Nat_Int(abs'(X_n)))"

rem_nonneg_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL s.
 m >=' gn_inj_Nat_Int(0'') -->
 m rem X_n = makePartial s =
 (EX r.
  m = (X_n *' r) +' s &
  gn_inj_Nat_Int(0'') <=' s & s <' gn_inj_Nat_Int(abs'(X_n)))"

mod_dom_Int [rule_format] :
"ALL m.
 ALL X_n. defOp (m mod' X_n) = (~ X_n = gn_inj_Nat_Int(0''))"

mod_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL a.
 m mod' X_n = makePartial a =
 (EX r. m = (X_n *' r) +' gn_inj_Nat_Int(a) & a <'' abs'(X_n))"

distr1_Int [rule_format] :
"ALL r. ALL s. ALL t. (r +' s) *' t = (r *' t) +' (s *' t)"

distr2_Int [rule_format] :
"ALL r. ALL s. ALL t. t *' (r +' s) = (t *' r) +' (t *' s)"

Int_Nat_sub_compat [rule_format] :
"ALL a.
 ALL b.
 defOp (a -? b) -->
 (let (Xb1, Xc0) = a -? b
  in if Xb1 then makePartial (gn_inj_Nat_Int(Xc0)) else noneOp) =
 makePartial (a -'' b)"

abs_decomp_Int [rule_format] :
"ALL m. m = sign(m) *' gn_inj_Nat_Int(abs'(m))"

mod_abs_Int [rule_format] :
"ALL m. ALL X_n. m mod' X_n =s= m mod' gn_inj_Nat_Int(abs'(X_n))"

div_mod_Int [rule_format] :
"ALL m.
 ALL X_n.
 ~ X_n = gn_inj_Nat_Int(0'') -->
 makePartial m =
 (let (Xb7, Xc0) =
      let (Xb6, Xc5) = m div' X_n
      in if Xb6 then makePartial (Xc5 *' X_n) else noneOp
  in if Xb7
        then let (Xb4, Xc1) =
                 let (Xb3, Xc2) = m mod' X_n
                 in if Xb3 then makePartial (gn_inj_Nat_Int(Xc2)) else noneOp
             in if Xb4 then makePartial (Xc0 +' Xc1) else noneOp
        else noneOp)"

quot_abs_Int [rule_format] :
"ALL m.
 ALL X_n.
 (let (Xb3, Xc0) =
      let (Xb2, Xc1) = m quot X_n
      in if Xb2 then makePartial (abs'(Xc1)) else noneOp
  in if Xb3 then makePartial (gn_inj_Nat_Int(Xc0)) else noneOp) =s=
 gn_inj_Nat_Int(abs'(m)) quot gn_inj_Nat_Int(abs'(X_n))"

rem_abs_Int [rule_format] :
"ALL m.
 ALL X_n.
 (let (Xb3, Xc0) =
      let (Xb2, Xc1) = m rem X_n
      in if Xb2 then makePartial (abs'(Xc1)) else noneOp
  in if Xb3 then makePartial (gn_inj_Nat_Int(Xc0)) else noneOp) =s=
 gn_inj_Nat_Int(abs'(m)) rem gn_inj_Nat_Int(abs'(X_n))"

quot_rem_Int_1 [rule_format] :
"ALL m.
 ALL X_n.
 ~ X_n = gn_inj_Nat_Int(0'') -->
 makePartial m =
 (let (Xb5, Xc0) =
      let (Xb4, Xc3) = m quot X_n
      in if Xb4 then makePartial (Xc3 *' X_n) else noneOp
  in if Xb5
        then let (Xb2, Xc1) = m rem X_n
             in if Xb2 then makePartial (Xc0 +' Xc1) else noneOp
        else noneOp)"

power_Int [rule_format] :
"ALL m. ALL a. ALL b. m ^' (a +'' b) = (m ^' a) *' (m ^' b)"

part_div_def : "x /??y = (if (x mod y = 0) then makePartial(x div y) else noneOp)"
part_minus_def : "x -?? y = (if (x>=y) then makePartial(x-y) else noneOp)"

declare ga_projection [simp]
declare ga_projection_1 [simp]
declare ga_projection_2 [simp]
declare ga_transitivity [simp]
declare ga_selector_pre [simp]
declare ga_selector_undef_pre_0 [simp]
declare ga_comm___XPlus__ [simp]
declare ga_assoc___XPlus__ [simp]
declare ga_right_unit___XPlus__ [simp]
declare ga_left_unit___XPlus__ [simp]
declare ga_left_comm___XPlus__ [simp]
declare ga_comm___Xx__ [simp]
declare ga_assoc___Xx__ [simp]
declare ga_right_unit___Xx__ [simp]
declare ga_left_unit___Xx__ [simp]
declare ga_left_comm___Xx__ [simp]
declare ga_comm_min [simp]
declare ga_assoc_min [simp]
declare ga_left_comm_min [simp]
declare ga_comm_max [simp]
declare ga_assoc_max [simp]
declare ga_right_unit_max [simp]
declare ga_left_unit_max [simp]
declare ga_left_comm_max [simp]
declare leq_def1_Nat [simp]
declare dvd_def_Nat [simp]
declare leq_def2_Nat [simp]
declare leq_def3_Nat [simp]
declare geq_def_Nat [simp]
declare less_def_Nat [simp]
declare greater_def_Nat [simp]
declare even_0_Nat [simp]
declare even_suc_Nat [simp]
declare odd_def_Nat [simp]
declare factorial_0 [simp]
declare factorial_suc [simp]
declare add_0_Nat [simp]
declare add_suc_Nat [simp]
declare mult_0_Nat [simp]
declare mult_suc_Nat [simp]
declare power_0_Nat [simp]
declare power_suc_Nat [simp]
declare subTotal_def1_Nat [simp]
declare subTotal_def2_Nat [simp]
declare sub_dom_Nat [simp]
declare divide_0_Nat [simp]
declare min_0 [simp]
declare ga_comm___XPlus___1 [simp]
declare ga_assoc___XPlus___1 [simp]
declare ga_right_unit___XPlus___1 [simp]
declare ga_left_unit___XPlus___1 [simp]
declare ga_left_comm___XPlus___1 [simp]
declare ga_comm___Xx___1 [simp]
declare ga_assoc___Xx___1 [simp]
declare ga_right_unit___Xx___1 [simp]
declare ga_left_unit___Xx___1 [simp]
declare ga_left_comm___Xx___1 [simp]
declare ga_comm_min_1 [simp]
declare ga_comm_max_1 [simp]
declare ga_assoc_min_1 [simp]
declare ga_assoc_max_1 [simp]
declare ga_left_comm_min_1 [simp]
declare ga_left_comm_max_1 [simp]
declare leq_def_Int [simp]
declare even_def_Int [simp]
declare odd_alt_Int [simp]
declare neg_def_Int [simp]
declare sign_def_Int [simp]
declare abs_def_Int [simp]
declare add_def_Int [simp]
declare mult_def_Int [simp]
declare sub_def_Int [simp]
declare min_def_Int [simp]
declare max_def_Int [simp]
declare power_neg1_Int [simp]
declare power_others_Int [simp]
declare divide_Int [simp]
declare div_Int [simp]
declare quot_neg_Int [simp]
declare quot_nonneg_Int [simp]
declare quot_rem_Int [simp]
declare rem_nonneg_Int [simp]
declare mod_Int [simp]
declare mod_abs_Int [simp]

section "Nat2nat copy (cannot be imported for some reasons)"

section "Strong Equality"

lemma strong_equality : "!! (t::'a partial) (s::'a partial) . (t =s= s)  =  (! x . ((t = makePartial x) <-> (s = makePartial x)))"
apply (rule iffI)
defer
apply (unfold makePartial_def)
apply (unfold strongEqualOp_def)
apply (auto)
done

lemma normal2strong: "!!a b. (a=b) ==> (a =s= b)"
apply (unfold strongEqualOp_def)
apply (auto)
done

lemma makepartial_intro : "(s=makePartial t) = (defOp(s) & (snd(s)=t))"
apply (rule iffI)
apply (simp add: makePartial_def)
apply (subst defOp_def)
apply (simp)
apply (simp add: makePartial_def)
apply (case_tac "s")
apply (simp add: defOp_def)
done

lemma makepartial_intro_weak: "(s=makePartial t) ==> (snd(s)=t)"
apply (simp add: makePartial_def)
done


lemma makePartialproj: "snd (makePartial x) = x"
apply (simp add: makePartial_def)
done

section "Definition of the Isomorphism"

primrec Nat2nat
where 
  Nat2nat_0: "Nat2nat  0'' = 0 " 
  | Nat2nat_suc: "Nat2nat  (suc'(x)) = Suc (Nat2nat x)"

primrec nat2Nat
where
  nat2Nat_0: "nat2Nat 0 = 0''"
| nat2Nat_Suc: "nat2Nat (Suc x) = suc' (nat2Nat x)"

lemma nat2Nat_iso [simp] : "! x . nat2Nat(Nat2nat x) = x"
apply (auto)
apply (induct_tac x)
apply (auto)
done

lemma Nat2nat_iso [simp] : "! x. Nat2nat(nat2Nat x) = x"
apply (auto)
apply (induct_tac x)
apply (auto)
done


lemma nat2Nat_injectivity : "nat2Nat(x) = nat2Nat(y) ==> x = y"
apply (drule_tac f="%x. Nat2nat(x)" in arg_cong)
apply (simp)
done

lemma Nat2nat_injectivity : "Nat2nat(x) = Nat2nat(y) ==>  x = y"
apply (drule_tac f="%x. nat2Nat(x)" in arg_cong)
apply (simp)
done

(* ask Lutz which version to use *)
lemma inj_predefined : "inj Nat2nat"
apply (simp add: inj_on_def)
apply (auto)
apply (drule_tac f="%x. nat2Nat(x)" in arg_cong)
apply (simp)
done

section "Simple Definitions"

(* the numbers need special treatment. we use the following strategy: 1' is manually proved
   for subsequent numbers: apply definition for n' -> suc( [n-1]'), use theorem for [n-1]', ripple out via nat2Nat_Suc *)

(* ============================== 1 ============================== *)

(*by (auto simp add: X1_def_Nat)*)
theorem nat2Nat_1_def_Nat : "1'' = nat2Nat(1)"
apply (simp)
apply (subst X1_def_Nat)
apply (auto)
done

(* get backwards direction via the iso (already in the simplifier) and the other direction *)
theorem Nat2nat_1_def_Nat : "1=Nat2nat(1'')"
apply (simp add: nat2Nat_1_def_Nat)
done

(* ============================== 2 ============================== *)

theorem nat2Nat_2_def_Nat : "2'' = nat2Nat(2)"
apply (subst X2_def_Nat)
apply (subst nat2Nat_1_def_Nat)
apply (subst nat2Nat_Suc [rule_format, THEN sym])
apply (subgoal_tac "Suc 1 = 2")
apply (drule_tac f="%x. nat2Nat(x)" in arg_cong)
apply (auto)
done

theorem two_2  : "2 = Nat2nat(2'')"
apply (simp add: nat2Nat_2_def_Nat)
done

(* ============================== 3 ============================== *)

theorem nat2Nat_3_def_Nat : "3'' = nat2Nat(3)"
apply (subst X3_def_Nat)
apply (subst nat2Nat_2_def_Nat)
apply (subst nat2Nat_Suc [rule_format, THEN sym])
apply (simp)
done

theorem nat2Nat_3_def_nat : "3 = Nat2nat(3'')"
apply (simp add: nat2Nat_3_def_Nat)
done

(* ============================== 4 ============================== *)

theorem nat2Nat_4_def_Nat : "4'' = nat2Nat(4)"
apply (subst X4_def_Nat)
apply (subst nat2Nat_3_def_Nat)
apply (subst nat2Nat_Suc [rule_format, THEN sym])
apply (simp)
done

theorem Nat2nat_4_def_Nat : "4  = Nat2nat(4'')"
apply (simp add: nat2Nat_4_def_Nat)
done

(* ============================== 5 ============================== *)

theorem nat2Nat_5_def_Nat : "5'' = nat2Nat(5)"
apply (subst X5_def_Nat)
apply (subst nat2Nat_4_def_Nat)
apply (subst nat2Nat_Suc [rule_format, THEN sym])
apply (simp)
done

theorem Nat2nat_5_def_Nat : "5  = Nat2nat(5'')"
apply (simp add: nat2Nat_5_def_Nat)
done

(* ============================== 6 ============================== *)

theorem nat2Nat_6_def_Nat : "6'' = nat2Nat(6)"
apply (subst X6_def_Nat)
apply (subst nat2Nat_5_def_Nat)
apply (subst nat2Nat_Suc [rule_format, THEN sym])
apply (simp)
done

theorem Nat2nat_6_def_Nat : "6  = Nat2nat(6'')"
apply (simp add: nat2Nat_6_def_Nat)
done

(* ============================== 7 ============================== *)

theorem nat2Nat_7_def_Nat : "7'' = nat2Nat(7)"
apply (subst X7_def_Nat)
apply (subst nat2Nat_6_def_Nat)
apply (subst nat2Nat_Suc [rule_format, THEN sym])
apply (simp)
done

theorem Nat2nat_7_def_Nat : "7  = Nat2nat(7'')"
apply (simp add: nat2Nat_7_def_Nat)
done

(* ============================== 8 ============================== *)

theorem nat2Nat_8_def_Nat : "8'' = nat2Nat(8)"
apply (subst X8_def_Nat)
apply (subst nat2Nat_7_def_Nat)
apply (subst nat2Nat_Suc [rule_format, THEN sym])
apply (simp)
done

theorem Nat2nat_8_def_Nat : "8  = Nat2nat(8'')"
apply (simp add: nat2Nat_8_def_Nat)
done

(* ============================== 9 ============================== *)

theorem nat2Nat_9_def_Nat : "9'' = nat2Nat(9)"
apply (subst X9_def_Nat)
apply (subst nat2Nat_8_def_Nat)
apply (subst nat2Nat_Suc [rule_format, THEN sym])
apply (simp)
done

theorem Nat2nat_9_def_Nat : "9  = Nat2nat(9'')"
apply (simp add: nat2Nat_9_def_Nat)
done


section "Recursive Definitions"

theorem nat2Nat_add [simp] : "nat2Nat (x + y) = (nat2Nat x) +'' (nat2Nat y)"
apply (induct_tac x)
apply (auto simp only: nat2Nat_Suc nat2Nat_0 add_Suc add_0 add_suc_Nat add_0_Nat)
done

theorem Nat2nat_add : "Nat2nat (x +'' y) = (Nat2nat x) + (Nat2nat y)"
apply (rule nat2Nat_injectivity)
apply (auto)
done

theorem nat2Nat_mul [simp] : "nat2Nat (x * y) = (nat2Nat x) *'' (nat2Nat y)"
apply (induct_tac x)
apply (auto simp only: nat2Nat_Suc nat2Nat_0 nat2Nat_add mult_Suc mult_0 mult_suc_Nat mult_0_Nat)
apply (auto)
done

theorem Nat2nat_mul : "Nat2nat (x *'' y) = (Nat2nat x) * (Nat2nat y)"
apply (rule nat2Nat_injectivity)
apply (auto)
done

theorem nat2Nat_power [simp] : "nat2Nat(x ^ y) = nat2Nat(x) ^'' nat2Nat(y)"
apply (induct_tac y)
apply (auto)
apply (simp add: X1_def_Nat)
done

theorem Nat2nat_power : "Nat2nat(x ^'' y) = Nat2nat(x) ^ Nat2nat(y)"
apply (rule nat2Nat_injectivity)
apply (auto)
done

theorem nat2Nat_fac [simp] : "nat2Nat(fact(x)) = nat2Nat(x)!'"
apply (induct_tac x)
apply (simp add: X1_def_Nat)
apply (subst fact.simps)
apply (simp only: nat2Nat_mul nat2Nat_Suc factorial_suc)
done

theorem Nat2nat_fac : "Nat2nat(x!') = fact(Nat2nat(x))"
apply (rule nat2Nat_injectivity)
apply auto
done

section "Predicates"


subsection "ordering"

lemma no_le_zero [simp] : "(x <='' 0'') = (x = 0'')"
apply (case_tac x)
by (auto)

lemma no_nat2Nat_zero [simp] : "!!x. nat2Nat x = 0'' ==> x = 0"
apply (rule nat2Nat_injectivity)
apply simp
done

theorem nat2Nat_lt_equal [simp] : "x <= y <-> nat2Nat(x) <='' nat2Nat(y)"
apply (rule diff_induct)
apply (auto)
done

theorem Nat2nat_lt_equal : "x <='' y <-> Nat2nat(x) <= Nat2nat(y)"
apply (auto)
done

theorem nat2Nat_lt [simp] : "x < y <-> nat2Nat(x) <'' nat2Nat(y)"
apply (rule diff_induct)
apply (auto)
done

theorem Nat2nat_lt : "x <'' y <-> Nat2nat(x) < Nat2nat(y)"
apply (auto)
done

theorem nat2Nat_gt [simp] : "x > y <-> nat2Nat(x) >'' nat2Nat(y)"
apply (rule diff_induct)
apply (auto)
done

theorem Nat2nat_gt : "x >'' y <-> Nat2nat(x) > Nat2nat(y)"
apply (auto)
done

theorem nat2Nat_gt_equal [simp] : "x >= y <-> nat2Nat(x) >='' nat2Nat(y)"
apply (rule diff_induct)
apply (auto)
done

theorem Nat2nat_gt_equal : "x >='' y <-> Nat2nat(x) >= Nat2nat(y)"
apply(auto)
done

subsection "Even and Odd"

lemma suc_even_nat: "even(x) ==> even(Suc(Suc(x)))"
apply (auto)
done

theorem nat2Nat_even [simp] : "((even''(x) <-> even(Nat2nat(x))) & (odd''(x) <-> odd(Nat2nat(x))))"
apply (induct x)
apply (simp)
apply (rule conjI)
apply (simp only: even_suc_Nat Nat2nat_suc even_nat_Suc suc_even_nat)
apply (subst Nat2nat_suc)
apply (subst even_nat_Suc [rule_format, THEN sym])
apply (auto)
done

theorem Nat2nat_even : "((even(x) <-> even''(nat2Nat(x))) & (odd(x) <-> odd''(nat2Nat(x))))"
apply (auto)
done

theorem nat2Nat_dvd [simp] : "(x dvd y) <-> (nat2Nat(x) dvd' nat2Nat(y))"
apply (subst dvd_def_Nat)
apply (subst dvd_def)
apply (rule iffI)
apply (erule exE)
apply (drule_tac f="%x. nat2Nat(x)" in arg_cong)
apply (force)
apply (erule exE)
apply (drule_tac f="%x. Nat2nat(x)" in arg_cong)
apply (simp (no_asm_use) only: Nat2nat_mul Nat2nat_iso)
apply (auto)
done


theorem Nat2nat_dvd : "(x dvd' y) = (Nat2nat(x) dvd Nat2nat(y))"
apply (auto)
sorry

section "Simple Functions"

theorem nat2Nat_max [simp]: "nat2Nat(max x y) = max''(nat2Nat(x),nat2Nat(y))"
apply (simp add: max_def_Nat max_def)
done

theorem Nat2nat_max : "Nat2nat(max''(x,y)) = (max (Nat2nat(x)) (Nat2nat(y)))"
apply (simp add: max_def_Nat max_def)
done

theorem nat2Nat_min : "nat2Nat(min x y) = min'' (nat2Nat(x), nat2Nat(y))"
apply (simp add: min_def_Nat min_def)
done

theorem Nat2nat_min : "Nat2nat(min''(x,y)) = (min (Nat2nat(x)) (Nat2nat(y)))"
apply (simp add: min_def_Nat min_def)
done


(* ============================================================================= *)
(* ============================== cut off minus ================================ *)
(* ============================================================================= *)


lemma anything_part_minus_zero [simp] : "x -? 0'' = makePartial x"
apply (simp add: sub_def_Nat)
done

lemma add_partiality  : "x=y <-> makePartial x = makePartial y"
apply (simp add: makePartial_def)
done


lemma anything_minus_zero [simp] : "x -! 0'' = x"
(* here the problem is that the defined rewrite rule is only applicable for makePartial x-!y *)
apply (subst add_partiality)
apply (subst subTotal_def2_Nat)
apply (simp)
apply (subst anything_part_minus_zero)
apply (simp)
done

lemma not_greater_zero : "~ x>''0'' <-> x <='' 0''"
apply (simp)
apply (auto)
done



lemma zero_minus_anything [simp] : "0'' -! x = 0''"
apply (case_tac "x>''0''")
apply (simp only: subTotal_def1_Nat)
apply (subst (asm) not_greater_zero)
apply (subst add_partiality)
apply (subst subTotal_def2_Nat)
apply (auto)
done

lemma not_iff : "(A<->B) <-> (~A <-> ~B)"
apply (auto)
done


lemma not_greater_suc : "~ (x>''y) <-> x <'' suc'(y)"
apply (insert Nat2nat_gt)
apply (subst (asm) not_iff)
apply (subst (asm) not_less_eq)
apply (subst (asm) Nat2nat_suc [rule_format, THEN sym])
apply (subst (asm) Nat2nat_lt [rule_format, THEN sym])
apply (auto)
done

lemma not_greater_isa : "~((x::nat) > (y::nat)) <-> x<=y"
apply (arith)
done

lemma minus_Suc : "(Suc(x) - Suc(y))=(x-y)"
apply (auto)
done

lemma not_greater : " ~ (x>''y) <-> x<=''y"
sorry

lemma minus_neutral : "(x <='' y) ==> y = (y -! x) +'' x"
apply (drule subTotal_def2_Nat)
apply (drule sym)
apply (subst (asm) sub_def_Nat)
apply (auto)
done

(*forward reasoning anstatt makePartial einfügen ist hilfreich*)

lemma minus_suc : "(suc'(x) -! suc'(y))=(x-!y)"
apply (case_tac "y>''x")
apply (simp)
apply (subst (asm) not_greater)
apply (subst add_partiality)
apply (subst subTotal_def2_Nat)
apply (simp)
apply (subst sub_def_Nat)
apply (subst ga_comm___XPlus__)
apply (subst add_suc_Nat)
apply (subst ga_injective_suc)
apply (subst ga_comm___XPlus__)
apply (rule minus_neutral)
apply (simp)
done

theorem nat2Nat_minus: "nat2Nat (x - y) = (nat2Nat(x) -! nat2Nat (y))"
apply (rule diff_induct)
apply (simp)
apply (simp only: nat2Nat_0 nat2Nat_Suc diff_0_eq_0 zero_minus_anything)
apply (subst minus_Suc)
apply (simp)
apply (subst minus_suc)
apply (auto)
done

theorem Nat2nat_minus: "Nat2nat (x -! y) = (Nat2nat (x) - Nat2nat(y))"
apply (rule nat2Nat_injectivity)
apply (subst nat2Nat_minus)
apply (auto)
done


section "Partial Functions"

theorem Nat2nat_iso_negated: "~(nat2Nat(x)=nat2Nat(y)) ==> ~(x=y)"
apply (auto)
done

theorem nat2Nat_iso_negated1: "x~=y ==> ~(Nat2nat(x)=Nat2nat(y))"
apply (auto)
apply (drule Nat2nat_injectivity)
apply (auto)
done





section "Non-canonical Mappings"

theorem nat2Nat_at : "nat2Nat(x @@@ y) = nat2Nat(x) @@ nat2Nat(y)"
apply (auto simp add: decimal_def decimal_def_nat)
apply (rule Nat2nat_injectivity)
apply (simp only: Nat2nat_mul Nat2nat_add Nat2nat_9_def_Nat[rule_format, THEN sym])
by (auto)

theorem Nat2nat_at  : "Nat2nat( x @@ y) = Nat2nat(x) @@@ Nat2nat(y)"
apply (simp only: decimal_def decimal_def_nat)
apply (simp only: Nat2nat_mul Nat2nat_suc Nat2nat_add Nat2nat_9_def_Nat[rule_format, THEN sym])
done


theorem Nat2nat_pre : "!!x. x > 0 --> nat2Nat(snd (pre_nat(x))) = snd (pre (nat2Nat(x)))"
apply (case_tac x)
apply (simp)
apply (simp add: makePartial_def)
done

theorem nat2Nat_pre : "!!x. x >'' 0'' --> ( Nat2nat(snd (pre(x)))  = snd(pre_nat (Nat2nat x)))"
apply (case_tac x)
apply (simp)
apply (simp add: makePartial_def)
done

theorem nat2Nat_div [simp] : " y ~= 0 ==> nat2Nat(x div y) = snd(nat2Nat(x) div'' nat2Nat(y))"
apply (rule sym)
apply (rule makepartial_intro_weak)
apply (subst div_Nat)
apply (rule_tac x="nat2Nat (x mod y)" in exI)
apply (rule conjI)
apply (rule Nat2nat_injectivity)
apply (simp only: Nat2nat_iso Nat2nat_add Nat2nat_mul)
apply (arith)
apply (subst nat2Nat_lt[rule_format,THEN sym])
apply (rule mod_less_divisor)
apply (arith)
done

theorem Nat2nat_div [simp] : " y ~= 0'' ==> Nat2nat(snd (x div'' y)) = Nat2nat(x) div Nat2nat(y)"
apply (frule nat2Nat_iso_negated1)
apply (subst (asm) Nat2nat_0)
apply (rule nat2Nat_injectivity)
apply (drule nat2Nat_div)
apply (simp)
done


theorem nat2Nat_mod [simp] : "~(y = 0) ==> nat2Nat(x mod y) =snd (nat2Nat(x) mod'' nat2Nat(y))"
apply (rule sym)
apply (rule makepartial_intro_weak)
(*apply (subst nat2Nat_mod_mp[rule_format,THEN sym])*)
apply (simp)
apply (subst mod_Nat)
apply (rule_tac x="nat2Nat (x div y)" in exI)
apply (rule conjI)
apply (subst nat2Nat_mul[rule_format,THEN sym])
apply (subst nat2Nat_add[rule_format,THEN sym])
apply (rule_tac f="nat2Nat" in arg_cong)
apply (simp)
apply (subst Nat2nat_lt)
apply (simp only: Nat2nat_iso)
apply (rule mod_less_divisor)
apply (auto)
done

theorem Nat2nat_mod : "~(y = 0'') ==>  Nat2nat (snd (x mod'' y)) = (Nat2nat(x) mod Nat2nat(y))"
apply (frule nat2Nat_iso_negated1)
apply (subst (asm) Nat2nat_0)
apply (rule nat2Nat_injectivity)
apply (drule nat2Nat_mod)
apply (simp)
done

theorem nat2Nat_pdiv : "[|~ y = 0 ; x mod y = 0|] ==> nat2Nat(snd(x /?? y)) =snd(nat2Nat(x) /?'' nat2Nat(y))"
apply (rule sym)
apply (rule makepartial_intro_weak)
apply (subst divide_Pos_Nat)
apply (simp)
apply (rule Nat2nat_injectivity)
apply (simp only: Nat2nat_mul Nat2nat_iso)
apply (subst part_div_def)
apply (simp add: makePartialproj)
apply (drule nat2Nat_iso_negated1)
apply (simp only: Nat2nat_0 Nat2nat_iso)
apply (auto)
done


theorem Nat2nat_pdiv : "[|~ y = 0'' ; x mod'' y = makePartial 0''|] ==> Nat2nat(snd(x /?'' y)) =snd(Nat2nat(x) /?? Nat2nat(y))"
apply (drule nat2Nat_iso_negated1)
apply (subst (asm) Nat2nat_0)
apply (drule_tac f="%x. snd(x)" in arg_cong)
apply (drule_tac f="%x. Nat2nat(x)" in arg_cong)
apply (subst (asm) Nat2nat_mod)
apply (simp)
apply (simp  only: makePartialproj Nat2nat_0 Nat2nat_mod)
apply (rule nat2Nat_injectivity)
apply (drule nat2Nat_pdiv)
apply (simp)
apply (simp)
done

theorem nat2Nat_pminus : "(x >= y) ==> nat2Nat(snd (x -?? y)) = snd(nat2Nat(x) -? nat2Nat(y))"
apply (rule sym)
apply (rule makepartial_intro_weak)
apply (subst sub_def_Nat)
apply (rule Nat2nat_injectivity)
apply (simp only: Nat2nat_add Nat2nat_iso)
apply (subst part_minus_def)
apply (simp add: makePartialproj)
done

theorem Nat2nat_pminus : "(x >='' y) ==> Nat2nat(snd(x -? y)) = snd(Nat2nat(x) -?? Nat2nat(y))"
apply (subst (asm) Nat2nat_gt_equal)
apply (rule nat2Nat_injectivity)
apply (subst nat2Nat_pminus)
apply (simp)
apply (simp)
done

(* =============================================================================
    jetzt gehts wirklich los
   ============================================================================= *)

section "Specification of the Isomorphism"

consts int2Int :: "int => X_Int"
consts Int2int :: "X_Int => int"

defs
int2Int_def : "int2Int x == SOME y . EX a b . x = (Abs_Integ (intrel `` {(a,b)})) & y = (nat2Nat a -'' nat2Nat b)"

defs 
(* Int2int_def : "Int2int x == SOME y . EX a b . x = (nat2Nat a -'' nat2Nat b) & y = (Abs_Integ (intrel `` {(a,b)}))" *)
Int2int_def : "Int2int x == SOME y. EX a b . x = a -'' b & y = Abs_Integ (intrel `` {(Nat2nat a, Nat2nat b)})"


section "Int-Isomorphism"

lemma abs_1 [rule_format] : "!! a b . ? y . (Abs_Integ (intrel `` {(a,b)})) = y "
by (auto)

lemma abs_2 [rule_format] : "! x . ? a b . (Abs_Integ (intrel `` {(a,b)})) = x "
apply (auto)
apply (case_tac "0 <= x")
apply (rule_tac x="nat x" in exI)
apply (rule_tac x="0" in exI)
apply (subst int_def[THEN sym])
apply (force)
apply (rule_tac x="0" in exI)
apply (rule_tac x="nat (-x)" in exI)
apply (subst minus[THEN sym])
apply (subst int_def[THEN sym])
by (force)


lemma int_ind [rule_format,simp] : "!! (P :: int => bool) . (!! a b . P(Abs_Integ (intrel `` {(a,b)}))) ==> ! x . P x"
apply (auto)
apply (insert abs_2)
apply (drule_tac x="x" in meta_spec)
apply (elim exE)
by (auto)

axioms Int_ind [rule_format] : "!! (P :: X_Int => bool) . (!! a b . P(a -'' b)) ==> ! x . P x"


theorem int2Int_hil [rule_format,simp] : "!! a b . Int2int (a -'' b) = (Abs_Integ (intrel `` {(Nat2nat a, Nat2nat b)}))"
apply (auto simp add: Int2int_def)
apply (rule someI2_ex)
apply (auto)
apply (subst (asm) equality_Int)
apply (drule_tac f="%x. Nat2nat(x)" in arg_cong)
apply (simp only: Nat2nat_add)
done

theorem Int2int_hil [rule_format,simp] : "!! a b . int2Int (Abs_Integ (intrel `` {(a,b)})) = (nat2Nat a -'' nat2Nat b)"
apply (auto simp add: int2Int_def)
apply (rule someI2_ex)
apply (auto simp add: equality_Int)
apply (rule Nat2nat_injectivity)
apply (simp only: Nat2nat_add Nat2nat_iso)
done


theorem int2Int_iso [rule_format,simp] : "int2Int (Int2int (a)) = a"
apply (rule Int_ind)
by (auto)

theorem Int2int_iso [rule_format,simp] : "!! a . Int2int(int2Int (a)) = a"
apply (rule int_ind)
by (auto)

lemma int2Int_injectivity : "int2Int(x) = int2Int(y) ==> x = y"
apply (drule_tac f="%x. Int2int(x)" in arg_cong)
apply (simp)
done

lemma Int2int_injectivity : "Int2int(x) = Int2int(y) ==>  x = y"
apply (drule_tac f="%x. int2Int(x)" in arg_cong)
apply (simp)
done


theorem Int2int_hil2 : " !! a b .  (Abs_Integ (intrel `` {(a,b)})) = Int2int (nat2Nat a -'' nat2Nat b)"
apply (rule int2Int_injectivity)
apply (subst Int2int_hil)
apply (subst int2Int_iso)
apply (simp)
done

theorem int2Int_hil2 [rule_format,simp] : "!! a b . (a -'' b) = int2Int (Abs_Integ (intrel `` {(Nat2nat a, Nat2nat b)}))"
apply (rule Int2int_injectivity)
apply (subst Int2int_hil)
apply (simp add: nat2Nat_iso)
done


section "Simple Definitions"

(* the numbers need special treatment. we use the following strategy: 1' is manually proved
   for subsequent numbers: apply definition for n' -> suc( [n-1]'), use theorem for [n-1]', ripple out via nat2Nat_Suc *)

(* ============================== 0 ============================== *)


theorem int2Int_0_def : "int2Int(0)=0'"
apply (subst ga_function_monotonicity)
apply (subst Nat2Int_embedding)
apply (subst nat2Nat_0[THEN sym])
apply (subst nat2Nat_0[THEN sym])
apply (subst Int2int_hil[THEN sym])
apply (simp)
done


theorem Int2int_0_def : "Int2int(0')=0"
apply (simp add: int2Int_0_def[THEN sym])
done

(* ============================== 1 ============================== *)

(*by (auto simp add: X1_def_Nat)*)

theorem my_equ: "x = x"
by (auto)

theorem int2Int_1_def : "int2Int(1)=1'"
apply (subst ga_function_monotonicity_1)
apply (subst Nat2Int_embedding)
apply (subst nat2Nat_0[THEN sym])
apply (subst nat2Nat_1_def_Nat)
apply (subst Int2int_hil[THEN sym])
apply (subst One_int_def)
apply (rule my_equ)
done

(* get backwards direction via the iso (already in the simplifier) and the other direction *)
theorem Int2int_1_def_Nat : "Int2int(1')=1"
apply (simp add: int2Int_1_def[THEN sym])
done

(* ============================== 2 ============================== *)

lemma twotoone : "(2::int) = (1::int) + (1:: int)"
apply (auto)
done

lemma Two_int_def : "(2::int) = Abs_Integ (intrel `` {(2::nat, 0::nat)})"
apply (subst twotoone)
apply (subst One_int_def)
apply (subst One_int_def)
apply (subst add)
apply (simp)
done

theorem int2Int_2 : "int2Int(2)=2'"
apply (subst ga_function_monotonicity_4)
apply (subst Nat2Int_embedding)
apply (subst nat2Nat_2_def_Nat)
apply (subst nat2Nat_0[THEN sym])
apply (subst Int2int_hil[THEN sym])
apply (rule Int2int_injectivity)
apply (subst Int2int_iso)
apply (subst Int2int_iso)
apply (subst Two_int_def)
apply (auto)
done


theorem Int2int_2  : "Int2int(2')=2"
apply (simp add: int2Int_2[THEN sym])
done

(* ============================== 3 ============================== *)

lemma threetoone : "(3::int) = (2::int) + (1:: int)"
apply (auto)
done

lemma Three_int_def : "(3::int) = Abs_Integ (intrel `` {(3::nat, 0::nat)})"
apply (subst threetoone)
apply (subst Two_int_def)
apply (subst One_int_def)
apply (subst add)
apply (simp)
done

theorem int2Int_3 : "int2Int(3)= 3'"
apply (subst ga_function_monotonicity_5)
apply (subst Nat2Int_embedding)
apply (subst nat2Nat_3_def_Nat)
apply (subst nat2Nat_0[THEN sym])
apply (subst Int2int_hil[THEN sym])
apply (rule Int2int_injectivity)
apply (subst Int2int_iso)
apply (subst Int2int_iso)
apply (subst Three_int_def)
apply (simp)
done

theorem Int2int_3 : " Int2int(3')=3"
apply (simp add: int2Int_3[THEN sym])
done

(* ============================== 4 ============================== *)

lemma fourtoone : "(4::int) = (3::int) + (1:: int)"
apply (auto)
done

lemma Four_int_def : "(4::int) = Abs_Integ (intrel `` {(4::nat, 0::nat)})"
apply (subst fourtoone)
apply (subst Three_int_def)
apply (subst One_int_def)
apply (subst add)
apply (simp)
done


theorem int2Int_4 : "int2Int(4)= 4'"
apply (subst ga_function_monotonicity_6)
apply (subst Nat2Int_embedding)
apply (subst nat2Nat_4_def_Nat)
apply (subst nat2Nat_0[THEN sym])
apply (subst Int2int_hil[THEN sym])
apply (rule Int2int_injectivity)
apply (subst Int2int_iso)
apply (subst Int2int_iso)
apply (subst Four_int_def)
apply (simp)
done

theorem Int2int_4 : "4  = Int2int(4')"
apply (simp add: int2Int_4[THEN sym])
done

(* ============================== 5 ============================== *)

lemma fivetoone : "(5::int) = (4::int) + (1:: int)"
apply (auto)
done

lemma Five_int_def : "(5::int) = Abs_Integ (intrel `` {(5::nat, 0::nat)})"
apply (subst fivetoone)
apply (subst Four_int_def)
apply (subst One_int_def)
apply (subst add)
apply (simp)
done

theorem int2Int_5 : "int2Int(5)=5'"
apply (subst ga_function_monotonicity_7)
apply (subst Nat2Int_embedding)
apply (subst nat2Nat_5_def_Nat)
apply (subst nat2Nat_0[THEN sym])
apply (subst Int2int_hil[THEN sym])
apply (rule Int2int_injectivity)
apply (subst Int2int_iso)
apply (subst Int2int_iso)
apply (subst Five_int_def)
apply (simp)
done

theorem Int2int_5 : "Int2int(5') = 5"
apply (simp add: int2Int_5[THEN sym])
done

(* ============================== 6 ============================== *)

lemma sixtoone : "(6::int) = (5::int) + (1:: int)"
apply (auto)
done

lemma Six_int_def : "(6::int) = Abs_Integ (intrel `` {(6::nat, 0::nat)})"
apply (subst sixtoone)
apply (subst Five_int_def)
apply (subst One_int_def)
apply (subst add)
apply (simp)
done

theorem int2Int_6 : "int2Int(6) = 6'"
apply (subst ga_function_monotonicity_8)
apply (subst Nat2Int_embedding)
apply (subst nat2Nat_6_def_Nat)
apply (subst nat2Nat_0[THEN sym])
apply (subst Int2int_hil[THEN sym])
apply (rule Int2int_injectivity)
apply (subst Int2int_iso)
apply (subst Int2int_iso)
apply (subst Six_int_def)
apply (simp)
done

theorem Int2int_6 : "Int2int(6')=6"
apply (simp add: int2Int_6[THEN sym])
done

(* ============================== 7 ============================== *)

lemma seventoone : "(7::int) = (6::int) + (1:: int)"
apply (auto)
done

lemma Seven_int_def : "(7::int) = Abs_Integ (intrel `` {(7::nat, 0::nat)})"
apply (subst seventoone)
apply (subst Six_int_def)
apply (subst One_int_def)
apply (subst add)
apply (simp)
done

theorem int2Int_7 : "int2Int(7)=7'"
apply (subst ga_function_monotonicity_9)
apply (subst Nat2Int_embedding)
apply (subst nat2Nat_7_def_Nat)
apply (subst nat2Nat_0[THEN sym])
apply (subst Int2int_hil[THEN sym])
apply (rule Int2int_injectivity)
apply (subst Int2int_iso)
apply (subst Int2int_iso)
apply (subst Seven_int_def)
apply (simp)
done

theorem Int2int_7 : "Int2int(7') = 7"
apply (simp add: int2Int_7[THEN sym])
done

(* ============================== 8 ============================== *)

lemma eighttoone : "(8::int) = (7::int) + (1:: int)"
apply (auto)
done

lemma Eight_int_def : "(8::int) = Abs_Integ (intrel `` {(8::nat, 0::nat)})"
apply (subst eighttoone)
apply (subst Seven_int_def)
apply (subst One_int_def)
apply (subst add)
apply (simp)
done

theorem int2Int_8 : "int2Int(8)=8'"
apply (subst ga_function_monotonicity_10)
apply (subst Nat2Int_embedding)
apply (subst nat2Nat_8_def_Nat)
apply (subst nat2Nat_0[THEN sym])
apply (subst Int2int_hil[THEN sym])
apply (rule Int2int_injectivity)
apply (subst Int2int_iso)
apply (subst Int2int_iso)
apply (subst Eight_int_def)
apply (simp)
done

theorem Int2int_8 : "Int2int(8')=8"
apply (simp add: int2Int_8[THEN sym])
done

(* ============================== 9 ============================== *)

lemma ninetoone : "(9::int) = (8::int) + (1:: int)"
apply (auto)
done

lemma Nine_int_def : "(9::int) = Abs_Integ (intrel `` {(9::nat, 0::nat)})"
apply (subst ninetoone)
apply (subst Eight_int_def)
apply (subst One_int_def)
apply (subst add)
apply (simp)
done

theorem int2Int_9 : "int2Int(9)=9'"
apply (subst ga_function_monotonicity_11)
apply (subst Nat2Int_embedding)
apply (subst nat2Nat_9_def_Nat)
apply (subst nat2Nat_0[THEN sym])
apply (subst Int2int_hil[THEN sym])
apply (rule Int2int_injectivity)
apply (subst Int2int_iso)
apply (subst Int2int_iso)
apply (subst Nine_int_def)
apply (simp)
done

theorem Int2int_9 : "Int2int(9')= 9"
apply (simp add: int2Int_9[THEN sym])
done



(* =============================================================================
   ============================== Simple definitions end =======================
   ============================================================================= *)




theorem int2Int_inj [rule_format] : "!! a b . int2Int a = int2Int b --> a = b"
apply (rule int_ind_bin)
apply (auto simp add: equality_Int)
apply (drule Nat2nat_wd)
by (auto)

theorem Int2int_inj [rule_format] : "!! a b . Int2int a = Int2int b --> a = b"
apply (rule Int_ind_bin)
apply (auto simp add: equality_Int)
apply (rule Nat2nat_inj)
by (auto)

theorem int2Int_inj_2 [rule_format] : "!! a b . a ~= b --> int2Int a ~= int2Int b"
apply (rule int_ind_bin)
apply (auto simp add: equality_Int)
apply (drule Nat2nat_wd)
by (auto)

theorem Int2int_inj_2 [rule_format] : "!! a b . a ~= b --> Int2int a ~= Int2int b"
apply (rule Int_ind_bin)
apply (auto simp add: equality_Int)
apply (drule nat2Nat_inj_2)
by (auto)

theorem int2Int_inj_3 [rule_format] : "!! a b . int2Int a ~= int2Int b --> a ~= b"
apply (rule int_ind_bin)
apply (auto simp add: equality_Int)
apply (drule nat2Nat_inj_2)
by (auto)

theorem Int2int_inj_3 [rule_format] : "!! a b . Int2int a ~= Int2int b --> a ~= b"
apply (rule Int_ind_bin)
apply (auto simp add: equality_Int)
apply (drule Nat2nat_wd)
by (auto)

theorem Int2int_inj_4 [rule_format] : "!! a b . (Int2int a = Int2int b) = (a = b)"
apply (auto)
apply (rule Int2int_inj)
by (blast)

theorem int2Int_wd [rule_format] : "!! a b . a = b --> int2Int a = int2Int b"
apply (rule int_ind_bin)
apply (auto simp add: equality_Int)
apply (rule Nat2nat_inj)
by (auto)

theorem Int2int_wd [rule_format] : "!! a b . a = b --> Int2int a = Int2int b"
apply (rule Int_ind_bin)
apply (auto simp add: equality_Int)
apply (drule Nat2nat_wd)
by (auto)




theorem int2Int_hil [rule_format,simp] : "!! a b . Int2int (a -'' b) = (Abs_Integ (intrel `` {(Nat2nat a, Nat2nat b)}))"
apply (auto simp add: Int2int_def)
apply (rule someI2_ex)
apply (auto)
apply (rule_tac x="Nat2nat a" in exI)
apply (rule_tac x="Nat2nat b" in exI)
apply (auto simp add: equality_Int)
apply (drule_tac f="% x . Nat2nat(x)" in arg_cong)
by (auto)

theorem Int2int_hil [rule_format,simp] : "!! a b . int2Int (Abs_Integ (intrel `` {(a,b)})) = (nat2Nat a -'' nat2Nat b)"
apply (auto simp add: int2Int_def)
apply (rule someI2_ex)
apply (auto simp add: equality_Int)
apply (rule Nat2nat_inj)
by (auto)

axioms Int_ind [rule_format] : "!! (P :: X_Int => bool) . (!! a b . P(a -'' b)) ==> ! x . P x"

lemma converse_P [rule_format] : "!! a b (P :: X_Int => X_Int => bool) . P^--1 a b = P b a"
by (auto)

lemma converse_Pint [rule_format] : "!! a b (P :: int => int => bool) . P^--1 a b = P b a"
by (auto)

lemma Int_ind_bin [rule_format] : "!! (P :: X_Int => X_Int => bool) . ((!! a b c d.  P(a -'' b) (c -'' d) ) ==> ! x y . P x y)"
apply (auto)
apply (rule Int_ind)
apply (subst converse_P[THEN sym])
apply (rule Int_ind)
apply (subst converse_P)
by (auto)

lemma abs_1 [rule_format] : "!! a b . ? y . (Abs_Integ (intrel `` {(a,b)})) = y "
by (auto)

lemma abs_2 [rule_format] : "! x . ? a b . (Abs_Integ (intrel `` {(a,b)})) = x "
apply (auto)
apply (case_tac "0 <= x")
apply (rule_tac x="nat x" in exI)
apply (rule_tac x="0" in exI)
apply (subst int_def[THEN sym])
apply (force)
apply (rule_tac x="0" in exI)
apply (rule_tac x="nat (-x)" in exI)
apply (subst minus[THEN sym])
apply (subst int_def[THEN sym])
by (force)

lemma int_ind [rule_format,simp] : "!! (P :: int => bool) . (!! a b . P(Abs_Integ (intrel `` {(a,b)}))) ==> ! x . P x"
apply (auto)
apply (insert abs_2)
apply (drule_tac x="x" in meta_spec)
apply (elim exE)
by (auto)

lemma int_ind_bin [rule_format] : "!! (P :: int => int => bool) . ((!! a b c d.  P (Abs_Integ (intrel `` {(a,b)})) (Abs_Integ (intrel `` {(c,d)}))) ==> ! x y . P x y)"
apply (auto)
apply (rule int_ind)
apply (subst converse_Pint[THEN sym])
apply (rule int_ind)
by (force)

lemma zero_Int [simp] : "0''' -'' 0''' = 0''"
apply (subst Nat2Int_embedding[THEN sym])
apply (subst ga_function_monotonicity)
by (auto)

lemma zero_Int2int : "Int2int 0'' = 0"
apply (subst zero_Int [THEN sym])
apply (subst int2Int_hil)
by (auto)

lemma zero_int2Int : "int2Int 0 = 0''"
apply (subst Zero_int_def)
apply (subst Int2int_hil)
by (auto)


section "Addition"

theorem int_add_1 [rule_format, simp] : "!! a b . int2Int (a + b) = int2Int a +' int2Int b"
apply (rule int_ind_bin)
apply (rule Int2int_inj)
apply (auto simp only: equality_Int)
by (auto simp add: add)

theorem int_add_2 [rule_format, simp] : "!! a b . Int2int (a +' b) = Int2int a + Int2int b"
apply (rule Int_ind_bin)
by (auto simp add: add)

section "Subtraction"

theorem int_u_minus_1 [rule_format, simp] : "!! a . int2Int (-a) = -' int2Int a"
apply (rule int_ind)
apply (rule Int2int_inj)
by (auto simp add: minus)

theorem int_u_minus_2 [rule_format, simp] : "!! a . Int2int (-' a) = - Int2int(a)"
apply (rule Int_ind)
by (auto simp add:minus)

lemma minus_int_lem [rule_format] : "!! a (b ::int) . a - b = a + - b"
by (auto)

theorem int_b_minus_1 [rule_format, simp] : "!! a b . int2Int (a - b) = int2Int a -' int2Int b"
apply (rule int_ind_bin)
apply (rule Int2int_inj)
by (force simp add: equality_Int minus_int_lem minus add)

theorem int_b_minus_2 [rule_format, simp] : "!! a b . Int2int ( a -' b) = Int2int a - Int2int b"
apply (rule Int_ind_bin)
by (force simp add: equality_Int minus_int_lem minus add)

section "Neutral Elements"

theorem int_zero_1 [rule_format, simp] : "Int2int 0'' = 0"
apply (subst zero_Int [THEN sym])
apply (subst int2Int_hil)
by (auto)

theorem int_zero_2 [rule_format,simp] : "int2Int 0 = 0''"
apply (rule Int2int_inj)
by (auto)

lemma one_int2Int [rule_format] : "int2Int 1 = 1'"
apply (auto simp add: One_int_def)
apply (subst ga_function_monotonicity_21[THEN sym])
apply (subst ga_function_monotonicity[THEN sym])
apply (subst X1_def_Nat[THEN sym])
apply (subst ga_function_monotonicity_1[THEN sym])
apply (auto)
apply (rule Int2int_inj)
by (auto)

lemma one_Int2int [rule_format, simp] : "Int2int 1' = 1"
apply (subst one_int2Int[THEN sym])
by (auto)

section "Multiplication"

theorem int_mult_1 [rule_format, simp] : "!! a b . int2Int (a * b) = int2Int a *' int2Int b"
apply (rule int_ind_bin)
apply (rule Int2int_inj)
by (auto simp add: mult)

theorem int_mult_2 [rule_format, simp] : "!! a b . Int2int (a *' b) = Int2int a * Int2int b"
apply (rule Int_ind_bin)
by (auto simp add: mult)

section "Order"

lemma add_neutral [rule_format, simp] : "! a . 0'' +' a = a"
apply (auto)
apply (rule Int2int_inj)
by (auto)

lemma zero_is_minus_zero [rule_format, simp] : "-' 0'' = 0''"
apply (rule Int2int_inj)
by (auto)

lemma defOp_lt [rule_format] : "!! a . defOp (gn_proj_Int_Nat(a)) = (0'' <=' a)"
apply (rule Int_ind)
by (auto simp add: leq_def_Int)

lemma less_int_lemma_1 [rule_format] : "!! a (b :: int) . (a <= b) = (0 <= b - a)"
by (auto)

lemma le_nat_lemma_1 [rule_format]:"!! a b . defOp (gn_proj_Int_Nat (a -'' b)) = (b <='' a)"
apply (auto)
apply (subst (asm)ga_function_monotonicity_21[THEN sym])
apply (subst (asm) leq_def_Int[THEN sym])
apply (subst (asm) ga_predicate_monotonicity_1)
apply (force)
apply (subst ga_function_monotonicity_21[THEN sym])
apply (subst leq_def_Int[THEN sym])
apply (subst ga_predicate_monotonicity_1)
by (force)

theorem Int_order1 [rule_format] : "!! a b . (a <= b) --> (int2Int a <=' int2Int b)"
apply (rule int_ind_bin)
apply (auto simp add: equality_Int leq_def_Int)
apply (subst add_def_Int[THEN sym])
apply (subst neg_def_Int[THEN sym])
apply (subst ga_comm___XPlus___1)
apply (subst sub_def_Int[THEN sym])
apply (auto simp add: le_int_def)
apply (auto simp add: le_nat_lemma_1)
apply (subst add1[rule_format,THEN sym])
apply (subst add1[rule_format,THEN sym])
apply (rule order1[rule_format])
by (auto)

lemma less_le_lemma [rule_format] : "!! a b . a < b --> (a <= b & a ~= b)"
apply (auto)
apply (arith)
by (arith)

theorem Int_order2 [rule_format] : "!! a b . (a < b) --> (int2Int a <' int2Int b)"
apply (auto simp add: less_def_Int del: leq_def_Int)
apply (drule less_le_lemma)
apply (clarify)
apply (drule Int_order1)
apply (force)
apply (drule less_le_lemma)
apply (clarify)
apply (drule int2Int_inj)
by (force)

theorem Int_order3 [rule_format] : "!! a b . (a >= b) --> (int2Int a >=' int2Int b)"
apply (auto simp add: geq_def_Int del: leq_def_Int)
apply (drule Int_order1)
by (force)

theorem Int_order4 [rule_format] : "!! a b . (a > b) --> (int2Int a >' int2Int b)"
apply (auto simp add: greater_def_Int del: leq_def_Int)
apply (drule less_le_lemma)
apply (clarify)
apply (drule Int_order1)
apply (drule int2Int_inj_2)
apply (subst less_def_Int)
by (auto)

theorem Int_order5 [rule_format] : "!! a b . (a <=' b) --> (Int2int a <= Int2int b)"
apply (rule Int_ind_bin)
apply (auto simp add: equality_Int leq_def_Int)
apply (subst (asm) add_def_Int[THEN sym])
apply (subst (asm) neg_def_Int[THEN sym])
apply (subst (asm) ga_comm___XPlus___1)
apply (subst (asm) sub_def_Int[THEN sym])
apply (auto simp add: le_nat_lemma_1)
apply (drule order3[rule_format])
by (auto simp add: le)

theorem Int_order6 [rule_format] : "!! a b . (a <' b) --> (Int2int a < Int2int b)"
apply (auto simp add: less_def_Int leq_def_Int)
apply (subst (asm) sub_def_Int[THEN sym])
apply (subst (asm) leq_def_Int[THEN sym])
apply (drule Int_order5)
apply (drule Int2int_inj_2)
by (force)

theorem Int_order7 [rule_format] : "!! a b . (a >=' b) --> (Int2int a >= Int2int b)"
apply (auto simp add: geq_def_Int leq_def_Int)
apply (subst (asm) sub_def_Int[THEN sym])
apply (subst (asm) leq_def_Int[THEN sym])
apply (drule Int_order5)
by (force)

theorem Int_order8 [rule_format] : "!! a b . (a >' b) --> (Int2int a > Int2int b)"
apply (auto simp add: greater_def_Int)
apply (drule Int_order6)
by(force)

section "Sign/Abs"

lemma smaller_greater_lemma_1 [rule_format] : "!! a . (a <=' 0'') = (-' a >=' 0'')"
by (auto simp add: geq_def_Int leq_def_Int)

lemma smaller_greater_lemma_2 [rule_format] : "!! a . (0'' <=' -' a ) = (a <=' 0'')"
by (auto simp add: leq_def_Int)

lemma def_lemma_1 [rule_format] : "!! a . defOp(gn_proj_Int_Nat(a)) = (0'' <=' a)"
apply (auto simp add: leq_def_Int)
by (auto simp add: ga_function_monotonicity)

lemma def_lemma_2 [rule_format] : "!! a . (a <' 0'') --> ~ defOp(gn_proj_Int_Nat(a))"
apply (auto simp add: less_def_Int leq_def_Int)
apply (subst (asm) def_lemma_1)+
apply (subst (asm) smaller_greater_lemma_2)
apply (drule Int_order5)+
apply (drule Int2int_inj_2)
apply (subst (asm) zero_Int2int)+
by (force)

lemma tf_lemma : "!! a . (~a ==> False) ==> (a ==> True)"
by (auto)

consts sign_int :: "int => int"
defs sign_int_def : "sign_int(a) == if a = 0 then 0 else if a > 0 then 1 else -1"

theorem int_abs_1 [rule_format, simp] : "!! a . int2Int(abs(a)) = gn_inj_Nat_Int(abs'(int2Int(a)))"
apply (auto simp only: abs_def_Int zabs_def)
apply (split split_if)
apply (rule conjI)
apply (auto simp add: ga_function_monotonicity[THEN sym])
apply (drule Int_order6)
apply (force)
apply (rule Int2int_inj)
apply (auto)
apply (erule notE)
apply (subst zero_int2Int[THEN sym])
apply (rule Int_order2)
by (force)

theorem int_abs_2 [rule_format, simp] : "!! a . Int2int(gn_inj_Nat_Int(abs'(a))) = abs(Int2int(a))"
apply (auto simp only: abs_def_Int zabs_def)
apply (split split_if)
apply (rule conjI)
apply (auto simp only: ga_function_monotonicity[THEN sym])
apply (split split_if)
apply (rule conjI)
apply (clarify)
apply (drule Int_order6)
apply (force)
apply (clarify)
apply (erule notE)
apply (drule Int_order2)
apply (force)
apply (split split_if)
apply (rule conjI)
apply (clarify)
apply (drule Int_order6)
apply (force)
by (blast)

theorem int_sign_1 [rule_format, simp] : "!! a . int2Int(sign_int(a)) = sign(int2Int(a))"
apply (auto simp add: ga_function_monotonicity[THEN sym] greater_def_Int)
apply (subst (asm) less_def_Int)
apply (force)
apply (auto simp add: ga_function_monotonicity_2[THEN sym])
apply (subst sign_int_def)
apply (split split_if)
apply (rule conjI)
apply (clarify)
apply (subst (asm) zero_int2Int)+
apply (force)
apply (clarify)
apply (split split_if)
apply (rule conjI)
apply (clarify)
apply (subst one_int2Int[THEN sym])
apply (clarify)+
apply (drule Int_order6)
apply (simp)
apply (subst sign_int_def)
apply (split split_if)
apply (rule conjI)
apply (clarify)+
apply (split split_if)
apply (rule conjI)
apply (clarify)
apply (subst (asm) int_zero_2[THEN sym])+
apply (drule int2Int_inj)
apply (clarify)+
apply (subst (asm) int_zero_2[THEN sym])+
apply (drule int2Int_inj)
apply (clarify)+
apply (subst sign_int_def)
apply (split split_if)
apply (rule conjI)
apply (clarify)+
apply (subst (asm) int_zero_2[THEN sym])+
apply (clarify)
apply (split split_if)
apply (rule conjI)
apply (clarify)+
apply (drule Int_order2)
apply (simp)
apply (clarify)
apply (rule Int2int_inj)
by (simp)

theorem int_sign_2 [rule_format, simp] : "!! a . Int2int(sign(a)) = sign_int(Int2int(a))"
apply (subst sign_int_def)
apply (subst sign_def_Int)
apply (split split_if, rule conjI, clarify)+
apply (subst (asm) ga_function_monotonicity[THEN sym])+
apply (subst ga_function_monotonicity_2[THEN sym])
apply (drule Int2int_inj_2)
apply (subst (asm) zero_Int2int)
apply (clarify)+
apply (subst (asm) ga_function_monotonicity[THEN sym])+
apply (subst ga_function_monotonicity_2[THEN sym])
apply (drule Int2int_inj_2)
apply (subst (asm) zero_Int2int)
apply (clarify)+
apply (subst ga_function_monotonicity[THEN sym])+
apply (subst ga_function_monotonicity_2[THEN sym])+
apply (split split_if, rule conjI, clarify)+
apply (subst (asm) zero_Int2int)
apply (clarify)+
apply (split split_if, rule conjI, clarify)+
apply (rule int2Int_inj)
apply (subst one_Int2int)
apply (clarify)+
apply (drule Int2int_inj_2)
apply (subst (asm) zero_Int2int)
apply (erule notE)
apply (drule Int_order2)
apply (simp)
apply (erule notE)
apply (subst (asm) greater_def_Int[THEN sym])
apply (force)
apply (split split_if, rule conjI, clarify)+
apply (subst (asm) zero_Int2int)
apply (force)
apply (clarify)
apply (split split_if, rule conjI, clarify)+
apply (erule notE)+
apply (drule Int_order8)
apply (simp)
apply (clarify)
apply (rule int2Int_inj)
by (simp)

theorem Int_order1b [rule_format] : "!! a b . (int2Int a <=' int2Int b) --> (a <= b)"
apply (clarify)
apply (drule Int_order5)
by (auto)

theorem Int_order2b [rule_format] : "!! a b . (int2Int a <' int2Int b) --> (a < b)"
apply (clarify)
apply (drule Int_order6)
by (auto)

theorem Int_order3b [rule_format] : "!! a b . (int2Int a >=' int2Int b) --> (a >= b)"
apply (clarify)
apply (drule Int_order7)
by (auto)

theorem Int_order4b [rule_format] : "!! a b . (int2Int a >' int2Int b) --> (a > b)"
apply (clarify)
apply (drule Int_order8)
by (auto)

theorem Int_order5b [rule_format] : "!! a b . (Int2int a <= Int2int b) --> (a <=' b)"
apply (clarify)
apply (drule Int_order1)
by (auto)

theorem Int_order6b [rule_format] : "!! a b . (Int2int a < Int2int b) --> (a <' b)"
apply (clarify)
apply (drule Int_order2)
by (auto)

theorem Int_order7b [rule_format] : "!! a b . (Int2int a >= Int2int b) --> (a >=' b)"
apply (clarify)
apply (drule Int_order3)
by (auto)

theorem Int_order8b [rule_format] : "!! a b . (Int2int a > Int2int b) --> (a >' b)"
apply (clarify)
apply (drule Int_order4)
by (auto)

section "Exponentiation"

lemma Int_minus_one_lemma [rule_format] : "(int2Int ((- 1)::int)) = (-' 1')"
apply (rule Int2int_inj)
by (auto)

lemma Int_power_1 [rule_format] : "!! a . ev_nat a --> (-1::int) ^ a = 1"
apply (auto simp only: ev_nat_def)
apply (induct_tac q)
by (auto)

lemma mod_lemma_1 [rule_format] : "!! a . 0 < a mod (2::nat) --> a mod 2 = 1" 
by (auto)

lemma Int_power_2 [rule_format] : "!! (b::int) . b = b ^ 1"
by (auto)

lemma Int_power_3 [rule_format] : "!! a (b::int) . a~= 0 --> b ^ a = (b ^ ( a - 1)) * b"
apply (auto)
apply (subst (6) Int_power_2)
apply (subst zpower_zadd_distrib[THEN sym])
by (auto)

lemma Int_power_4 [rule_format] : "!! a . ~ev_nat a --> (-1::int) ^ a = -1"
apply (auto simp only: ev_nat_def)
apply (drule mod_lemma_1)
apply (auto)
apply (subst Int_power_3)
apply (clarify)
apply (force)
apply (subst Int_power_1)
apply (auto simp only: ev_nat_def)
by (auto simp add: mod_nat)

lemma Int_power_5 [rule_format] : "!! a b . a ^ b = sign_int(a)^ b * abs(a) ^ b"
apply (auto simp only: sign_int_def)
apply (split split_if)
apply (rule conjI)
apply (clarify)
apply (simp)
apply (case_tac "b=0")
apply (simp)
apply (simp)
apply (clarify)
apply (split split_if)
apply (rule conjI)
apply (clarify)
apply (force)
apply (clarify)
apply (subst zabs_def)
apply (split split_if)
apply (rule conjI)
apply (clarify)
prefer 2
apply (clarify)
apply (simp)
apply (induct_tac b)
by (auto)

lemma coeff [rule_format] : "!! (a::int) b c d . (a = c & b = d) --> a * b = c * d"
by (auto)

theorem Int_exp_1 [rule_format, simp] : "!! a b . ((int2Int a) ^' (nat2Nat b)) = int2Int(a ^ b)"
apply (case_tac "a = ((- 1)::int)")
apply (simp)
apply (clarify)
apply (subst Int_minus_one_lemma[simplified])
apply (subst ga_function_monotonicity_2)
apply (subst power_neg1_Int)
apply (split split_if)
apply (rule conjI)
apply (subst ga_function_monotonicity_2[THEN sym])
apply (clarify)
apply (subst Int_power_1)
apply (force)+
apply (subst one_int2Int[THEN sym])
apply (clarify)
apply (clarify)
apply (subst ga_function_monotonicity_2[THEN sym])
apply (subst Int_power_4)
apply (force)
apply (rule Int2int_inj)
apply (force)
apply (subst power_others_Int)
apply (auto simp only: ga_function_monotonicity_2[THEN sym])
apply (drule Int2int_wd)
apply (force)
apply (rule Int2int_inj)
apply (subst int_mult_2)
apply (subst iso_2)
apply (subst Int_power_5)
apply (rule coeff)
apply (rule conjI)
apply (case_tac "0 <= a")
apply (case_tac "0 = a")
apply (clarify)
apply (subst int_sign_1[THEN sym])
apply (subst sign_int_def)+
apply (simp)
apply (subst ga_function_monotonicity)
apply (subst ga_function_monotonicity_23)
apply (induct_tac b)
apply (simp)
apply (subst ga_function_monotonicity_1[THEN sym])
apply (simp)
apply (simp)
apply (subst ga_function_monotonicity[THEN sym])
apply (simp)
apply (subst int_sign_1[THEN sym])
apply (subst sign_int_def)+
apply (simp)
apply (subst one_int2Int)
apply (subst ga_function_monotonicity_1)
apply (subst ga_function_monotonicity_23)
apply (induct_tac b)
apply (simp)
apply (subst ga_function_monotonicity_1[THEN sym])
apply (simp)
apply (simp)
apply (subst int_sign_1[THEN sym])
apply (subst sign_int_def)+
apply (simp)
apply (case_tac "ev_nat(b)")
apply (subst Int_minus_one_lemma[simplified])
apply (subst ga_function_monotonicity_2)
apply (subst power_neg1_Int)
apply (split split_if)
apply (rule conjI)
prefer 2
apply (simp)
apply (clarify)
apply (subst ga_function_monotonicity_2[THEN sym])
apply (subst Int_power_1)
apply (simp)
apply (simp)
apply (subst Int_minus_one_lemma[simplified])
apply (subst ga_function_monotonicity_2)
apply (subst power_neg1_Int)
apply (split split_if)
apply (rule conjI)
apply (clarify)
apply (simp)
apply (clarify)
apply (subst ga_function_monotonicity_2[THEN sym])
apply (subst Int_power_4)
apply (simp)
apply (simp)
apply (auto)
apply (induct_tac b)
apply (simp)
apply (subst ga_function_monotonicity_1[THEN sym])
apply (auto)
apply (subst ga_function_monotonicity_12[THEN sym])
apply (subst int_mult_2)
apply (subst int_abs_1[THEN sym])
apply (subst iso_2)
by (auto)

theorem Int_exp_2 [rule_format, simp] : "!! a b . ((Int2int a) ^ (Nat2nat b)) = Int2int(a ^' b)"
apply (rule int2Int_inj)
apply (subst Int_exp_1[THEN sym])
by (simp)

section "int additions"

consts ev_int :: "int => bool"
consts od_int :: "int => bool"

defs
ev_int_def: "ev_int x == ev_nat(nat (abs(x)))"
od_int_def: "od_int x == od_nat(nat (abs(x)))"

section "Injection"

theorem Int_inj_1 [rule_format] : "!! a . Int2int(gn_inj_Nat_Int(a)) = int(Nat2nat(a))"
apply (induct_tac a)
apply (subst ga_function_monotonicity[THEN sym])
apply (simp)
apply (auto)
apply (subst suc[rule_format, THEN sym])
apply (subst ga_function_monotonicity_15[THEN sym])
apply (subst ga_function_monotonicity_1[THEN sym])
apply (subst ga_comm___XPlus___1)
by (simp)

theorem Int_inj_2 [rule_format] : "!! a . int2Int(int a) = gn_inj_Nat_Int(nat2Nat(a))"
apply (induct_tac a)
apply (auto simp add: ga_function_monotonicity[THEN sym])
apply (subst suc[rule_format, THEN sym])
apply (subst ga_comm___XPlus__)
apply (subst ga_function_monotonicity_15[THEN sym])
apply (subst ga_function_monotonicity_1[THEN sym])
apply (subst one_int2Int)
by (auto)

section "Division"

lemma Int_mod_lemma_1 [rule_format] : "!! a (b::int) . a * b mod b = 0"
by (auto)

lemma Int_add_zero [rule_format] : "!! (a::int) . a + 0 = a"
by (auto)

lemma le_Nat_lemma [rule_format] : "!! a b . [|a <='' b; a ~= b |] ==> a <'' b"
by (auto)

lemma zero_nat_inj_1 [rule_format] : "!! (a::nat) . 0 <= int a"
by (auto)

lemma Int_order_lem_6 [rule_format] : "!! a b . (a <' b) = (Int2int a < Int2int b)"
apply (auto)
apply (drule Int_order6)
apply (blast)
apply (rule Int_order6b)
by (blast)

lemma Int_order_lem_5 [rule_format] : "!! a b . (a <=' b) = (Int2int a <= Int2int b)"
apply (auto)
apply (drule Int_order5)
apply (blast)
apply (rule Int_order5b)
by (blast)

lemma Int_lt_2_le [rule_format] : "!! a b . ~ (a <' b) --> b <=' a"
apply (auto)
apply (subst (asm) Int_order_lem_6)
apply (rule Int_order5b)
by (auto)

lemma Int_le_2_le [rule_format] : "!! a b . ~ (a <=' b) --> b <' a"
apply (auto)
apply (subst (asm) Int_order_lem_5)
apply (rule Int_order6b)
by (auto)

lemma mod_lemma_1 [rule_format] : "!! (a::int) b . (a < 0 & b < 0) --> (a mod b <= 0)"
by (auto)

lemma mod_lemma_2 [rule_format] : "!! (a::int) b . (a >= 0 & b < 0) --> (a mod b <=0)"
by (auto)

lemma mod_lemma_3 [rule_format] : "!! (a::int) b . (a < 0 & b > 0) --> (a mod b >= 0)"
by (auto)

lemma mod_lemma_4 [rule_format] : "!! (a::int) b . (a >= 0 & b > 0) --> (a mod b >= 0)"
by (auto)

lemma mod_lemma_5 [rule_format] : "!! (a::int) b . b < 0 --> (a mod b <= 0)"
by (auto)

lemma mod_lemma_6 [rule_format] : "!! (a::int) b . b > 0 --> (a mod b >= 0)"
by (auto)

lemma int_nat_less_lemma [rule_format] : "!! (a::nat) b . a < b --> int a < int b"
by(auto)

lemma nat_imp_gt_zero [rule_format] : "!! (a:: nat) b c . int (a) = b * c --> b * c >= 0"
by (auto)

lemma gn_inj_Int_Nat_neq [rule_format] : "!! (a::Nat) b . a ~= b --> gn_inj_Nat_Int(a) ~= gn_inj_Nat_Int(b)"
apply (auto)
apply (drule ga_embedding_injectivity)
by (force)

lemma gn_inj_Int_Nat_Neq_2 [rule_format] : "!! (a::Nat) b . gn_inj_Nat_Int(a) ~= gn_inj_Nat_Int(b) --> a ~= b"
by (auto)

lemma fact_lemma_1 [rule_format] : "!! a b c d . a +' (b *' c) = b *' d --> (? n . a = b *' n)"
apply (clarify)
apply (rule_tac x="d -' c" in exI)
apply (rule Int2int_inj)
apply (drule Int2int_wd)
by (simp add: int_distrib)

lemma int_lt_le_lemma_1 [rule_format] : "!! a (b::int) . [| a <= b; a~= b |] ==> a < b"
by (auto)

lemma int_minus_one [rule_format] : "!! (b::int) . - b = b * (-1)"
by (auto)

lemma int_one [rule_format] : "!! (b::int) . b = b * 1"
by (auto)

lemma int_order_trans_1 [rule_format] : "!! (a::int) b c d . [|a <= b *c; b*c < d|] ==> a < d"
by (auto)

lemma int_order_trans_2 [rule_format] : "!! (a::int) b c d . [|a <= b *c; b*c <= d|] ==> a <= d"
by (auto)

lemma int_cancel_1 [rule_format] : "!! (b :: int) n . (b < 0) --> (((b * n) < - b) = (n > -1))"
thm mult_less_cancel_left
apply (auto)
apply (subst (asm) int_minus_one)
apply (subst (asm) mult_less_cancel_left)
apply (auto)
apply (subst int_minus_one)
apply (subst mult_less_cancel_left)
by (auto)

lemma int_cancel_2 [rule_format] : "!! (b :: int) n . (0 < b) --> (((b * n) <= b) = (n <= 1))"
apply (auto)
apply (subst (asm) (6) int_one)
apply (subst (asm) mult_le_cancel_left)
apply (auto)
apply (subst (4) int_one)
apply (subst mult_le_cancel_left)
by (auto)

lemma int_mult_zero [rule_format] : "!! (b::int) . 0 * b = 0"
by (auto)

lemma int_mult_zero_l [rule_format] : "!! (a::int) . a * 0 = 0"
by (auto)

lemma int_mult_lemma_1 [rule_format] :" !! (a::int) b . 0 <= a & 0 <= b --> 0 <= a * b"
apply (clarify)
apply (subst int_mult_zero [THEN sym, where b1="b"])
apply (subst mult_le_cancel_right)
by (auto)

lemma int_mult_lemma_2 [rule_format] :" !! (a::int) b . 0 >= a & 0 >= b --> 0 <= a * b"
apply (clarify)
apply (subst int_mult_zero [THEN sym, where b1="b"])
apply (subst mult_le_cancel_right)
by (auto)

lemma int_mult_lemma_3 [rule_format] : "!! a (b::int) . 0 <= a * b --> (a <= 0 & b <= 0) | (a >= 0 & b >= 0)"
apply (auto)
apply (subst (asm) int_mult_zero_l [THEN sym, where a1="a"])
apply (subst (asm) mult_le_cancel_left)
apply (auto)
apply (subst (asm) int_mult_zero [THEN sym, where b1="b"])
apply (subst (asm) mult_le_cancel_right)
by (auto)

lemma the_lemma [rule_format] : "!! f a .  (! z . a = Some z& f z) ==> f(the a)"
by (auto)

lemma nat_pos [rule_format] : "!! a b . b < 0 & a > b --> int(nat(a - b)) = a - b"
by (arith)

lemma nat_pos_2 [rule_format] : "!! a b . 0 <= a --> int(nat(a)) = a"
by (arith)

lemma b_pos [rule_format] : "!! (b::int) . [| ~ b < 0; b ~= 0|] ==> 0 < b"
by (auto)

lemma zero_less_int [rule_format] : "!! a b . a <='' b --> 0'' <=' b -'' a"
apply (rule diff_induct_Nat)
apply (auto)
apply (rule Int_order5b)
apply (simp)
apply (subst Zero_int_def)
apply (subst le)
apply (auto)
apply (rule Int_order5b)
apply (simp)
apply (drule Int_order5)
apply (simp)
apply (subst Zero_int_def)
apply (subst le)
apply (subst (asm) Zero_int_def)
apply (subst (asm) le)
by (simp)

lemma negation_lemma_1 [rule_format] : "!! b . ~ (b <' 0'') --> 0'' <=' b"
apply (rule Int_ind)
apply (auto)
apply (case_tac "ba <='' a")
apply (drule zero_less_int)
apply (simp)
apply (rule zero_less_int)
apply (erule notE)
sorry

theorem Int_mod_1 [rule_format, simp] : "!! a b z . 
if (b < 0 & a mod b ~= 0) then 
  (Some (int2Int ((a mod b) - b)) = 
    (option_map X_gn_inj_Nat_Int ((int2Int a) mod' (int2Int b))))
else if (0 ~= b) then
    (Some (int2Int ((a mod b))) = 
      (option_map X_gn_inj_Nat_Int ((int2Int a) mod' (int2Int b))))
else
  ~ (defOp(int2Int a mod' int2Int b))
"
apply (split split_if)
apply (rule conjI)
apply (clarify)
apply (rule sym)
apply (subst option_map_eq_Some)
apply (rule_tac x="nat2Nat (nat(a mod b-b))" in exI)
apply (rule conjI)
prefer 2
apply (subst Int_inj_2[THEN sym])
apply (rule Int2int_inj)
apply (subst nat_pos)
apply (simp)
apply (simp)
apply (simp)
apply (rule conjI)
apply (rule_tac x="int2Int(a div b + 1)" in exI)
apply (subst Int_inj_2[THEN sym])
apply (subst nat_pos)
apply (rule conjI)
apply (simp)
apply (drule_tac a="a" in neg_mod_conj)
apply (simp)
apply (rule Int2int_inj)
apply (simp)
apply (subst zadd_zmult_distrib2)
apply (simp)
apply (subst ga_predicate_monotonicity_1[THEN sym])
apply (rule conjI)
apply (rule Int_order5b)
apply (subst Int_inj_1)
apply (subst int_abs_1[THEN sym])
apply (subst Nat2nat_iso)
apply (subst iso_2)
apply (subst nat_pos)
apply (rule conjI)
apply (blast)
apply (frule_tac a="a" in neg_mod_conj)
apply (simp)
apply (simp)
apply (rule gn_inj_Int_Nat_Neq_2)
apply (rule Int2int_inj_3)
apply (subst abs_def_Int)
apply (subst ga_function_monotonicity[THEN sym])
apply (split split_if)
apply (rule conjI)
apply (clarify)
apply (drule Int_order6)
apply (subst (asm) Int_inj_1)
apply (subst (asm) Nat2nat_iso)
apply (subst (asm) int_u_minus_1[THEN sym])
apply (subst (asm) iso_2)+
apply (subst (asm) int_zero_1)
apply (subst (asm) nat_pos)
apply (rule conjI)
apply (blast)
apply (drule_tac a="a" in neg_mod_conj)
apply (blast)
apply (drule_tac f="% x . x + b" in arg_cong)
apply (simp)
apply (clarify)
apply (erule notE)
apply (erule notE)
apply (subst (asm) Int_inj_1)
apply (subst (asm) Nat2nat_iso)
apply (subst (asm) iso_2)+
apply (subst (asm) nat_pos)
apply (rule conjI)
apply (blast)
apply (drule_tac a="a" in neg_mod_conj)
apply (blast)
apply (drule_tac f="% x . x + b" in arg_cong)
apply (simp)
apply (drule_tac a="a" in neg_mod_conj)
apply (simp)
apply (split split_if)
apply (rule conjI)
apply (clarify)
apply (subst (asm) de_Morgan_conj)
apply (auto)
apply (rule sym)
apply (subst option_map_eq_Some)
apply (rule_tac x="nat2Nat (nat(a mod b))" in exI)
apply (rule conjI)
prefer 2
apply (rule Int2int_inj)
apply (subst Int_inj_1)
apply (subst Nat2nat_iso)
apply (subst iso_2)
apply (rule nat_pos_2)
apply (drule b_pos)
apply (blast)+
apply (drule_tac a="a" in pos_mod_conj)
apply (blast)
apply (drule b_pos)
apply (blast)
apply (simp)
apply (rule conjI)
apply (rule_tac x="int2Int (a div b)" in exI)
apply (rule Int2int_inj)
apply (simp)
apply (subst Int_inj_1)
apply (subst Nat2nat_iso)
apply (subst nat_pos_2)
apply (frule_tac a="a" in pos_mod_conj)
apply (blast)
apply (simp)
apply (rule conjI)
apply (subst ga_predicate_monotonicity_1[THEN sym])
apply (rule Int_order5b)
apply (subst abs_def_Int)
apply (subst Int_inj_1)
apply (subst Nat2nat_iso)
apply (subst nat_pos_2)
apply (drule_tac a="a" in pos_mod_conj)
apply (blast)+
apply (frule_tac a="a" in pos_mod_conj)
apply (split split_if)
apply (rule conjI)
apply (clarify)
apply (subst int_u_minus_1[THEN sym])
apply (subst (asm) ga_function_monotonicity[THEN sym])
apply (drule Int_order6)
apply (subst (asm) int_zero_1)
apply (subst (asm) iso_2)
apply (subst iso_2)
apply (force)
apply (clarify)
apply (subst (asm) ga_function_monotonicity[THEN sym])
apply (subst iso_2)
apply (frule_tac a="a" in pos_mod_conj)
apply (simp)
apply (rule gn_inj_Int_Nat_Neq_2)
apply (subst abs_def_Int)
apply (subst ga_function_monotonicity[THEN sym])
apply (rule Int2int_inj_3)
apply (subst Int_inj_1)
apply (subst Nat2nat_iso)
apply (subst nat_pos_2)
apply (frule_tac a="a" in pos_mod_conj)
apply (blast)
apply (split split_if)
apply (rule conjI)
apply (clarify)
apply (drule Int_order6)
apply (subst (asm) int_u_minus_1[THEN sym])
apply (subst (asm) iso_2)+
apply (subst (asm) int_zero_1)
apply (simp)
apply (clarify)
apply (subst (asm) iso_2)
apply (frule_tac a="a" in pos_mod_conj)
apply (simp)
apply (rule sym)
apply (subst option_map_eq_Some)
apply (rule_tac x="0'''" in exI)
apply (subst ga_function_monotonicity[THEN sym])
apply (simp)
apply (rule conjI)
apply (rule_tac x="int2Int q" in exI)
apply (rule Int2int_inj)
apply (force)
apply (rule gn_inj_Int_Nat_Neq_2)
apply (subst ga_function_monotonicity[THEN sym])
apply (subst abs_def_Int)
apply (split split_if)
apply (rule conjI)
apply (subst ga_function_monotonicity[THEN sym])+
apply (clarify)
apply (drule Int_order6)
apply (drule Int2int_wd)
apply (subst (asm) int_u_minus_1[THEN sym])
apply (subst (asm) iso_2)+
apply (subst (asm) int_zero_1)+
apply (thin_tac "b < 0")
apply (force)
apply (clarify)
apply (thin_tac "~ int2Int b <' gn_inj_Nat_Int(0''')")
apply (drule Int2int_wd)
apply (subst (asm) int_zero_1)+
apply (subst (asm) iso_2)+
apply (blast)
apply (subst (asm) mod_dom_Int)
apply (subst (asm) ga_function_monotonicity[THEN sym])
by (blast)

theorem Int_mod_1_1 [rule_format, simp] : "!! a b z . 
  (b < 0 & a mod b ~= 0) --> 
  (Some (int2Int ((a mod b) - b)) = 
    (option_map X_gn_inj_Nat_Int ((int2Int a) mod' (int2Int b))))"
apply (clarify)
apply (rule sym)
apply (subst option_map_eq_Some)
apply (rule_tac x="nat2Nat (nat(a mod b-b))" in exI)
apply (rule conjI)
prefer 2
apply (subst Int_inj_2[THEN sym])
apply (rule Int2int_inj)
apply (subst nat_pos)
apply (simp)
apply (simp)
apply (simp)
apply (rule conjI)
apply (rule_tac x="int2Int(a div b + 1)" in exI)
apply (subst Int_inj_2[THEN sym])
apply (subst nat_pos)
apply (rule conjI)
apply (simp)
apply (drule_tac a="a" in neg_mod_conj)
apply (simp)
apply (rule Int2int_inj)
apply (simp)
apply (subst zadd_zmult_distrib2)
apply (simp)
apply (subst ga_predicate_monotonicity_1[THEN sym])
apply (rule conjI)
apply (rule Int_order5b)
apply (subst Int_inj_1)
apply (subst int_abs_1[THEN sym])
apply (subst Nat2nat_iso)
apply (subst iso_2)
apply (subst nat_pos)
apply (rule conjI)
apply (blast)
apply (frule_tac a="a" in neg_mod_conj)
apply (simp)
apply (simp)
apply (rule gn_inj_Int_Nat_Neq_2)
apply (rule Int2int_inj_3)
apply (subst abs_def_Int)
apply (subst ga_function_monotonicity[THEN sym])
apply (split split_if)
apply (rule conjI)
apply (clarify)
apply (drule Int_order6)
apply (subst (asm) Int_inj_1)
apply (subst (asm) Nat2nat_iso)
apply (subst (asm) int_u_minus_1[THEN sym])
apply (subst (asm) iso_2)+
apply (subst (asm) int_zero_1)
apply (subst (asm) nat_pos)
apply (rule conjI)
apply (blast)
apply (drule_tac a="a" in neg_mod_conj)
apply (blast)
apply (drule_tac f="% x . x + b" in arg_cong)
apply (simp)
apply (clarify)
apply (erule notE)
apply (erule notE)
apply (subst (asm) Int_inj_1)
apply (subst (asm) Nat2nat_iso)
apply (subst (asm) iso_2)+
apply (subst (asm) nat_pos)
apply (rule conjI)
apply (blast)
apply (drule_tac a="a" in neg_mod_conj)
apply (blast)
apply (drule_tac f="% x . x + b" in arg_cong)
apply (simp)
apply (drule_tac a="a" in neg_mod_conj)
by (simp)

theorem Int_mod_1_2 [rule_format, simp] : "!! a b z . 
 (b > 0 | (b < 0 & a mod b = 0)) -->
    (Some (int2Int ((a mod b))) = 
      (option_map X_gn_inj_Nat_Int ((int2Int a) mod' (int2Int b))))"
apply (clarify)
apply (auto)
apply (rule sym)
apply (subst option_map_eq_Some)
apply (rule_tac x="0'''" in exI)
apply (subst ga_function_monotonicity[THEN sym])
apply (simp)
apply (rule conjI)
apply (rule_tac x="int2Int q" in exI)
apply (rule Int2int_inj)
apply (simp)
apply (rule gn_inj_Int_Nat_Neq_2)
apply (subst abs_def_Int)
apply (split split_if)
apply (rule conjI)
apply (subst ga_function_monotonicity[THEN sym])+
apply (clarify)
apply (drule Int_order6)
apply (drule Int2int_wd)
apply (subst (asm) int_u_minus_1[THEN sym])
apply (subst (asm) iso_2)+
apply (subst (asm) int_zero_1)+
apply (thin_tac "b < 0")
apply (force)
apply (clarify)
apply (drule Int2int_wd)
apply (subst (asm) ga_function_monotonicity[THEN sym])+
apply (subst (asm) int_zero_1)+
apply (subst (asm) iso_2)+
by (blast)

theorem Nat_Int_embed_eq [rule_format] : "ALL x. ALL y. (gn_inj_Nat_Int(x) = gn_inj_Nat_Int(y)) = (x = y)"
apply (auto)
apply (rule ga_embedding_injectivity)
by blast

theorem Int_mod_2 [rule_format, simp] : "!! a b . 
if (b <' 0'' & a mod' b ~= Some 0''') then 
  (option_map Int2int (option_map X_gn_inj_Nat_Int(a mod' b)) = Some (Int2int a mod Int2int b - Int2int b))
else if (b ~= 0'') then
  (option_map Int2int (option_map X_gn_inj_Nat_Int(a mod' b)) = Some (Int2int a mod Int2int b))
else
  ~ (defOp(a mod' b))
"
(* First goal *)
apply (split split_if)
apply (rule conjI)
apply (clarify)
apply (rule_tac x="int2Int (Int2int a mod Int2int b) -' b" in exI)
apply (simp)
apply (rule_tac x="nat2Nat( nat (Int2int a mod Int2int b - Int2int b))" in exI)
apply (rule conjI)
apply (rule_tac x="int2Int(Int2int a div Int2int b + 1)" in exI)
apply (rule Int2int_inj)
apply (simp)
apply (subst Int_inj_1)
apply (subst Nat2nat_iso)
apply (drule Int_order6)
apply (subst (asm) int_zero_1)
apply (subst nat_pos)
apply (simp)
apply (subst zadd_zmult_distrib2)
apply (simp)
apply (rule conjI)
apply (subst ga_predicate_monotonicity_1[THEN sym])
apply (simp)
apply (rule conjI)
apply (clarify)
apply (subst (asm) ga_function_monotonicity[THEN sym])+
apply (rule Int_order5b)
apply (drule Int_order6)+
apply (subst Int_inj_1)+
apply (subst Nat2nat_iso)+
apply (subst nat_pos)
apply (simp)
apply (subst int_u_minus_2)
apply (subst (asm) int_zero_1)+
apply (drule_tac a="Int2int a" in  neg_mod_conj)
apply (simp)
apply (clarify)
apply (drule Int_order6)+
apply (subst (asm) ga_function_monotonicity[THEN sym])+
apply (subst (asm) int_zero_1)+
apply (drule negation_lemma_1)
apply (drule Int_order5)
apply (simp)
apply (rule conjI)
apply (rule gn_inj_Int_Nat_Neq_2)
apply (rule Int2int_inj_3)
apply (subst int_abs_2)
apply (subst Int_inj_2[THEN sym])
apply (subst iso_2)
apply (drule Int_order6)
apply (subst (asm) zero_Int2int)
apply (subst nat_pos_2)
apply (drule_tac a="Int2int a" in neg_mod_conj)
apply (thin_tac "(ALL r. a ~= b *' r) | 0''' = abs'(b)")
apply (force)
apply (drule_tac a="Int2int a" in neg_mod_conj)
apply (simp)
apply (clarify)
apply (case_tac "0''' = abs'(b)")
apply (simp)
apply (subst (asm) Nat_Int_embed_eq[THEN sym])
apply (drule Int2int_wd)
apply (subst (asm) int_abs_2)
apply (subst (asm) ga_function_monotonicity[THEN sym])
apply (subst (asm) zero_Int2int)
apply (arith)
apply (simp)
apply (subst (asm) Nat_Int_embed_eq[THEN sym])
apply (drule Int2int_inj_2)
apply (subst (asm) int_abs_2)
apply (subst (asm) ga_function_monotonicity[THEN sym])
apply (subst (asm) zero_Int2int)
apply (drule_tac x="int2Int q" in spec)
apply (drule Int2int_inj_2)
apply (subst (asm) int_mult_2)
apply (subst (asm) iso_2)
apply (blast)
apply (drule Int_order6)
apply (subst (asm) zero_Int2int)
apply (rule Int2int_inj)
apply (subst Int_inj_2[THEN sym])
apply (subst iso_2)
apply (subst int_add_2)
apply (subst int_u_minus_2)
apply (subst iso_2)
apply (subst nat_pos_2)
apply (drule_tac a="Int2int a" in neg_mod_conj)
apply (force)
apply (case_tac "0''' = abs'(b)")
apply (simp)
apply (simp)
(* Second goal *)
apply (clarify)
apply (subst (asm) de_Morgan_conj)
apply (split split_if)
apply (rule conjI)
apply (clarify)
apply (rule_tac x="int2Int(Int2int a mod Int2int b)" in exI)
apply (subst option_map_eq_Some)
apply (rule conjI)
apply (rule_tac x="nat2Nat( nat (Int2int a mod Int2int b))" in exI)
apply (rule conjI)
apply (case_tac "~ b <' 0''")
apply (simp only: iso_2 triv_forall_equality True_implies_equals if_True if_False if_cancel if_eq_cancel imp_disjL conj_assoc disj_assoc de_Morgan_conj
 de_Morgan_disj imp_disj1 imp_disj2 not_imp disj_not1 not_all not_ex cases_simp the_eq_trivial the_sym_eq_trivial ex_simps all_simps simp_thms)
apply (subst mod_Int)
apply (rule_tac x="int2Int(Int2int a div Int2int b)" in exI)
apply (rule conjI)
apply (rule Int2int_inj)
apply (simp)
apply (subst Int_inj_2[THEN sym])
apply (subst iso_2)
apply (subst nat_pos_2)
apply (drule Int2int_inj_2, subst (asm) Int_order_lem_6, (subst (asm) zero_Int2int)+)
apply (simp)
apply (drule Int2int_inj_2, subst (asm) Int_order_lem_6, (subst (asm) zero_Int2int)+)
apply (simp)
apply (drule Int2int_inj_2, subst (asm) Int_order_lem_6, (subst (asm) zero_Int2int)+)
apply (subst ga_predicate_monotonicity[THEN sym])
apply (rule Int_order6b)
apply (subst int_abs_2)
apply (subst Int_inj_2[THEN sym])
apply (subst iso_2)
apply (subst nat_pos_2)
apply (simp)
apply (simp)
apply (simp only: iso_2 triv_forall_equality True_implies_equals if_True if_False if_cancel if_eq_cancel imp_disjL conj_assoc disj_assoc de_Morgan_conj
 de_Morgan_disj imp_disj1 imp_disj2 not_imp disj_not1 not_all not_ex cases_simp the_eq_trivial the_sym_eq_trivial ex_simps all_simps simp_thms)
apply (simp)
apply (drule Int2int_inj_2, subst (asm) Int_order_lem_6, (subst (asm) zero_Int2int)+)
apply (clarify)
apply (rule ga_embedding_injectivity)
apply (rule Int2int_inj, subst ga_function_monotonicity[THEN sym], subst zero_Int2int)
apply (subst Int_inj_2[THEN sym], subst iso_2)
apply (subst int_mult_2)
apply(simp)
apply (drule Int2int_inj_2, subst (asm) Int_order_lem_6, (subst (asm) zero_Int2int)+)
apply (rule Int2int_inj)
apply (subst Int_inj_2[THEN sym])
apply (subst iso_2)+
apply (subst nat_pos_2)
apply (simp del: mod_Int)
apply (subst (asm) disj_not1[THEN sym])
apply (case_tac "~ Int2int b < 0")
apply (simp del: mod_Int)
apply (drule notnotD)
apply (simp)
apply (drule conjunct1)
apply (subst (asm) Int2int_inj_4[THEN sym])
apply (subst (asm) int_mult_2)
apply (force)
apply (blast)
apply (subst iso_2)
apply (blast)
(* Third goal *)
apply (clarify)
apply (case_tac "~ 0'' <' 0''")
apply (simp)
apply (subst (asm) mod_dom_Int)
apply (erule notE)
apply (subst ga_function_monotonicity[THEN sym])
apply (blast)
apply (subst (asm) mod_dom_Int)
apply (erule notE)
back
apply (subst ga_function_monotonicity[THEN sym])
by (blast)

theorem Int_div_1 [rule_format] : "! a b . (b ~= 0) --> 
  (if (b < 0 & a mod b ~= 0) then
  Some (int2Int(a div b + 1)) = (int2Int a div' int2Int b)
  else
  Some (int2Int(a div b)) = (int2Int a div' int2Int b))"
apply (clarify)
apply (split split_if)
apply (rule conjI)
apply (clarify)
apply (rule sym)
apply (subst div_Int)
apply (rule_tac x="nat2Nat(nat(a mod b - b))" in exI)
apply (rule conjI)
apply (rule Int2int_inj)
apply (subst int_add_2)
apply (subst int_mult_2)
apply (subst Int_inj_2[THEN sym])
apply (subst iso_2)+
apply (subst nat_pos_2)
apply (drule_tac a="a" in neg_mod_conj)
apply (force)
apply (subst zadd_zmult_distrib2)
apply (simp)
apply (subst ga_predicate_monotonicity[THEN sym])
apply (rule Int_order6b)
apply (subst int_abs_2)
apply (subst Int_inj_1)+
apply (subst Nat2nat_iso, subst iso_2)
apply (subst nat_pos_2)
apply (drule_tac a="a" in neg_mod_conj)
apply (force)
apply (drule_tac a="a" in neg_mod_conj)
apply (simp)
apply (clarify)
apply (subst (asm) de_Morgan_conj)
apply (case_tac "b < 0")
apply (rule sym)
apply (subst div_Int)
apply (rule_tac x="nat2Nat(nat(a mod b))" in exI)
apply (rule conjI)
apply (rule Int2int_inj)
apply (simp)
apply (force)
apply (subst ga_predicate_monotonicity[THEN sym])
apply (rule Int_order6b)
apply (subst int_abs_2)
apply (subst Int_inj_1)+
apply (subst Nat2nat_iso, subst iso_2)
apply (subst nat_pos_2)
apply (simp)
apply (simp)
apply (rule sym)
apply (subst div_Int)
apply (rule_tac x="nat2Nat(nat(a mod b))" in exI)
apply (rule conjI)
apply (rule Int2int_inj)
apply (simp)
apply (subst Int_inj_1)+
apply (subst Nat2nat_iso)
apply (subst nat_pos_2)
apply (simp)
apply (simp)
apply (subst ga_predicate_monotonicity[THEN sym])
apply (rule Int_order6b)
apply (subst int_abs_2)
apply (subst Int_inj_1)+
apply (subst Nat2nat_iso, subst iso_2)
apply (subst nat_pos_2)
apply (simp)
by (simp)


lemma mod_neq_zero [rule_format] : "!! a (b::int) . a ~= b * (a div b) --> a mod b ~= 0"
by (auto)

theorem Int_div_2 [rule_format, simp] : "! a b . (b ~= 0'') --> 
  (if (b <' 0'' & a mod' b ~= Some 0''' ) then
  option_map Int2int (a div' b) = Some (Int2int a div Int2int b + 1 )
  else
  option_map Int2int (a div' b) = Some (Int2int a div Int2int b))"
apply (clarify)
apply (split split_if)
apply (rule conjI)
apply (clarify)
apply (rule_tac x="int2Int (Int2int a div Int2int b + 1)" in exI)
apply (rule conjI)
apply (subst div_Int)
apply (rule_tac x="nat2Nat (nat (Int2int a mod Int2int b - Int2int b))" in exI)
apply (rule conjI)
apply (rule Int2int_inj)
apply (simp only: iso_2 Nat2nat_iso int_add_2 int_mult_2 triv_forall_equality True_implies_equals if_True if_False if_cancel if_eq_cancel imp_disjL conj_assoc disj_assoc de_Morgan_conj
 de_Morgan_disj imp_disj1 imp_disj2 not_imp disj_not1 not_all not_ex cases_simp the_eq_trivial the_sym_eq_trivial ex_simps all_simps simp_thms)
apply (subst Int_inj_1)+
apply (subst Nat2nat_iso)
apply (subst nat_pos_2)
apply (drule Int_order6)
apply (subst (asm) zero_Int2int)
apply (drule_tac a="Int2int a" in neg_mod_conj)
apply (simp)
apply (subst zadd_zmult_distrib2)
apply (simp)
apply (subst ga_predicate_monotonicity[THEN sym])
apply (rule Int_order6b)
apply (subst int_abs_2)
apply (subst Int_inj_1)+
apply (subst Nat2nat_iso)
apply (drule Int_order6)
apply (subst (asm) zero_Int2int)
apply (subst nat_pos_2)
apply (drule_tac a="Int2int a" in neg_mod_conj)
apply (simp)
apply (subst (asm) mod_Int)
apply (subst (asm) ga_predicate_monotonicity[THEN sym])
apply (subst (asm) Int2int_inj_4[THEN sym])+
apply (subst (asm) Int_order_lem_6)
apply (subst (asm) int_abs_2)
apply (subst (asm) ga_function_monotonicity[THEN sym])+
apply (subst (asm) zero_Int2int)+
apply (simp)
apply (drule_tac x="int2Int(Int2int a div Int2int b)" in spec)
apply (simp)
apply (drule_tac a="Int2int a" in neg_mod_conj)
apply (drule mod_neq_zero)
apply (simp)
apply (subst iso_2)
apply (blast)
apply (clarify)
apply (subst (asm) de_Morgan_conj)
apply (case_tac "~ b <' 0''")
apply (rule_tac x="int2Int(Int2int a div Int2int b)" in exI)
apply (rule conjI)
apply (subst div_Int)
apply (rule_tac x="nat2Nat(nat(Int2int a mod Int2int b))" in exI)
apply (rule conjI)
apply (rule Int2int_inj)
apply (subst int_add_2)
apply (subst int_mult_2)
apply (subst iso_2)
apply (subst Int_inj_1)
apply (subst Nat2nat_iso)
apply (subst nat_pos_2)
apply (drule Int2int_inj_2)
apply (drule Int_lt_2_le)
apply (drule Int_order5)
apply (subst (asm) zero_Int2int)+
apply (simp)
apply (subst zmod_zdiv_equality[THEN sym])
apply (blast)
apply (subst ga_predicate_monotonicity[THEN sym])
apply (rule Int_order6b)
apply (subst int_abs_2)
apply (subst Int_inj_1)
apply (subst Nat2nat_iso)
apply (subst nat_pos_2, drule Int2int_inj_2, drule Int_lt_2_le,
  drule Int_order5, (subst (asm) zero_Int2int)+, simp)
apply (simp)
apply (drule Int2int_inj_2, drule Int_lt_2_le, drule Int_order5,
  (subst (asm) zero_Int2int)+, simp)
apply (subst iso_2)
apply (blast)
apply (rule_tac x="int2Int(Int2int a div Int2int b)" in exI)
apply (subst iso_2)+
apply (rule conjI)
apply (subst div_Int)
apply (rule_tac x="nat2Nat(nat(Int2int a mod Int2int b))" in exI)
apply (rule conjI)
apply (rule Int2int_inj)
apply (subst int_add_2, subst int_mult_2)
apply (subst Int_inj_1)
apply ((subst iso_2)+, (subst Nat2nat_iso)+)
apply (subst nat_pos_2)
apply (drule Int2int_inj_2)
apply (drule notnotD)
apply (simp)
apply (drule Int_order6)
apply (subst (asm) zero_Int2int)+
apply (subst (asm) Nat_Int_embed_eq[THEN sym])
apply (subst (asm) Int2int_inj_4[THEN sym])+
apply (subst (asm) ga_function_monotonicity[THEN sym])+
apply (subst (asm) int_abs_2)
apply (subst (asm) zero_Int2int)+
apply (subst (asm) int_mult_2)
apply (force)
apply (subst zmod_zdiv_equality[THEN sym])
apply (blast)
apply (drule notnotD)
apply (drule Int_order6)
apply (subst (asm) zero_Int2int)+
apply (subst (asm) Int2int_inj_4[THEN sym])+
apply (subst (asm) Int_order_lem_6)
apply (subst (asm) zero_Int2int)+
apply (simp)
by (blast)

section "Even odd"

theorem Int_even_1 [rule_format, simp] : "!! a . even'(a) = ev_int(Int2int(a))"
apply (auto simp add: ev_int_def)
apply (subst int_abs_2[THEN sym])
apply (subst Int_inj_1)
apply (simp)
apply (subst (asm) int_abs_2[THEN sym])
apply (subst (asm) Int_inj_1)
by (simp)

lemma iso_inj_proj [rule_format] : "!! a . gn_proj_Int_Nat(gn_inj_Nat_Int(a)) = Some a"
by (auto)

lemma int_inj_lemma_1 [rule_format] : "!! a (b::nat) . int a = int b --> a = b"
by (auto)

lemma int_inj_lemma_2 [rule_format] : "!! a (b::nat) . a = b --> int a = int b"
by (auto)

theorem Int_even_2 [rule_format, simp] : "!! a . ev_int(a) = even'(int2Int(a))"
apply (subst Int_even_1)
apply (subst iso_2)
by (blast)

theorem Int_odd_1 [rule_format, simp] : "!! a . odd'(a) = od_int(Int2int(a))"
apply (auto simp add: od_int_def)
apply (subst int_abs_2[THEN sym])
apply (subst Int_inj_1)
apply (simp)
apply (subst (asm) int_abs_2[THEN sym])
apply (subst (asm) Int_inj_1)
by (simp)

theorem Int_odd_2 [rule_format, simp] : "!! a . od_int(a) = odd'(int2Int(a))"
apply (subst Int_odd_1)
apply (subst iso_2)
by (blast)

section "Min/Max"

theorem Int_min_1 [rule_format] : "!! a (b::int) . min'(int2Int a, int2Int b) = 
  int2Int(min a b)"

end
