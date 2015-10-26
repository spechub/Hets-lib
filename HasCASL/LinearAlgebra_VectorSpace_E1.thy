theory LinearAlgebra_VectorSpace_E1
imports "$HETS_LIB/Isabelle/MainHCPairs"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"subtype_def\", \"subtype_pred_def\", \"ga_assoc___Xx__\",
     \"ga_right_unit___Xx__\", \"ga_left_unit___Xx__\", \"inv_Group\",
     \"rinv_Group\", \"ga_comm___Xx__\", \"binary_inverse\",
     \"ga_assoc___Xx___2\", \"ga_right_unit___Xx___2\",
     \"ga_left_unit___Xx___2\", \"inv_Group_1\", \"rinv_Group_1\",
     \"ga_comm___Xx___2\", \"ga_assoc___Xx___1\",
     \"ga_right_unit___Xx___1\", \"ga_left_unit___Xx___1\",
     \"distr1_Ring\", \"distr2_Ring\", \"ga_comm___Xx___1\",
     \"noZeroDiv\", \"zeroNeqOne\", \"Ax1\", \"ga_assoc___Xx___2_1\",
     \"ga_right_unit___Xx___2_1\", \"ga_left_unit___Xx___2_1\",
     \"inv_Group_1_1\", \"rinv_Group_1_1\", \"unit\", \"mix_assoc\",
     \"distr_Field\", \"distr_Space\", \"zero_by_left_zero\",
     \"zero_by_right_zero\", \"inverse_by_XMinus1\"]"

typedecl Elem
typedecl NonZero
typedecl Space

consts
X0X1 :: "Elem" ("0''")
X0X2 :: "Space" ("0''''")
X1X1 :: "Elem" ("1''")
X1X2 :: "NonZero" ("1''''")
XMinus__XX1 :: "Elem => Elem" ("(-''/ _)" [56] 56)
XMinus__XX2 :: "Space => Space" ("(-''''/ _)" [56] 56)
X__XMinus__X :: "Space => Space => Space" ("(_/ -''/ _)" [54,54] 52)
X__XPlus__XX1 :: "Elem => Elem => Elem" ("(_/ +''/ _)" [54,54] 52)
X__XPlus__XX2 :: "Space => Space => Space" ("(_/ +''''/ _)" [54,54] 52)
X__Xx__XX1 :: "Elem => Elem => Elem" ("(_/ *''/ _)" [54,54] 52)
X__Xx__XX2 :: "Elem => Space => Space" ("(_/ *''''/ _)" [54,54] 52)
X__Xx__XX3 :: "NonZero => NonZero => NonZero" ("(_/ *'_3/ _)" [54,54] 52)
X_gn_inj :: "'a => 'b" ("gn'_inj/'(_')" [3] 999)
X_gn_proj :: "'a => 'b partial" ("gn'_proj/'(_')" [3] 999)
X_inv :: "NonZero => NonZero" ("inv''/'(_')" [3] 999)
X_isSubtype :: "('s => 't) => ('t => 's) => bool" ("isSubtype/'(_,/ _')" [3,3] 999)
X_isSubtypeWithPred :: "('t => bool) => ('s => 't) => ('t => 's) => bool" ("isSubtypeWithPred/'(_,/ _,/ _')" [3,3,3] 999)

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
"ALL x. ALL y. ALL z. (x +'' y) +'' z = x +'' (y +'' z)"

ga_right_unit___Xx__ [rule_format] : "ALL x. x +'' 0'' = x"

ga_left_unit___Xx__ [rule_format] : "ALL x. 0'' +'' x = x"

inv_Group [rule_format] : "ALL x. -'' x +'' x = 0''"

rinv_Group [rule_format] : "ALL x. x +'' -'' x = 0''"

ga_comm___Xx__ [rule_format] : "ALL x. ALL y. x +'' y = y +'' x"

binary_inverse [rule_format] : "ALL x. ALL y. x -' y = x +'' -'' y"

ga_assoc___Xx___2 [rule_format] :
"ALL x. ALL y. ALL z. (x +' y) +' z = x +' (y +' z)"

ga_right_unit___Xx___2 [rule_format] : "ALL x. x +' 0' = x"

ga_left_unit___Xx___2 [rule_format] : "ALL x. 0' +' x = x"

inv_Group_1 [rule_format] : "ALL x. -' x +' x = 0'"

rinv_Group_1 [rule_format] : "ALL x. x +' -' x = 0'"

ga_comm___Xx___2 [rule_format] : "ALL x. ALL y. x +' y = y +' x"

ga_assoc___Xx___1 [rule_format] :
"ALL x. ALL y. ALL z. (x *' y) *' z = x *' (y *' z)"

ga_right_unit___Xx___1 [rule_format] : "ALL x. x *' 1' = x"

ga_left_unit___Xx___1 [rule_format] : "ALL x. 1' *' x = x"

distr1_Ring [rule_format] :
"ALL x. ALL y. ALL z. (x +' y) *' z = (x *' z) +' (y *' z)"

distr2_Ring [rule_format] :
"ALL x. ALL y. ALL z. z *' (x +' y) = (z *' x) +' (z *' y)"

ga_comm___Xx___1 [rule_format] : "ALL x. ALL y. x *' y = y *' x"

noZeroDiv [rule_format] :
"ALL x. ALL y. x *' y = 0' --> x = 0' | y = 0'"

zeroNeqOne [rule_format] : "~ 1' = 0'"

Ax1 [rule_format] : "ALL x. defOp (gn_proj(x)) = (~ x = 0')"

ga_assoc___Xx___2_1 [rule_format] :
"ALL x. ALL y. ALL z. (x *_3 y) *_3 z = x *_3 (y *_3 z)"

ga_right_unit___Xx___2_1 [rule_format] : "ALL x. x *_3 1'' = x"

ga_left_unit___Xx___2_1 [rule_format] : "ALL x. 1'' *_3 x = x"

inv_Group_1_1 [rule_format] : "ALL x. inv'(x) *_3 x = 1''"

rinv_Group_1_1 [rule_format] : "ALL x. x *_3 inv'(x) = 1''"

unit [rule_format] : "ALL x. gn_inj(1'') *'' x = x"

mix_assoc [rule_format] :
"ALL r. ALL s. ALL x. (r *' s) *'' x = r *'' (s *'' x)"

distr_Field [rule_format] :
"ALL r. ALL s. ALL x. (r +' s) *'' x = (r *'' x) +'' (s *'' x)"

distr_Space [rule_format] :
"ALL r. ALL x. ALL y. r *'' (x +'' y) = (r *'' x) +'' (r *'' y)"

declare ga_assoc___Xx__ [simp]
declare ga_right_unit___Xx__ [simp]
declare ga_left_unit___Xx__ [simp]
declare inv_Group [simp]
declare rinv_Group [simp]
declare ga_comm___Xx__ [simp]
declare ga_assoc___Xx___2 [simp]
declare ga_right_unit___Xx___2 [simp]
declare ga_left_unit___Xx___2 [simp]
declare inv_Group_1 [simp]
declare rinv_Group_1 [simp]
declare ga_comm___Xx___2 [simp]
declare ga_assoc___Xx___1 [simp]
declare ga_right_unit___Xx___1 [simp]
declare ga_left_unit___Xx___1 [simp]
declare ga_comm___Xx___1 [simp]
declare ga_assoc___Xx___2_1 [simp]
declare ga_right_unit___Xx___2_1 [simp]
declare ga_left_unit___Xx___2_1 [simp]
declare inv_Group_1_1 [simp]
declare rinv_Group_1_1 [simp]
declare unit [simp]

theorem zero_by_left_zero : "ALL x. 0' *'' x = 0''"
proof
  fix x
  have "0' = 0' +' 0'" by simp
  hence "0' *'' x = (0' +' 0') *'' x" by simp
  hence fact: "0' *'' x = (0' *'' x) +'' (0' *'' x)" by (simp only: distr_Field)
  have "0'' = -''(0' *'' x) +'' (0' *'' x)" by simp
  also from fact have "\<dots> = -''(0' *'' x) +'' ((0' *'' x) +'' (0' *'' x))" by simp
  also have "\<dots> = (-''(0' *'' x) +'' (0' *'' x)) +'' (0' *'' x)" by (simp only: ga_assoc___Xx__)
  finally show "0' *'' x = 0''"
    by (simp  only: ga_left_unit___Xx__ inv_Group)
qed
  
ML "Header.record \"zero_by_left_zero\""

theorem zero_by_right_zero : "ALL r. r *'' 0'' = 0''"
using subtype_def subtype_pred_def by (auto)

ML "Header.record \"zero_by_right_zero\""

-- "the 1'' shouldn't be exported, but only 1' at its place!"
theorem inverse_by_XMinus1 : "ALL x. -' gn_inj(1'') *'' x = -'' x"
using subtype_def subtype_pred_def by (auto)

ML "Header.record \"inverse_by_XMinus1\""

end
