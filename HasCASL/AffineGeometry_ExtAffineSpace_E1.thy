theory AffineGeometry_ExtAffineSpace_E1
imports "$HETS_LIB/Isabelle/MainHCPairs"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"subtype_def\", \"subtype_pred_def\", \"ga_assoc___Xx__\",
     \"ga_right_unit___Xx__\", \"ga_left_unit___Xx__\", \"inv_Group\",
     \"rinv_Group\", \"ga_comm___Xx__\", \"ga_assoc___Xx___1\",
     \"ga_right_unit___Xx___1\", \"ga_left_unit___Xx___1\",
     \"distr1_Ring\", \"distr2_Ring\", \"ga_comm___Xx___1\",
     \"noZeroDiv\", \"zeroNeqOne\", \"Ax1\", \"ga_assoc___Xx___2\",
     \"ga_right_unit___Xx___2\", \"ga_left_unit___Xx___2\",
     \"inv_Group_1\", \"rinv_Group_1\", \"ga_assoc___Xx___3\",
     \"ga_right_unit___Xx___3\", \"ga_left_unit___Xx___3\",
     \"inv_Group_2\", \"rinv_Group_2\", \"ga_comm___Xx___3\",
     \"binary_inverse\", \"unit\", \"mix_assoc\", \"distr_Field\",
     \"distr_Space\", \"zero_by_left_zero\", \"zero_by_right_zero\",
     \"inverse_by_XMinus1\", \"plus_injective\", \"plus_surjective\",
     \"point_vector_plus_associative\", \"vec_def\",
     \"transitivity_of_vec_plus\", \"plus_vec_identity\"]"

typedecl Elem
typedecl NonZero
typedecl Point
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
X__XPlus__XX2 :: "Point => Space => Point" ("(_/ +''''/ _)" [54,54] 52)
X__XPlus__XX3 :: "Space => Space => Space" ("(_/ +'_3/ _)" [54,54] 52)
X__Xx__XX1 :: "Elem => Elem => Elem" ("(_/ *''/ _)" [54,54] 52)
X__Xx__XX2 :: "Elem => Space => Space" ("(_/ *''''/ _)" [54,54] 52)
X__Xx__XX3 :: "NonZero => NonZero => NonZero" ("(_/ *'_3/ _)" [54,54] 52)
X_gn_inj :: "'a => 'b" ("gn'_inj/'(_')" [3] 999)
X_gn_proj :: "'a => 'b partial" ("gn'_proj/'(_')" [3] 999)
X_inv :: "NonZero => NonZero" ("inv''/'(_')" [3] 999)
X_isSubtype :: "('s => 't) => ('t => 's) => bool" ("isSubtype/'(_,/ _')" [3,3] 999)
X_isSubtypeWithPred :: "('t => bool) => ('s => 't) => ('t => 's) => bool" ("isSubtypeWithPred/'(_,/ _,/ _')" [3,3,3] 999)
X_vec :: "Point => Point => Space" ("vec/'(_,/ _')" [3,3] 999)

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

inv_Group [rule_format] : "ALL x. -' x +' x = 0'"

rinv_Group [rule_format] : "ALL x. x +' -' x = 0'"

ga_comm___Xx__ [rule_format] : "ALL x. ALL y. x +' y = y +' x"

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

ga_assoc___Xx___2 [rule_format] :
"ALL x. ALL y. ALL z. (x *_3 y) *_3 z = x *_3 (y *_3 z)"

ga_right_unit___Xx___2 [rule_format] : "ALL x. x *_3 1'' = x"

ga_left_unit___Xx___2 [rule_format] : "ALL x. 1'' *_3 x = x"

inv_Group_1 [rule_format] : "ALL x. inv'(x) *_3 x = 1''"

rinv_Group_1 [rule_format] : "ALL x. x *_3 inv'(x) = 1''"

ga_assoc___Xx___3 [rule_format] :
"ALL x. ALL y. ALL z. (x +_3 y) +_3 z = x +_3 (y +_3 z)"

ga_right_unit___Xx___3 [rule_format] : "ALL x. x +_3 0'' = x"

ga_left_unit___Xx___3 [rule_format] : "ALL x. 0'' +_3 x = x"

inv_Group_2 [rule_format] : "ALL x. -'' x +_3 x = 0''"

rinv_Group_2 [rule_format] : "ALL x. x +_3 -'' x = 0''"

ga_comm___Xx___3 [rule_format] : "ALL x. ALL y. x +_3 y = y +_3 x"

binary_inverse [rule_format] : "ALL x. ALL y. x -' y = x +_3 -'' y"

unit [rule_format] : "ALL x. gn_inj(1'') *'' x = x"

mix_assoc [rule_format] :
"ALL r. ALL s. ALL x. (r *' s) *'' x = r *'' (s *'' x)"

distr_Field [rule_format] :
"ALL r. ALL s. ALL x. (r +' s) *'' x = (r *'' x) +_3 (s *'' x)"

distr_Space [rule_format] :
"ALL r. ALL x. ALL y. r *'' (x +_3 y) = (r *'' x) +_3 (r *'' y)"

zero_by_left_zero [rule_format] : "ALL x. 0' *'' x = 0''"

zero_by_right_zero [rule_format] : "ALL r. r *'' 0'' = 0''"

inverse_by_XMinus1 [rule_format] :
"ALL x. -' gn_inj(1'') *'' x = -'' x"

plus_injective [rule_format] :
"ALL p. ALL v. ALL w. p +'' v = p +'' w --> v = w"

plus_surjective [rule_format] : "ALL p. ALL q. EX y. p +'' y = q"

point_vector_plus_associative [rule_format] :
"ALL p. ALL v. ALL w. p +'' (v +_3 w) = (p +'' v) +'' w"

vec_def [rule_format] : "ALL p. ALL q. p +'' vec(p, q) = q"

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
declare ga_assoc___Xx___3 [simp]
declare ga_right_unit___Xx___3 [simp]
declare ga_left_unit___Xx___3 [simp]
declare inv_Group_2 [simp]
declare rinv_Group_2 [simp]
declare ga_comm___Xx___3 [simp]
declare unit [simp]
declare zero_by_left_zero [simp]
declare zero_by_right_zero [simp]
declare inverse_by_XMinus1 [simp]
declare vec_def [simp]

theorem transitivity_of_vec_plus :
"ALL p. ALL q. ALL r. vec(p, q) +_3 vec(q, r) = vec(p, r)"
proof (rule allI)+
  fix p q r
  have "p +'' (vec(p,q) +_3 vec(q,r)) = r"
    by (simp only: vec_def point_vector_plus_associative)
  also have "\<dots> = p +'' vec(p,r)" by simp
  finally show "vec(p, q) +_3 vec(q, r) = vec(p, r)"
    by (simp only: plus_injective)
qed

ML "Header.record \"transitivity_of_vec_plus\""

theorem plus_vec_identity :
"ALL p. ALL q. ALL v. p +'' v = q --> v = vec(p, q)"
  proof ((rule allI)+, rule impI)
  fix p q v
  assume "p +'' v = q"
  also have "\<dots> = p +'' vec(p, q)" by simp
  finally show "v = vec(p, q)" by (simp only: plus_injective)
qed

ML "Header.record \"plus_vec_identity\""

end
