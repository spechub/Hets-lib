theory Algebra_Ring_E1
imports "$HETS_LIB/Isabelle/MainHCPairs"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"subtype_def\", \"subtype_pred_def\", \"ga_assoc___Xx__\",
     \"ga_right_unit___Xx__\", \"ga_left_unit___Xx__\", \"inv_Group\",
     \"rinv_Group\", \"ga_comm___Xx__\", \"ga_assoc___Xx___1\",
     \"ga_right_unit___Xx___1\", \"ga_left_unit___Xx___1\",
     \"distr1_Ring\", \"distr2_Ring\", \"left_zero\", \"right_zero\"]"

typedecl Elem

consts
X0 :: "Elem" ("0''")
X1 :: "Elem" ("1''")
XMinus__X :: "Elem => Elem" ("(-''/ _)" [56] 56)
X__XPlus__X :: "Elem => Elem => Elem" ("(_/ +''/ _)" [54,54] 52)
X__Xx__X :: "Elem => Elem => Elem" ("(_/ *''/ _)" [54,54] 52)
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

declare ga_assoc___Xx__ [simp]
declare ga_right_unit___Xx__ [simp]
declare ga_left_unit___Xx__ [simp]
declare inv_Group [simp]
declare rinv_Group [simp]
declare ga_comm___Xx__ [simp]
declare ga_assoc___Xx___1 [simp]
declare ga_right_unit___Xx___1 [simp]
declare ga_left_unit___Xx___1 [simp]

theorem left_zero : "ALL x. 0' *' x = 0'"
proof
  fix x
  have "0' = 0' +' 0'" by simp
  hence "0' *' x = (0' +' 0') *' x" by simp
  hence fact: "0' *' x = (0' *' x) +' (0' *' x)" by (simp only: distr1_Ring)
  have "0' = -'(0' *' x) +' (0' *' x)" by simp
  also from fact have "\<dots> = -'(0' *' x) +' ((0' *' x) +' (0' *' x))" by simp
  also have "\<dots> = (-'(0' *' x) +' (0' *' x)) +' (0' *' x)" by (simp only: ga_assoc___Xx__)
  finally show "0' *' x = 0'"
    by (simp  only: ga_left_unit___Xx__ inv_Group)
qed

ML "Header.record \"left_zero\""

theorem right_zero : "ALL x. x *' 0' = 0'"
proof
  fix x
  have "0' = 0' +' 0'" by simp
  hence "x *' 0' = x *' (0' +' 0')" by simp
  hence fact: "x *' 0' = (x *' 0') +' (x *' 0')" by (simp only: distr2_Ring)
  have "0' = -'(x *' 0') +' (x *' 0')" by simp
  also from fact have "\<dots> = -'(x *' 0') +' ((x *' 0') +' (x *' 0'))" by simp
  also have "\<dots> = (-'(x *' 0') +' (x *' 0')) +' (x *' 0')" by (simp only: ga_assoc___Xx__)
  finally show "x *' 0' = 0'"
    by (simp  only: ga_left_unit___Xx__ inv_Group)
qed

ML "Header.record \"right_zero\""

end
