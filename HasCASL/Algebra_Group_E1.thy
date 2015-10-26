theory Algebra_Group_E1
imports "$HETS_LIB/Isabelle/MainHCPairs"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"subtype_def\", \"subtype_pred_def\", \"ga_assoc___Xx__\",
     \"ga_right_unit___Xx__\", \"ga_left_unit___Xx__\", \"inv_Group\",
     \"rinv_Group\"]"

typedecl Elem

consts
X__Xx__X :: "Elem => Elem => Elem" ("(_/ *''/ _)" [54,54] 52)
X_inv :: "Elem => Elem" ("inv''/'(_')" [3] 999)
X_isSubtype :: "('s => 't) => ('t => 's) => bool" ("isSubtype/'(_,/ _')" [3,3] 999)
X_isSubtypeWithPred :: "('t => bool) => ('s => 't) => ('t => 's) => bool" ("isSubtypeWithPred/'(_,/ _,/ _')" [3,3,3] 999)
e :: "Elem"

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
"ALL x. ALL y. ALL z. (x *' y) *' z = x *' (y *' z)"

ga_right_unit___Xx__ [rule_format] : "ALL x. x *' e = x"

ga_left_unit___Xx__ [rule_format] : "ALL x. e *' x = x"

inv_Group [rule_format] : "ALL x. inv'(x) *' x = e"

declare ga_assoc___Xx__ [simp]
declare ga_right_unit___Xx__ [simp]
declare ga_left_unit___Xx__ [simp]
declare inv_Group [simp]

theorem rinv_Group : "ALL x. x *' inv'(x) = e"
  proof
    fix x
    have "x *' inv'(x) = (inv'(inv'(x)) *' inv'(x)) *' (x *' inv'(x))"
      by simp
    also have "\<dots> = inv'(inv'(x))  *' ((inv'(x) *' x) *' inv'(x))"
      by (simp only: ga_assoc___Xx__)
    also have "\<dots> = e" by simp
    finally show "x *' inv'(x) = e" by simp
  qed

ML "Header.record \"rinv_Group\""

end
