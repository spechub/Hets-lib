theory PartialityTest_Test_E1
imports "$HETS_ISABELLE_LIB/MainHC" "$HETS_LIB/Isabelle/RestrictOpProps"
uses "$HETS_ISABELLE_LIB/prelude"
begin

ML "Header.initialize [\"Ax1\", \"Ax1_2\"]"

typedecl a

consts
X_f :: "a => a => a partial" ("f/'(_,/ _')" [3,3] 999)

axioms
Ax1 [rule_format] :
"ALL (x :: a).
 ALL (y :: a).
 ALL (z :: a).
 defOp (f(x, y)) & defOp (f(y, z)) -->
 lift2partial (X_f x) (f(y, z)) =
 lift2partial (flip X_f z) (f(x, y))"

lemma assoc_dom : "defOp (f(x, y)) & defOp (f(y, z)) ==> 
  (defOp (f(x, makeTotal (f(y, z)))) & defOp (f(y, z))) = 
  (defOp (f(makeTotal (f(x, y)), z)) & defOp (f(x, y)))"
apply (frule Ax1)
sorry

lemma assoc_eq : "defOp (f(x, y)) & defOp (f(y, z)) ==> 
  f(x, makeTotal (f(y, z))) = f(makeTotal (f(x, y)), z)"
apply (frule Ax1)
apply (auto)
sorry

theorem Ax1_2 :
"ALL (w :: a).
 ALL (x :: a).
 ALL (y :: a).
 ALL (z :: a).
 defOp (lift2partial (X_f x) (f(y, z))) &
 defOp (lift2partial (X_f y) (f(z, w))) -->
 lift2partial (flip X_f w) (lift2partial (X_f x) (f(y, z))) =
 lift2partial (X_f x) (lift2partial (X_f y) (f(z, w)))"
apply (auto)
apply (simp add: assoc_eq assoc_dom)
sorry

ML "Header.record \"Ax1_2\""

end
