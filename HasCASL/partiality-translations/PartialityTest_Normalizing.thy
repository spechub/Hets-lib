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
 restrictOp (f(x, makeTotal (f(y, z)))) (defOp (f(y, z))) =
 restrictOp (f(makeTotal (f(x, y)), z)) (defOp (f(x, y)))"

lemma assoc_dom : "defOp (f(x, y)) & defOp (f(y, z)) ==> 
  (defOp (f(x, makeTotal (f(y, z)))) & defOp (f(y, z))) = 
  (defOp (f(makeTotal (f(x, y)), z)) & defOp (f(x, y)))"
apply (frule Ax1)
apply (simp)
done

lemma assoc_eq : "defOp (f(x, y)) & defOp (f(y, z)) ==> 
  f(x, makeTotal (f(y, z))) = f(makeTotal (f(x, y)), z)"
apply (frule Ax1)
apply (simp)
done

theorem Ax1_2 :
"ALL (w :: a).
 ALL (x :: a).
 ALL (y :: a).
 ALL (z :: a).
 defOp (restrictOp (f(x, makeTotal (f(y, z)))) (defOp (f(y, z)))) &
 defOp
 (restrictOp (f(y, makeTotal (f(z, w)))) (defOp (f(z, w)))) -->
 restrictOp (f(makeTotal (f(x, makeTotal (f(y, z)))), w))
 (defOp (f(x, makeTotal (f(y, z)))) & defOp (f(y, z))) =
 restrictOp (f(x, makeTotal (f(y, makeTotal (f(z, w))))))
 (defOp (f(y, makeTotal (f(z, w)))) & defOp (f(z, w)))"
apply (auto)
apply (simp add: assoc_eq assoc_dom)
done


ML "Header.record \"Ax1_2\""

end
