theory PartialityTest_PartMinus_E1
imports "$HETS_ISABELLE_LIB/MainHC" "$HETS_LIB/Isabelle/RestrictOpProps"
uses "$HETS_ISABELLE_LIB/prelude"
begin

ML "Header.initialize [\"Ax1\", \"Ax2\", \"Ax3\", \"Ax1_4\"]"

typedecl X_Nat

consts
X__XGtXEq__X :: "X_Nat => X_Nat => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XMinusXQuest__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ -?/ _)" [54,54] 52)
X__XPlus__X :: "X_Nat => X_Nat => X_Nat" ("(_/ +''/ _)" [54,54] 52)
X_even :: "X_Nat => bool" ("even''/'(_')" [3] 999)
X_odd :: "X_Nat => bool" ("odd''/'(_')" [3] 999)

axioms
Ax1 [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). defOp (m -? X_n) = (m >=' X_n)"

Ax2 [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 ALL (r :: X_Nat). m -? X_n = makePartial r = (m = r +' X_n)"

Ax3 [rule_format] :
"ALL (a :: X_Nat). ALL (b :: X_Nat). a +' b = b +' a"

declare Ax1 [simp]

lemma truesimp: "(True & True) = True" 
by (auto)


theorem Ax1_4 :
"ALL (a :: X_Nat).
 ALL (b :: X_Nat).
 ALL (c :: X_Nat).
 ((defOp (c -? a) &
   defOp (restrictOp (b -? makeTotal (c -? a)) (defOp (c -? a)))) &
  defOp
  (restrictOp (a -? makeTotal (b -? makeTotal (c -? a)))
   (defOp (b -? makeTotal (c -? a)) & defOp (c -? a)))) &
 defOp (c -? b) -->
 restrictOp (a -? makeTotal (b -? makeTotal (c -? a)))
 (defOp (b -? makeTotal (c -? a)) & defOp (c -? a)) =
 c -? b"
apply (rule allI)+
apply (rule impI)
apply (frule conjunct1, drule conjunct2)+
apply (simp only: restrict_trivial truesimp)
apply (frule defOp_implies_makePartial)
apply (erule exE)
apply (simp only:)
apply (subst Ax2)
apply (rule 
apply (simp only: truesimp)
apply (frule conjunct1)
apply (drule conjunct2)
apply (frule conjunct1)
apply (drule conjunct2)

apply (clarify)

apply (simp only: )
apply (subst (asm) restrict_trivial)
apply (clarify)
apply (simp)


ML "Header.record \"Ax1_4\""

end
