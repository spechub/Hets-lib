theory PartialityTest_PartMinus_E1
imports "$HETS_ISABELLE_LIB/MainHC" "$HETS_LIB/Isabelle/RestrictOpProps"
uses "$HETS_ISABELLE_LIB/prelude"
begin

ML "Header.initialize
    [\"ga_select_pre\", \"Ax3\", \"Ax4\", \"Ax5\", \"Ax6\", \"Ax1\",
     \"Ax2\", \"Ax3_8\", \"Ax4_7\"]"


consts
X__XMinusXQuest__X :: "nat => nat => nat partial" ("(_/ -?/ _)" [54,54] 52)

axioms
Ax3 [rule_format] : "0 -? 0 = makePartial 0"

Ax4 [rule_format] :
"ALL (x :: nat). suc(x) -? 0 = makePartial (suc(x))"

Ax5 [rule_format] : "ALL (x :: nat). ~ defOp (0 -? suc(x))"

Ax6 [rule_format] :
"ALL (x :: nat). ALL (y :: nat). suc(x) -? suc(y) = x -? y"

declare Ax3 [simp]
declare Ax4 [simp]
declare Ax5 [simp]
declare Ax6 [simp]

theorem Ax1 :
"defOp
 (restrictOp (a -? makeTotal (b -? makeTotal (c -? a)))
  (defOp (b -? makeTotal (c -? a)) & defOp (c -? a))) ==>
 defOp (c -? a)"
apply (auto)
done

ML "Header.record \"Ax1\""

theorem Ax2 :
"defOp
 (restrictOp (a -? makeTotal (b -? makeTotal (c -? a)))
  (defOp (b -? makeTotal (c -? a)) & defOp (c -? a))) ==>
 defOp (restrictOp (b -? makeTotal (c -? a)) (defOp (c -? a)))"
apply (auto)
done


ML "Header.record \"Ax2\""

theorem Ax3_8 :
"ALL (a :: nat).
 ALL (b :: nat).
 ALL (c :: nat).
 defOp
 (restrictOp (a -? makeTotal (b -? makeTotal (c -? a)))
  (defOp (b -? makeTotal (c -? a)) & defOp (c -? a))) -->
 defOp (c -? b)"
apply (rule allI)+
apply (rule impI)+
sorry

ML "Header.record \"Ax3_8\""

lemma defpartminus1 [simp]: "defOp(c -? 0)"
apply (induct_tac c)
apply (simp add: Ax3)
apply (auto)
done


lemma defpartminus: "defOp(c -? b) = (c>=b)"
apply (induct_tac b)
apply (simp)
apply (auto)
sorry

theorem Ax4_7 :
"ALL (a :: nat).
 ALL (b :: nat).
 ALL (c :: nat).
 defOp
 (restrictOp (a -? makeTotal (b -? makeTotal (c -? a)))
  (defOp (b -? makeTotal (c -? a)) & defOp (c -? a))) -->
 restrictOp (a -? makeTotal (b -? makeTotal (c -? a)))
 (defOp (b -? makeTotal (c -? a)) & defOp (c -? a)) =
 c -? b"
apply (rule allI)+
sorry

ML "Header.record \"Ax4_7\""

end
