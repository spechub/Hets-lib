theory PartialityTest_PartMinus_E1
imports "$HETS_ISABELLE_LIB/MainHC" "$HETS_LIB/Isabelle/RestrictOpProps"
uses "$HETS_ISABELLE_LIB/prelude"
begin

ML "Header.initialize
    [\"ga_select_pre\", \"Ax3\", \"Ax4\", \"Ax5\", \"Ax6\", \"Ax1\",
     \"Ax2\", \"Ax3_10\", \"Ax4_7\", \"Ax5_9\", \"Ax6_8\", \"Ax7\",
     \"Ax8\", \"Ax9\"]"


consts
X__XMinusXQuest__X :: "nat => nat => nat partial" ("(_/ -?/ _)" [54,54] 52)
X_pre :: "nat => nat partial" ("pre/'(_')" [3] 999)

axioms
ga_select_pre [rule_format] :
"ALL (x_1 :: nat). pre(Suc(x_1)) = makePartial x_1"

Ax3 [rule_format] : "0 -? 0 = makePartial 0"

Ax4 [rule_format] :
"ALL (x :: nat). Suc(x) -? 0 = makePartial (Suc(x))"

Ax5 [rule_format] : "ALL (x :: nat). ~ defOp (0 -? Suc(x))"

Ax6 [rule_format] :
"ALL (x :: nat). ALL (y :: nat). Suc(x) -? Suc(y) = x -? y"

declare ga_select_pre [simp]
declare Ax3 [simp]
declare Ax4 [simp]
declare Ax5 [simp]
declare Ax6 [simp]

theorem Ax1 :
"ALL (a :: nat).
 ALL (b :: nat).
 ALL (c :: nat).
 defOp
 (restrictOp (a -? makeTotal (b -? makeTotal (c -? a)))
  (defOp (b -? makeTotal (c -? a)) & defOp (c -? a))) -->
 defOp (c -? a)"
by (auto)

ML "Header.record \"Ax1\""

theorem Ax2 :
"ALL (a :: nat).
 ALL (b :: nat).
 ALL (c :: nat).
 defOp
 (restrictOp (a -? makeTotal (b -? makeTotal (c -? a)))
  (defOp (b -? makeTotal (c -? a)) & defOp (c -? a))) -->
 defOp (restrictOp (b -? makeTotal (c -? a)) (defOp (c -? a)))"
by (auto)

ML "Header.record \"Ax2\""

theorem Ax3_10 :
"ALL (a :: nat).
 ALL (b :: nat).
 ALL (c :: nat).
 defOp (restrictOp (a -? makeTotal (b -? c)) (defOp (b -? c))) -->
 defOp (b -? c)"
by (auto)

ML "Header.record \"Ax3_10\""

theorem Ax4_7 : "ALL (a :: nat). a -? a = makePartial 0"
apply (rule allI)
apply (induct_tac a)
by (auto)

ML "Header.record \"Ax4_7\""

lemma sucneutr [simp]: "(a -? 0) = makePartial a"
apply (induct_tac a)
apply (simp)
apply (simp)
done

lemma partminusundef [simp]: "~(defOp(a-?Suc(a)))"
apply (induct_tac a)
apply (simp)
apply (simp)
done


lemma test2 [simp]: "((z+a)-?a)=makePartial z"
apply (induct_tac a)
apply (auto)
done

lemma test4 [rule_format]:  "(!n.(defOp(a-? Suc(n)) --> (defOp(a -? n)))) & (!n.(defOp(a-?n) --> defOp(Suc(a)-?n)))"
apply (induct_tac a)
apply (simp)
apply (rule allI)
apply (case_tac n)
apply (simp)
apply (simp)
apply (induct_tac n)
apply (rule conjI, rule allI)
apply (simp)
apply (case_tac na)
apply (simp)
apply (simp)
apply (rule allI)
apply (case_tac na)
apply (simp)
apply (simp)
apply (case_tac nat)
apply (simp)
apply (simp)
apply (simp)
apply (rule allI)
apply (case_tac nb)
apply (simp)
apply (simp)
done
 

lemma test3: "defOp(a-?b) = (a>=b)"
apply (induct_tac b)
apply (simp)
apply (case_tac "n>a")
apply (simp add: test4)

apply (simp)
apply (case_tac "defOp(a -? Suc(n))")
apply (subst (asm) test4)
apply (simp)
apply (case_tac "n=a")
apply (simp)
apply (simp)
apply (case_tac "n=a")
apply (simp)
apply (simp)

theorem Ax5_9 :
"ALL (a :: nat).
 ALL (b :: nat).
 ALL (c :: nat).
 defOp (a -? b) -->
 restrictOp (makePartial (c + makeTotal (a -? b)))
 (defOp (a -? b)) =
 (c + a) -? b"

apply (rule allI)+
apply (simp)
apply (induct_tac b)
apply (simp add: sucneutr)
apply (induct_tac a)
apply (simp)
apply (simp)
apply (auto)
 
by (auto)

ML "Header.record \"Ax5_9\""

theorem Ax6_8 :
"ALL (a :: nat).
 ALL (b :: nat).
 ALL (c :: nat).
 defOp (a -? b) & defOp (b -? c) -->
 restrictOp (makePartial (makeTotal (a -? b) +' makeTotal (b -? c)))
 (defOp (a -? b) & defOp (b -? c)) =
 a -? c"
by (auto)

ML "Header.record \"Ax6_8\""

theorem Ax7 :
"ALL (a :: nat).
 ALL (b :: nat).
 ALL (c :: nat).
 defOp (restrictOp (a -? makeTotal (b -? c)) (defOp (b -? c))) -->
 restrictOp (a -? makeTotal (b -? c)) (defOp (b -? c)) =
 (a +' c) -? b"
by (auto)

ML "Header.record \"Ax7\""

theorem Ax8 :
"ALL (a :: nat).
 ALL (b :: nat).
 ALL (c :: nat).
 defOp
 (restrictOp (a -? makeTotal (b -? makeTotal (c -? a)))
  (defOp (b -? makeTotal (c -? a)) & defOp (c -? a))) -->
 defOp (c -? b)"
by (auto)

ML "Header.record \"Ax8\""

theorem Ax9 :
"ALL (a :: nat).
 ALL (b :: nat).
 ALL (c :: nat).
 defOp
 (restrictOp (a -? makeTotal (b -? makeTotal (c -? a)))
  (defOp (b -? makeTotal (c -? a)) & defOp (c -? a))) -->
 restrictOp (a -? makeTotal (b -? makeTotal (c -? a)))
 (defOp (b -? makeTotal (c -? a)) & defOp (c -? a)) =
 c -? b"
by (auto)

ML "Header.record \"Ax9\""

end
