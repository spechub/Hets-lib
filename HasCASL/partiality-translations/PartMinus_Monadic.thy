theory PartialityTest_PartMinus_E1 
imports "$HETS_ISABELLE_LIB/MainHC" "$HETS_LIB/Isabelle/RestrictOpProps"
uses "$HETS_ISABELLE_LIB/prelude"
begin

ML "Header.initialize
    [\"ga_select_pre\", \"Ax3\", \"Ax4\", \"Ax5\", \"Ax6\", \"Ax1\",
     \"Ax2\", \"Ax3_8\", \"Ax4_7\"]"

datatype X_Nat = X0 ("0''") | X_suc "X_Nat" ("suc/'(_')" [3] 999)

consts
X__XGtXEq__X :: "X_Nat => X_Nat => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XMinusXQuest__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ -?/ _)" [54,54] 52)
X__XPlus__X :: "X_Nat => X_Nat => X_Nat" ("(_/ +''/ _)" [54,54] 52)
X_pre :: "X_Nat => X_Nat partial" ("pre/'(_')" [3] 999)

axioms
ga_select_pre [rule_format] :
"ALL (x_1 :: X_Nat). pre(suc(x_1)) = makePartial x_1"

Ax3 [rule_format] : "0' -? 0' = makePartial 0'"

Ax4 [rule_format] :
"ALL (x :: X_Nat). suc(x) -? 0' = makePartial (suc(x))"

Ax5 [rule_format] : "ALL (x :: X_Nat). ~ defOp (0' -? suc(x))"

Ax6 [rule_format] :
"ALL (x :: X_Nat). ALL (y :: X_Nat). suc(x) -? suc(y) = x -? y"

declare ga_select_pre [simp]
declare Ax3 [simp]
declare Ax4 [simp]
declare Ax5 [simp]
declare Ax6 [simp]

theorem Ax1 :
"ALL (a :: X_Nat).
 ALL (b :: X_Nat).
 ALL (c :: X_Nat).
 defOp
 (lift2partial (X__XMinusXQuest__X a)
  (lift2partial (X__XMinusXQuest__X b) (c -? a))) -->
 defOp (c -? a)"
apply (auto)
sorry

ML "Header.record \"Ax1\""

theorem Ax2 :
"ALL (a :: X_Nat).
 ALL (b :: X_Nat).
 ALL (c :: X_Nat).
 defOp
 (lift2partial (X__XMinusXQuest__X a)
  (lift2partial (X__XMinusXQuest__X b) (c -? a))) -->
 defOp (lift2partial (X__XMinusXQuest__X b) (c -? a))"
apply (auto)
sorry


ML "Header.record \"Ax2\""

theorem Ax3_8 :
"ALL (a :: X_Nat).
 ALL (b :: X_Nat).
 ALL (c :: X_Nat).
 defOp
 (lift2partial (X__XMinusXQuest__X a)
  (lift2partial (X__XMinusXQuest__X b) (c -? a))) -->
 defOp (c -? b)"
by (auto)

ML "Header.record \"Ax3_8\""

theorem Ax4_7 :
"ALL (a :: X_Nat).
 ALL (b :: X_Nat).
 ALL (c :: X_Nat).
 defOp
 (lift2partial (X__XMinusXQuest__X a)
  (lift2partial (X__XMinusXQuest__X b) (c -? a))) -->
 lift2partial (X__XMinusXQuest__X a)
 (lift2partial (X__XMinusXQuest__X b) (c -? a)) =
 c -? b"
by (auto)

ML "Header.record \"Ax4_7\""

end
