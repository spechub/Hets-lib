theory Functions_Functions
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"o_def\", \"id_def\", \"o_assoc\", \"id_neut\", \"inj\",
     \"surj\"]"

consts
X__o__X :: "('b => 'c partial) * ('a => 'b partial) => 'a => 'c partial"
X_id :: "'a => 'a partial" ("id''/'(_')" [3] 999)

axioms
o_def [rule_format] :
"ALL f.
 ALL g.
 X__o__X (f, g) =
 (% x. case g x of
       None => noneOp |
       Some Xc0 => f Xc0)"

id_def [rule_format] : "X_id = makePartial o (% x. x)"

theorem o_assoc :
"ALL f.
 ALL g.
 ALL h. X__o__X (f, X__o__X (g, h)) = X__o__X (X__o__X (f, g), h)"
apply (auto simp only: o_def)
(* (%x. option_case None f (option_case None g (h x))) = (%x. case h x of None => None | Some x => option_case None f (g x))*)
apply (rule ext)
apply (case_tac "h x")
apply (simp_all add:noneOp_def)
done

theorem id_neut : "ALL f'. X__o__X (f', X_id) = f'"
apply (auto simp only: o_def id_def)
apply (rule ext)
apply (case_tac "f' x")
apply (simp_all add: noneOp_def makePartial_def)
done


theorem inj  :
"ALL f'.
 X__o__X (f', f') = X_id -->
 (ALL x. ALL y. f' x =s= f' y --> x = y)"
apply (auto)
apply (subgoal_tac "option_case None fâ (fâ y) = Some y")
apply (drule_tac x = "x" in fun_cong)
apply (case_tac "fâ x")
apply (drule_tac[3] x = "y" in fun_cong)
apply (unfold strongEqualOp_def)
apply (simp)
apply (case_tac "fâ y")
apply (auto)
apply (unfold o_def id_def)
apply (unfold makePartial_def)
apply (simp)
apply (unfold noneOp_def)
apply (simp)
done


theorem surj  :
"ALL f'.
 X__o__X (f', f') = X_id --> (ALL x. EX y. f' y = makePartial x)"
apply (auto)
apply (subgoal_tac "option_case None fâ (fâ y) = Some y")
apply (drule_tac x = "x" in fun_cong)
apply (case_tac "f' x")
apply (drule_tac[3] x = "y" in fun_cong)
apply (unfold strongEqualOp_def)
apply (simp)
apply (case_tac "f' y")
apply (auto)
apply (unfold o_def id_def)
apply (unfold makePartial_def)
apply (simp)
apply (unfold noneOp_def)
apply (simp)
done


end
