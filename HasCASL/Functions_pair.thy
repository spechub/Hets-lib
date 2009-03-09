theory Functions_Functions
imports "$HETS_LIB/Isabelle/MainHCPairs"
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
 (% x. let (Xb1, Xc0) = g x in if Xb1 then f Xc0 else noneOp)"

id_def [rule_format] : "X_id = makePartial o (% x. x)"

lemma strong_equality : "!! (t::'a partial) (s::'a partial) . (t =s= s)  =  (! x . ((t = makePartial x) <-> (s = makePartial x)))"
apply (rule iffI)
defer
apply (unfold makePartial_def)
apply (unfold strongEqualOp_def)
apply (auto)
done

theorem o_assoc :
"ALL f.
 ALL g.
 ALL h. X__o__X (f, X__o__X (g, h)) = X__o__X (X__o__X (f, g), h)"
apply (simp only: o_def id_def)
apply (auto)
apply (rule ext)
apply (case_tac "h x")
apply (simp add: noneOp_def)
done





theorem id_neut : "ALL f'. X__o__X (f', X_id) = f'"
apply (auto simp only: o_def id_def)
apply (rule ext)
apply (case_tac "f' x")
apply (simp_all add: noneOp_def makePartial_def)
done


theorem surj  :
"ALL f'.
 X__o__X (f', f') = X_id --> (ALL x. EX y. f' y = makePartial x)"
apply (auto)
apply (subgoal_tac "(f' (snd (f' y))) =(makePartial y)")
apply (unfold o_def id_def)
apply (unfold makePartial_def)
apply (unfold noneOp_def)
apply (case_tac "f' x")
apply (auto)


apply (subgoal_tac "option_case None f' (f' y) = Some y")
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


theorem inj  :
"ALL f'.
 X__o__X (f', f') = X_id -->
 (ALL x. ALL y. f' x =s= f' y --> x = y)"

apply (auto)
apply (subst (asm) strong_equality)
apply (drule_tac x = "x" in fun_cong)
apply (case_tac "f' x")
apply (simp)
apply (case_tac "f' y")
apply (auto)
apply (unfold o_def id_def)
apply (unfold makePartial_def)
apply (simp)
apply (unfold noneOp_def)
apply (unfold makePartial_def)
apply (auto)
done

end
