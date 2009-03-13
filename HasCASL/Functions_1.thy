theory Functions_1
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

consts
"id" :: "'a => 'a option"  
"o_X" :: "(('b => 'c option) * ('a => 'b option)) => ('a => 'c option)" 


axioms
o_def: "apt (Some o_X) (pair (Some f) (Some g)) = (Some (% x . app (Some f) (app (Some g) (Some x))))"
id_def: "(Some id) = (Some (% x . (Some x)))"

lemmas o_def' = o_def [simplified]
lemmas id_def' = id_def [simplified]

declare o_def' [simp]
declare o_def [simp]
declare id_def' [simp]
declare id_def [simp]


theorem o_assoc: "apt (Some o_X) (pair (Some f) (apt (Some o_X) (pair (Some g) (Some h)))) = apt (Some o_X) (pair (apt (Some o_X) (pair (Some f) (Some g))) (Some h))"
apply (simp)
apply (rule ext)
apply (case_tac "h x")
apply (simp_all)
done

theorem id_neut: "apt (Some o_X) (pair (Some f') (Some id)) = (Some f')"
apply (simp)
done
theorem inj: "apt (Some o_X) (pair (Some f') (Some f')) = (Some id) ==> (! x :: 'a . ! y :: 'a . app (Some f') (Some x) = app (Some f') (Some y) --> (Some x) = (Some y))"
apply (auto)
apply (subgoal_tac "option_case None f' (f' y) = Some y")
apply (drule_tac x = "x" in fun_cong)
apply (case_tac "f' x")
apply (drule_tac[3] x = "y" in fun_cong)
apply (simp)
apply (case_tac "f' y")
apply (auto)
done

theorem surj: "apt (Some o_X) (pair (Some f') (Some f')) = (Some id) --> (! x :: 'a . ? y :: 'a . app (Some f') (Some y) = (Some x))"
apply (auto)
apply (rule_tac x = "the (f' x)" in exI)
apply (drule_tac x = "x" in fun_cong)
apply (case_tac "f' x")
apply (auto)
done

end
