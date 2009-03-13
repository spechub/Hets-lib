theory Functions_Functions
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"o_def\", \"id_def\", \"X3comp_def\", \"X3comp_assoc1\",
     \"X3comp_assoc2\", \"o_assoc\", \"id_neut\", \"inj\", \"surj\"]"

consts
X__o__X :: "('b => 'c partial) * ('a => 'b partial) => 'a => 'c partial"
X_id :: "'a => 'a partial" ("id''/'(_')" [3] 999)
comp3 :: "(('c => 'd partial) * ('b => 'c partial)) * ('a => 'b partial) => 'a => 'd partial"

axioms
o_def [rule_format] :
"ALL f. ALL g. X__o__X (g, f) = (% x. lift2partial g (f x))"

id_def [rule_format] : "X_id = makePartial o (% x. x)"

X3comp_def [rule_format] :
"ALL f.
 ALL g.
 ALL h.
 comp3 ((h, g), f) = (% x. lift2partial h (lift2partial g (f x)))"


theorem X3comp_assoc1  :
"ALL f.
 ALL g. ALL h. comp3 ((h, g), f) = X__o__X (X__o__X (h, g), f)"
apply (auto)
apply (rule ext)
apply (simp only: o_def X3comp_def lift2partial_def restrictOp_def)
apply (case_tac "defOp (f x)")
apply (simp)
apply (simp add: undefinedOp_def)
done

theorem X3comp_assoc2  :
"ALL f.
 ALL g. ALL h. comp3 ((h, g), f) = X__o__X (h, X__o__X (g, f))"
apply (auto)
apply (rule ext)
apply (simp add: o_def X3comp_def)
done

theorem o_assoc :
"ALL f.
 ALL g.
 ALL h. X__o__X (h, X__o__X (g, f)) = X__o__X (X__o__X (h, g), f)"
apply (auto)
apply (rule ext)
apply (simp add: o_def X3comp_def lift2partial_def restrictOp_def)
apply (simp add: undefinedOp_def)
done

theorem mkpartial_cancel [simp]: "makeTotal(makePartial x) = x"
apply (simp add: makeTotal_def makePartial_def)
done

theorem defOp_trivial [simp]: "defOp(makePartial x) = True"
apply (simp add: makePartial_def makeTotal_def)
done


theorem mkpartial_cancel3 [simp] : "((makePartial x) = (makePartial y)) = (x = y)"
apply (simp add: makePartial_def)
done

theorem mkpartial_cancel4 [simp]: "(undefinedOp = makePartial x) = False"
apply (simp add: undefinedOp_def makePartial_def)
done

theorem id_neut [rule_format] : "ALL f'. X__o__X (f', X_id) = f'"
apply (auto)
apply (rule ext)
apply (simp add: o_def comp_def id_def lift2partial_def restrictOp_def)
done

theorem inj  :
"ALL f'.
 X__o__X (f', f') = X_id --> (ALL x. ALL y. f' x = f' y --> x = y)"
apply (auto)
apply (rule injD [of X_id])
apply (rule injI)
apply (simp add: o_def comp_def id_def)
apply (drule_tac sym)
apply (frule_tac x = "x" in fun_cong)
apply (drule_tac x = "y" in fun_cong)
apply (simp add: lift2partial_def restrictOp_def o_def)
done

theorem surj  :
"ALL f'.
 X__o__X (f', f') = X_id --> (ALL x. EX y. f' y = makePartial x)"
apply (auto)
apply (rule_tac x="makeTotal (f' x)" in exI)
apply (drule_tac x = "x" in fun_cong)
apply (simp add: lift2partial_def o_def comp_def id_def restrictOp_def)
apply (case_tac "defOp (f' x)")
apply (simp)
apply (simp)
done

end