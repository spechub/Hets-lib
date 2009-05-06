theory Functions_MainHC2
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


theorem restrict1 : "restrictOp (restrictOp a (defOp b)) c = restrictOp (restrictOp a c) (defOp (restrictOp b c))"
apply (case_tac c)
apply (simp add: restrictOp_def)
apply (simp add: restrictOp_def)
done

theorem restrict_trivial [simp]: "restrictOp t True = t"
apply (simp add: restrictOp_def)
done

theorem restrict_assoc[simp] : "restrictOp a (defOp (restrictOp b c)) = restrictOp (restrictOp a (defOp b)) c"
apply (case_tac c)
apply (simp add: restrictOp_def)
apply (simp add: restrictOp_def noneOp_def defOp.simps undefinedOp_def)
done

theorem restrict_out[simp] : "restrictOp (t b) b = restrictOp (t True) b"
apply (case_tac "b")
apply (simp add: restrictOp_def)
apply (simp add: restrictOp_def)
done

theorem restrict_out2[simp] : "restrictOp (t b) (a&b) = restrictOp (t True) (a&b)"
apply (case_tac "b")
apply (simp add: restrictOp_def)
apply (simp add: restrictOp_def)
done

theorem restrict_out_general : "(b-->a) ==> (restrictOp (t a) b) = (restrictOp (t True) b)"
apply (case_tac "b")
apply (simp only: restrictOp_def)
apply (simp only: restrictOp_def)
apply (simp)
done


theorem mkpartial_cancel [simp]: "makeTotal(makePartial x) = x"
apply (simp add: makeTotal_def makePartial_def)
done

theorem mkpartial_cancel2 [simp]: "defOp(x) ==> makePartial(makeTotal x) = x"
apply (simp add: makeTotal_def makePartial_def)
apply (case_tac x)
apply (simp)
apply (simp)
done

theorem mkpartial_cancel3 [simp] : "((makePartial x) = (makePartial y)) = (x = y)"
apply (simp add: makePartial_def)
done


theorem defOp_trivial [simp]: "defOp(makePartial x) = True"
apply (simp add: makePartial_def makeTotal_def)
done

theorem restrictOp_add_def: "(restrictOp f b) = (makePartial x) ==> b"
apply (simp add: makePartial_def restrictOp_def)
apply (simp only: undefinedOp_def)
apply (case_tac b)
apply (auto)
done

theorem restrictOp_trivial2[simp] : "restrictOp p (defOp p) = p"
apply (simp only: restrictOp_def)
apply (case_tac "p")
apply (simp add: undefinedOp_def defOp.simps)
apply (simp add: undefinedOp_def defOp.simps)
done


theorem restrictOp_mkpartial_defined: "(restrictOp f b) = (makePartial x) ==> f = (makePartial x)"
apply (simp add: makePartial_def restrictOp_def)
apply (simp only: undefinedOp_def)
apply (case_tac b)
apply (auto)
done

theorem restrictOp_outbool[simp] : "(restrictOp (restrictOp a b) c) = (restrictOp a (b & c))"
apply (case_tac "c")
apply (simp add: restrictOp_def)
apply (simp add: restrictOp_def)
done


theorem X3comp_assoc1  :
"ALL f.
 ALL g. ALL h. comp3 ((h, g), f) = X__o__X (X__o__X (h, g), f)"
apply (auto)
apply (rule ext)
apply (simp add: o_def X3comp_def lift2partial_def)
apply (subst restrict_out2)
apply (simp)
done
(*restrictOp (t b) (a&b) = restrictOp (t True) (a&b)*)

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
apply (simp add: o_def X3comp_def lift2partial_def)
(* "restrictOp (t b) (a&b) = restrictOp (t True) (a&b)" *)
apply (subst restrict_out2)
apply (simp)
done

theorem id_neut [rule_format] : "ALL f'. X__o__X (f', X_id) = f'"
apply (simp add: o_def comp_def id_def lift2partial_def)
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
apply (simp)
apply (simp (no_asm_simp) add: o_def comp_def id_def)
done

theorem surj  :
"ALL f'.
 X__o__X (f', f') = X_id --> (ALL x. EX y. f' y = makePartial x)"
apply (auto)
apply (rule_tac x="makeTotal (f' x)" in exI)
apply (drule_tac x = "x" in fun_cong)
apply (simp add: lift2partial_def o_def comp_def id_def restrictOp_mkpartial_defined)
done

end