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
 (% x. restrictOp ( f ((makeTotal o g) x)) (defOp (g x)))"

id_def [rule_format] : "X_id = makePartial o (% x. x)"

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
apply (simp add: restrictOp_def noneOp_def defOp.simps)
done

theorem restrict_out[simp] : "restrictOp (t b) b = restrictOp (t True) b"
apply (case_tac "b")
apply (simp add: restrictOp_def)
apply (simp add: restrictOp_def)
done

theorem mkpartial_cancel [simp]: "makeTotal(makePartial x) = x"
apply (simp add: makeTotal_def makePartial_def)
done

theorem defOp_trivial [simp]: "defOp(makePartial x) = True"
apply (simp add: makePartial_def makeTotal_def)
done


theorem o_assoc :
"X__o__X (f, X__o__X (g, h)) = X__o__X (X__o__X (f, g), h)"
apply (rule ext)
apply (simp add: o_def comp_def)
apply (subst restrict_out [of _ "defOp (h x)"]) back 
apply (simp)
done

theorem id_neut : "X__o__X (f', X_id) = f'"
by (simp add: o_def comp_def id_def)

theorem restrictOp_add_def: "(restrictOp f b) = (makePartial x) ==> b"
apply (simp add: makePartial_def restrictOp_def)
apply (simp only: noneOp_def)
apply (case_tac b)
apply (auto)
done


theorem restrictOp_mkpartial_defined: "(restrictOp f b) = (makePartial x) ==> f = (makePartial x)"
apply (simp add: makePartial_def restrictOp_def)
apply (simp only: noneOp_def)
apply (case_tac b)
apply (auto)
done

theorem inj  :
" X__o__X (f', f') = X_id ==>  f' x = f' y --> x = y"
apply (rule impI)
apply (drule_tac x = "x" in fun_cong)
apply (simp add: o_def comp_def id_def)
apply (frule_tac restrictOp_add_def)
apply (simp only: restrict_trivial)
apply (drule_tac x = "x" in fun_cong)

done


theorem surj  :
"ALL f'.
 X__o__X (f', f') = X_id --> (ALL x. EX y. f' y = makePartial x)"
done


end
