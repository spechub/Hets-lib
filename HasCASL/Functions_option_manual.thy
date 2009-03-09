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

theorem restrict_trivial : "restrictOp t True = t"
apply (simp add: restrictOp_def)
done

theorem restrict_assoc : "restrictOp a (defOp (restrictOp b c)) = restrictOp (restrictOp a (defOp b)) c"
apply (case_tac c)
apply (simp add: restrictOp_def)
apply (simp add: restrictOp_def noneOp_def defOp.simps)
done

theorem restrict_out : "restrictOp (t b) b = restrictOp (t True) b"
apply (case_tac "b")
apply (simp add: restrictOp_def)
apply (simp add: restrictOp_def)
done

theorem o_assoc :
"X__o__X (f, X__o__X (g, h)) = X__o__X (X__o__X (f, g), h)"
apply (rule ext)
apply (simp only: o_def comp_def)
apply (subst restrict_assoc)
apply (subst restrict_out [of _ "defOp (h x)"]) back 
apply (subst restrictOp_def)
apply (simp)
done

theorem id_neut : "ALL f'. X__o__X (f', X_id) = f'"
done


theorem inj  :
"ALL f'.
 X__o__X (f', f') = X_id -->
 (ALL x. ALL y. f' x =s= f' y --> x = y)"
done


theorem surj  :
"ALL f'.
 X__o__X (f', f') = X_id --> (ALL x. EX y. f' y = makePartial x)"
done


end
