theory Functions_gn_n3
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"Ax1\", \"Ax2\", \"Ax3\", \"Ax4\", \"Ax5\", \"Ax6\", \"Ax7\",
     \"Ax8\", \"Ax9\"]"

typedecl ('a1) Seq
typedecl X_Nat

consts
X_all :: "(nat => 'S partial) => ('S => bool) => bool" ("all''/'(_,/ _')" [3,3] 999)
X_concat :: "(nat => 'S partial) * (nat => 'S partial) => nat => 'S partial"
X_empty :: "(nat => 'S partial) => bool" ("empty''/'(_')" [3] 999)
X_even :: "nat => bool" ("even''/'(_')" [3] 999)
X_filter :: "(nat => 'S partial) => ('S => bool) => nat => 'S partial"
X_finite :: "(nat => 'S partial) => bool" ("finite''/'(_')" [3] 999)
X_h :: "(nat => 'S partial) => 'S partial" ("h/'(_')" [3] 999)
X_head :: "(nat => 'S partial) => 'S partial" ("head/'(_')" [3] 999)
X_length :: "(nat => 'S partial) => nat partial" ("length''/'(_')" [3] 999)
X_max :: "nat => nat => nat" ("max''/'(_,/ _')" [3,3] 999)
X_min :: "nat => nat => nat" ("min''/'(_,/ _')" [3,3] 999)
X_odd :: "nat => bool" ("odd''/'(_')" [3] 999)
X_pre :: "nat => nat partial" ("pre/'(_')" [3] 999)
X_suc :: "nat => nat" ("suc/'(_')" [3] 999)
nf :: "(nat => 'S partial) => nat => 'S partial"
tail :: "(nat => 'S partial) => nat => 'S partial"

axioms
Ax1 [rule_format] : "ALL s. head(s) = s 0"

Ax2 [rule_format] : "ALL s. tail s = (% x. s (x + 0))"

Ax3 [rule_format] : "ALL s. head(nf s) = h(s)"

Ax4 [rule_format] :
"ALL P. ALL s. nf (X_filter s P) = X_filter (nf s) P"

Ax5 [rule_format] :
"ALL P. ALL s. head(X_filter s P) =
  resOp (head(s), bool2partial (defOp (s 0) & P (makeTotal (s 0))))"

(*"ALL P.
 ALL s.
 head(X_filter s P) =
 (resOp
  (head(s), bool2partial (defOp (s 0) & P (makeTotal (s 0))))"*)


Ax6 [rule_format] :
"ALL P. ALL s. tail (X_filter s P) = X_filter (tail s) P"

Ax7 [rule_format] :
"ALL r.
 ALL s.
 h(s) = makePartial r =
 (EX X_n.
  s X_n = makePartial r & (ALL m. m < X_n --> ~ defOp (s m)))"

Ax8 [rule_format] :
"ALL s. finite'(s) = (EX X_n. ALL m. m > X_n --> ~ defOp (s m))"

Ax9 [rule_format] : "ALL s. empty'(s) = (ALL X_n. ~ defOp (s X_n))"

Ax10 [rule_format] :
"ALL s.
 ALL t.
 head(X_concat (s, t)) = (if ~ empty'(s) then head(s) else head(t))"

Ax11 [rule_format] :
"ALL s.
 ALL t.
 tail (X_concat (s, t)) =
 (if ~ empty'(s) then X_concat (tail s, t) else tail t)"

declare Ax1[simp]
lemmas Ax5' = Ax5 [simplified]

theorem coinduct: "(R s t --> (head(s)=head(t) & (R (tail s) (tail t)))) & R s t ==> s=t"
sorry

theorem restrict1 : "restrictOp (restrictOp a (defOp b)) c = restrictOp (restrictOp a c) (defOp (restrictOp b c))"
apply (case_tac c)
apply (simp add: restrictOp_def)
apply (simp add: restrictOp_def)
done

theorem restrict_trivial_rule[simp]: "b ==> restrictOp t b = t"
apply (simp add: restrictOp_def)
done

theorem restrict_trivial [simp]: "restrictOp t True = t"
apply (simp)
done

theorem restrict_assoc[simp] : "restrictOp a (defOp (restrictOp b c)) = restrictOp (restrictOp a (defOp b)) c"
apply (case_tac c)
apply (simp add: restrictOp_def)
apply (simp add: restrictOp_def noneOp_def defOp.simps)
sorry


theorem restrict_out[simp] : "restrictOp (t b) b = restrictOp (t True) b"
apply (case_tac "b")
apply (simp add: restrictOp_def)
apply (simp add: restrictOp_def)
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

(* Some more stuff about removing extraneous restrictions *)

theorem total_restrict2 [simp]: 
"(c ==> b) ==> restrictOp (t (makeTotal  (restrictOp a b))) c = 
	   restrictOp (t (makeTotal a)) c"
apply (simp add: makeTotal_def restrictOp_def defOp.simps undefinedOp_def)
done

theorem def_restrict [simp]:
"defOp (restrictOp a b) = (defOp a & b)"
apply (simp add:  restrictOp_def defOp.simps undefinedOp_def split: split_if)
done

theorem total_restrict [simp]: 
"restrictOp (t (makeTotal  (restrictOp a b))) (defOp (restrictOp a b)) = 
	   restrictOp (t (makeTotal a)) (defOp a & b)"
apply simp
done

lemma restrictOp_cong [cong]:
  "b = b' ==> (b' ==> a = a') ==> restrictOp a b = restrictOp a' b'"
  apply (simp add: restrictOp_def defOp.simps undefinedOp_def)
done


theorem defop_filter2[simp]: "((defOp (a 0)) & (P (makeTotal (a 0)))) = defOp(X_filter a P 0)"
apply (simp add: Ax5' bool2partial_def resOp_def)
done

lemma double_defop: "defOp(head(X_filter (X_filter a P) P)) = defOp(head(X_filter a P))"
apply (simp add: Ax5' resOp_def bool2partial_def del: defop_filter2)
apply (rule iffI)
apply (auto)
done

lemma double_defop2: "defOp( X_filter (X_filter a P) P 0) = defOp(X_filter a P 0)"
apply (simp only: Ax1[THEN sym])
apply (rule double_defop)
done

lemma double_filter[simp]: "head(X_filter (X_filter a P) P) = head(X_filter a P)"
(*apply (case_tac "defOp(a 0) & P(makeTotal (a 0))")*)
apply (simp only: Ax5 resOp_def bool2partial_def)
apply (auto)
apply (subst double_defop2)
apply (auto)
done

lemma double_filter2: "X_filter (X_filter a P) P 0 = X_filter a P 0"
apply (simp only: Ax1[THEN sym])
apply (rule double_filter)
done

theorem bisim1 : "(%x y. EX a. (x=X_filter a P) & y=(X_filter (X_filter a P) P)) s t ==> head(s)=head(t) & ((%x y. EX a. (x=X_filter a P) & y=(X_filter (X_filter a P) P)) (tail s) (tail t))"
apply (auto)
apply (simp add: double_filter2)
apply (rule_tac x="tail a" in exI)
apply (simp add: Ax6)
done


theorem filter_double : "ALL P. ALL s. X_filter s P=X_filter (X_filter s P) P"
apply (auto)
apply (rule_tac R="(%x y. EX a. (x=X_filter a P) & y=(X_filter (X_filter a P) P))" in coinduct)
apply (rule conjI)
apply (rule impI)
apply (rule bisim1)
apply (simp)
apply (rule_tac x="s" in exI)
apply (auto)
done

theorem bisim2: "(%x y. EX a. (x=nf(X_filter a P)) & (y=X_filter (nf a) P)) s t ==> head(s)=head(t) & ((%x y. EX a. (x=nf(X_filter a P)) & (y=X_filter (nf a) P)) (tail s) (tail t))"
apply (auto)
apply (subst Ax1[THEN sym])
apply (subst Ax3)
apply (subst Ax5')
apply (simp add: resOp_def bool2partial_def)
apply (subst Ax7)
apply (simp add: resOp_def bool2partial_def)
apply (frule exE)
sorry


theorem filter_nfcom: "ALL P. ALL s. nf (X_filter s P) = X_filter (nf s) P"
apply (auto)
apply (rule_tac R="(%x y. EX a. (x=nf(X_filter a P)) & (y=X_filter (nf a) P))" in coinduct)
apply (simp add: bisim2)
apply (rule_tac x="s" in exI)
apply (auto)
done



end
