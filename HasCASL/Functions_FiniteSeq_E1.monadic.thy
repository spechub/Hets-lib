theory Functions_FiniteSeq_E1
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"Ax1\", \"Ax2\", \"Ax3\", \"Ax4\", \"Ax5\", \"Ax6\", \"Ax7\",
     \"Ax8\", \"Ax9\", \"Ax10\", \"Ax11\", \"Ax12\", \"Ax13\", \"Ax14\",
     \"Ax15\", \"Ax1_1\", \"Ax2_1\", \"Ax3_1\"]"

typedecl ('a1) Seq

consts
X_all :: "(nat => 'S partial) => ('S => bool) => bool" ("all''/'(_,/ _')" [3,3] 999)
X_concat :: "(nat => 'S partial) * (nat => 'S partial) => nat => 'S partial"
X_empty :: "(nat => 'S partial) => bool" ("empty''/'(_')" [3] 999)
X_filter :: "(nat => 'S partial) => ('S => bool) => nat => 'S partial"
X_finite :: "(nat => 'S partial) => bool" ("finite''/'(_')" [3] 999)
X_head :: "(nat => 'S partial) => 'S partial" ("head/'(_')" [3] 999)
X_length :: "(nat => 'S partial) => nat partial" ("length''/'(_')" [3] 999)
X_max :: "nat => nat => nat" ("max''/'(_,/ _')" [3,3] 999)
X_minX1 :: "nat => nat => nat" ("min''/'(_,/ _')" [3,3] 999)
X_minX2 :: "(nat => bool) => nat partial" ("min''''/'(_')" [3] 999)
X_nfh :: "(nat => 'S partial) => 'S partial" ("nfh/'(_')" [3] 999)
X_start :: "(nat => 'S partial) => nat partial" ("start/'(_')" [3] 999)
nf :: "(nat => 'S partial) => nat => 'S partial"
nft :: "(nat => 'S partial) => nat => 'S partial"
tail :: "(nat => 'S partial) => nat => 'S partial"

axioms
Ax1 [rule_format] : "ALL Q. defOp (min''(Q)) --> (EX m. Q m)"

Ax2 [rule_format] :
"ALL Q.
 (EX m. Q m) -->
 min''(Q) =
 (if Q 0 then makePartial 0 else min''(% m. Q (m + 1)))"

Ax3 [rule_format] : "ALL s. start(s) = min''(% m. defOp (s m))"

Ax4 [rule_format] : "ALL s. head(s) = s 0"

Ax5 [rule_format] : "ALL s. tail s = (% x. s (x + 1))"

Ax6 [rule_format] : "ALL s. head(nf s) = nfh(s)"

Ax7 [rule_format] : "ALL s. tail (nf s) = nf (nft s)"

Ax8 [rule_format] :
"ALL P.
 ALL s.
 head(X_filter s P) =
 (resOp
  (head(s),
   bool2partial (defOp (head(s)) & P (makeTotal (head(s))))))"

Ax9 [rule_format] :
"ALL P. ALL s. tail (X_filter s P) = X_filter (tail s) P"
(*
Ax10 [rule_format] :
"ALL s.
 nfh(s) = lift2partial s (start(s)) 

Ax11 [rule_format] :
"ALL s.
 nft s =
 (% k.  lift2partial s (mapPartial (X__XPlus__X (k + 1)) (start(s))))

Ax12 [rule_format] :
"ALL s. finite'(s) = (EX X_n. ALL m. m > X_n --> ~ defOp (s m))"

Ax13 [rule_format] : "ALL s. empty'(s) = (ALL m. ~ defOp (s m))"

Ax14 [rule_format] :
"ALL s.
 ALL t.
 head(X_concat (s, t)) = (if ~ empty'(s) then head(s) else head(t))"

Ax15 [rule_format] :
"ALL s.
 ALL t.
 tail (X_concat (s, t)) =
 (if ~ empty'(s) then X_concat (tail s, t) else tail t)"
*)

declare Ax6 [simp]

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


lemma double_defop: "defOp(head(X_filter (X_filter a P) P)) = defOp(head(X_filter a P))"
apply (simp add: Ax8 resOp_def bool2partial_def)
apply (auto)
done

theorem defop_filter2: "((defOp (head(a))) & (P (makeTotal (head(a))))) = defOp(head(X_filter a P))"
apply (simp add: Ax8 bool2partial_def resOp_def lift2bool_def)
done

lemma double_filter_head[simp]: "head(X_filter (X_filter a P) P) = head(X_filter a P)"
(*apply (case_tac "defOp(a 0) & P(makeTotal (a 0))")*)
apply (simp add: Ax8 resOp_def bool2partial_def)
apply (simp add: defop_filter2 cong: conj_cong)
done

theorem coinduct: "[|R u v ==> (head(u)=head(v) & (R (tail u) (tail v)));  R u v|] ==> u=v"
apply (rule ext)
apply (induct_tac x)
sorry



theorem Ax2_1 :
"ALL P. ALL s. X_filter s P=X_filter (X_filter s P) P"
apply (auto)
apply (rule_tac R="(%x y. EX a. (x=X_filter a P) & y=(X_filter (X_filter a P) P))" in coinduct)
apply (auto)
apply (rule_tac x="tail a" in exI)
apply (simp add: Ax9)
done


theorem Ax1_1 :
"ALL P. ALL s. nf (X_filter s P) = X_filter (nf s) P"
by (auto)

ML "Header.record \"Ax1_1\""

ML "Header.record \"Ax2_1\""

theorem Ax3_1 : "ALL s. defOp (nfh(s)) = (~ empty'(s))"
by (auto)

ML "Header.record \"Ax3_1\""

end
