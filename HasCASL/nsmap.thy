theory nsmap_theory
imports "$HETS_LIB/Isabelle/MainHC" "List"
uses "$HETS_LIB/Isabelle/prelude"
begin

consts
X_all :: "('a => bool) => 'a list => bool"
X_map :: "('a => 'b partial) => 'a list => 'b list partial"
nsMap :: "('a => 'b partial) => 'a list => 'b partial list"
X_filter :: "'a list => ('a => bool) => 'a list"

axioms 
Ax1 [rule_format] : "ALL f. X_map f [] = makePartial []"

(*nsMap_nil : "nsMap f nil = nil"
nsMap_cons : "nsMap f (cons x l) = cons (f x) (nsMap f l)"*)

Ax2 [rule_format] :
"ALL f.
 ALL l.
 ALL x.
 X_map f (Cons x l) =
 restrictOp
 (makePartial (Cons (makeTotal (f x)) (makeTotal (X_map f l))))
 (defOp (f x) & defOp (X_map f l))"

Ax3 [rule_format] : "ALL P. X_all P nil"

Ax4 [rule_format] :
"ALL P. ALL l. ALL x. X_all P (Cons x l) = (P x & X_all P l)"

Ax5 [rule_format] :
"ALL P.
 ALL s.
 (X_filter (Cons x l) P) = (if (P x) then (Cons x (X_filter l P)) else (Cons x (X_filter l P)))"

Ax6 [rule_format] :
"ALL P. ALL s. X_filter [] P = []"

theorem restrict1 : "restrictOp (restrictOp a (defOp b)) c = restrictOp (restrictOp a c) (defOp (restrictOp b c))"
apply (case_tac c)
apply (simp add: restrictOp_def)
apply (simp add: restrictOp_def)
done

theorem restrict_trivial_rule[simp]: "b ==> restrictOp u b = u"
apply (simp add: restrictOp_def)
done

theorem restrict_trivial [simp]: "restrictOp u True = u"
apply (simp)
done

theorem restrict_assoc[simp] : "restrictOp a (defOp (restrictOp b c)) = restrictOp (restrictOp a (defOp b)) c"
apply (case_tac c)
apply (simp add: restrictOp_def)
apply (simp add: restrictOp_def noneOp_def defOp.simps)
sorry


theorem restrict_out[simp] : "restrictOp (u b) b = restrictOp (u True) b"
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
"(c ==> b) ==> restrictOp (u (makeTotal  (restrictOp a b))) c = 
	   restrictOp (u (makeTotal a)) c"
apply (simp add: makeTotal_def restrictOp_def defOp.simps undefinedOp_def)
done

theorem def_restrict [simp]:
"defOp (restrictOp a b) = (defOp a & b)"
apply (simp add:  restrictOp_def defOp.simps undefinedOp_def split: split_if)
done

theorem total_restrict [simp]: 
"restrictOp (u (makeTotal  (restrictOp a b))) (defOp (restrictOp a b)) = 
	   restrictOp (u (makeTotal a)) (defOp a & b)"
apply simp
done

lemma restrictOp_cong [cong]:
  "b = b' ==> (b' ==> a = a') ==> restrictOp a b = restrictOp a' b'"
  apply (simp add: restrictOp_def defOp.simps undefinedOp_def)
done



lemma test: "((restrictOp a c) = (restrictOp b c)) = (c --> (a = b))"
apply (simp add: restrictOp_def)
done

lemma res_overlap[simp]: "restrictOp (restrictOp a b) c = restrictOp a (b & c)"
apply (simp add: restrictOp_def)
done

(*theorem normaleq_1[simp]: "[|def a & b = def c & d; b & d --> a = c|]==> (restrictOp a b = restrictOp c d)"*)
lemma normalizeeq_1: "b=c ==> ((restrictOp a b) = (restrictOp a c))"
apply (simp)
done


theorem Ax1_1 :
"ALL f.
 ALL g.
 X_map (% y. restrictOp (g (makeTotal (f y))) (defOp (f y))) =
 (% k. restrictOp (X_map g (makeTotal (X_map f k)))
       (defOp (X_map f k)))"
apply (auto)
apply (rule ext)
apply (induct_tac "k")
apply (simp add: Ax1)
apply (simp add: Ax2 conj_ac)
done

term "(X_filter l (P o f))"
term "(map f l)"
term "X_filter (map f l) P"
term "(makeTotal (X_map f (X_filter l (P o f))))"
term "X_filter (makeTotal (X_map f l)) P"

lemma mapdef: "defOp (X_map f list) --> defOp(X_map f (X_filter list P))"
apply (induct_tac list)
apply (auto simp add: Ax1 Ax6 Ax5 Ax2)
done

theorem mapfilter: "defOp(X_map f l) --> (makeTotal (X_map f (X_filter l P))) = (X_filter (makeTotal (X_map f l)) P)"
apply (induct_tac "l")
apply (simp add: Ax1 Ax6)
apply (auto simp add: Ax5 Ax2 mapdef)
done


theorem Ax2_1 :
"ALL f. ALL l. defOp (X_map f l) = X_all (% y. defOp (f y)) l"

oops
