theory PartialityTest_Test_E1
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize [\"Ax1\", \"Ax1_1\"]"

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


typedecl a

consts
f :: "(a * a ) => a partial"

axioms
Ax1 [rule_format] :
"ALL x.
 ALL y.
 ALL z.
 defOp (f(x, y)) & defOp (f(y, z)) -->
 restrictOp (f(x, makeTotal (f(y, z)))) (defOp (f(y, z))) =
 restrictOp (f(makeTotal (f(x, y)), z)) (defOp (f(x, y)))"

Ax1_monad [rule_format] :
"ALL x.
 ALL y.
 ALL z.
 defOp (lift2partial f (pair x y)) & 
 defOp (lift2partial f (pair y z)) -->
 lift2partial f (pair x (lift2partial f (pair y z))) =
 lift2partial f (pair (lift2partial f (pair x y)) z)"

Ax1_monad_unsound [rule_format] :
"ALL x.
 ALL y.
 ALL z.
 lift2partial f (pair x (lift2partial f (pair y z))) =
 lift2partial f (pair (lift2partial f (pair x y)) z)"


theorem Ax1_1_monadic:
"ALL w.
 ALL x.
 ALL y.
 ALL z.
 preDefOp (lift2partial f (pair x (lift2partial f (pair y z)))) &
 preDefOp (lift2partial f (pair y (lift2partial f (pair z w)))) --> 
 lift2partial f (pair (lift2partial f (pair x (lift2partial f (pair y z)))) w)
 =
 lift2partial f (pair x (lift2partial f (pair y (lift2partial f (pair z w)))))"
apply (clarify)
apply (simp add: Ax1_monad)

back

lemma assoc_dom : "defOp (f(x, y)) & defOp (f(y, z)) ==> 
  (defOp (f(x, makeTotal (f(y, z)))) & defOp (f(y, z))) = 
  (defOp (f(makeTotal (f(x, y)), z)) & defOp (f(x, y)))"
apply (frule Ax1)
apply (simp add: makeTotal_def restrictOp_def defOp.simps undefinedOp_def)
done

lemma assoc_eq : "defOp (f(x, y)) & defOp (f(y, z)) ==> 
  f(x, makeTotal (f(y, z))) = f(makeTotal (f(x, y)), z)"
apply (frule Ax1)
apply (simp add: makeTotal_def restrictOp_def defOp.simps undefinedOp_def)
done

theorem Ax1_1 :
"ALL w.
 ALL x.
 ALL y.
 ALL z.
 defOp (restrictOp (f(x, makeTotal (f(y, z)))) (defOp (f(y, z)))) &
 defOp
 (restrictOp (f(y, makeTotal (f(z, w)))) (defOp (f(z, w)))) -->
 restrictOp (f(makeTotal (f(x, makeTotal (f(y, z)))), w))
 (defOp (f(x, makeTotal (f(y, z)))) & defOp (f(y, z))) =
 restrictOp (f(x, makeTotal (f(y, makeTotal (f(z, w))))))
 (defOp (f(y, makeTotal (f(z, w)))) & defOp (f(z, w)))"
apply (auto)
apply (simp add: assoc_eq assoc_dom)
done



ML "Header.record \"Ax1_1\""

end
