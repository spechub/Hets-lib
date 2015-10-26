theory RestrictOpProps
imports MainHC
begin

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

(* ============================================================================= *)

lemma makePartialproj: "makeTotal(makePartial x)=x"
apply (subst makeTotal_def)
apply (subst makePartial_def)
apply (auto)
done


end
