ML "val hetsLib = (OS.Process.getEnv \"HETS_LIB\"); 
case hetsLib of NONE => add_path \".\" 
| SOME s => add_path (s ^ \"/Isabelle\")"

theory Foldl3_FoldlImpl = MainHC:
datatype 'a List = nil | cons 'a "'a List"

consts
"foldl" :: "'b => (('b => ('a => 'b option)) => ('a List => 'b option))"   ( "foldl" )
"snoc" :: "'a List => ('a => 'a List)"   ( "snoc" )
lemma case_List_SomeProm [simp]:" (case caseVar of nil => Some (n)
   | cons a list => Some (c a list)
) =
Some (case caseVar of nil => n
   | cons a list => c a list
)"
apply (case_tac caseVar)
apply (auto)
done


axioms
ga_List: "True"
Ax2: "apt (apt (Some snoc) (Some nil)) (Some x) = apt (apt (Some cons) (Some x)) (Some nil)"
Ax3: "apt (apt (Some snoc) (apt (apt (Some cons) (Some y)) (Some l))) (Some x) = apt (apt (Some cons) (Some y)) (apt (apt (Some snoc) (Some l)) (Some x))"
Ax4: "app (apt (apt (Some foldl) (Some z)) (Some f)) (Some nil) = (Some z)"
Ax5: "app (apt (apt (Some foldl) (Some z)) (Some f)) (apt (apt (Some cons) (Some x)) (Some l)) = app (apt (apt (Some foldl) (app (apt (Some f) (Some z)) (Some x))) (Some f)) (Some l)"

(*replaced first apt by app in Ax4, snd app by apt in Ax5*)
lemmas ga_List' = ga_List [simplified]
lemmas Ax2' = Ax2 [simplified]
lemmas Ax3' = Ax3 [simplified]
lemmas Ax4' = Ax4 [simplified]
lemmas Ax5' = Ax5 [simplified]
thm Ax5'

declare ga_List' [simp]
declare ga_List [simp]
declare Ax2' [simp]
declare Ax2 [simp]
declare Ax3' [simp]
declare Ax3 [simp]
declare Ax4' [simp]
declare Ax4 [simp]
declare Ax5' [simp]
declare Ax5 [simp]


theorem ga_List1: "True"
apply (auto)
done

theorem Ax21: "apt (apt (Some snoc) (Some nil)) (Some x) = apt (apt (Some cons) (Some x)) (Some nil)"
apply (auto)
done

theorem Ax31: "apt (apt (Some snoc) (apt (apt (Some cons) (Some y)) (Some l))) (Some x) = apt (apt (Some cons) (Some y)) (apt (apt (Some snoc) (Some l)) (Some x))"
apply (auto)
done

theorem Ax41: "app (apt (apt (Some foldl) (Some z)) (Some f)) (Some nil) = (Some z)"
(* Replaced first apt by app *)
apply (auto)
done


theorem Ax51: "app (apt (apt (Some foldl) (Some z)) (Some f)) (apt (apt (Some snoc) (Some l)) (Some x)) = app (apt (Some f) (app (apt (apt (Some foldl) (Some z)) (Some f)) (Some l))) (Some x)"
(* replaced first apt in apt apt apt by app, 2 times; snd app on rhs by apt *)
apply (rule_tac x=z in spec)
apply (simp)
apply (induct l)
apply (auto)
apply (case_tac "f xa x")

apply (simp)
apply (simp)
apply (case_tac "f xa a")

apply (auto)
done


end
