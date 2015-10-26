theory State_1
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

typedecl "S"

consts
"GtXGtXEqX" :: "((S => (S * 'a) option) * ('a => (S => (S * 'a) option) option)) => (S => (S * 'a) option) option"   ( "GtXGtXEqX" )
"return" :: "'a => (S => (S * 'a) option) option"   ( "return" )


axioms
return_def: "app (Some return) (Some x) = (Some (% s . pair (Some s) (Some x)))"
bind_def: "app (Some GtXGtXEqX) (pair (Some m) (Some f)) = (Some (% s . app (Some (% (s', a) . app (app (Some f) (Some a)) (Some s'))) (app (Some m) (Some s))))"

lemmas return_def' = return_def [simplified]
lemmas bind_def' = bind_def [simplified]

declare return_def' [simp]
declare return_def [simp]
declare bind_def' [simp]
declare bind_def [simp]


theorem monad_assoc: "!! x :: 'a . app (Some GtXGtXEqX) (pair (app (Some GtXGtXEqX) (pair (app (Some f) (Some x)) (Some g))) (Some h)) = app (Some GtXGtXEqX) (pair (app (Some f) (Some x)) (Some (% y . app (Some GtXGtXEqX) (pair (app (Some g) (Some y)) (Some h)))))"
apply (simp)
apply (case_tac "f x")
apply (simp_all)
apply (rule ext)
apply (case_tac "a s")
apply (auto)
apply (case_tac "g b")
apply (simp_all)
done
theorem monad_unit1: "app (Some GtXGtXEqX) (pair (app (Some f) (Some x)) (Some return)) = app (Some f) (Some x)"
apply (simp)
apply (case_tac "f x")
apply (simp_all)
apply (rule ext)
apply (case_tac "a s")
apply (simp_all)
done
theorem monad_unit2a: "(defOp (app (Some f) (Some x))) --> app (Some GtXGtXEqX) (pair (app (Some return) (Some x)) (Some f)) = app (Some f) (Some x)"
apply (simp)
apply (case_tac "f x")
apply (simp_all)
done
theorem monad_unit2b: "app (Some GtXGtXEqX) (pair (Some m) (Some (% x . app (Some GtXGtXEqX) (pair (app (Some return) (Some x)) (Some f))))) = app (Some GtXGtXEqX) (pair (Some m) (Some f))"
apply (simp)
apply (rule ext)
apply (case_tac "m s")
apply (simp_all)
done

end
