theory HaskellLibs_LK
imports "$HETS_LIB/Isabelle/MainHCPlus"
uses "$HETS_LIB/Isabelle/prelude"
begin

datatype 'a List = Nil | Cons 'a "'a List"


consts
"map" :: "(('a => 'b option) * ('a List)) => ('b List) option"   ( "map" )
"o" :: "(('b => 'c option) * ('a => 'b option)) => ('a => 'c option)"   ( "o" )


axioms
comp: "apt (Some o) (pair (Some f) (Some g)) = (Some (% x . app (Some f) (app (Some g) (Some x))))"
map_nil: "app (Some map) (pair (Some g) (Some Nil)) = (Some Nil)"
map_cons: "app (Some map) (pair (Some g) (apt (apt (Some Cons) (Some x)) (Some xs))) = apt (apt (Some Cons) (app (Some g) (Some x))) (app (Some map) (pair (Some g) (Some xs)))"


theorem induct_List_pl: "P (Some HaskellLibs_LK.List.Nil) ==>
  (!!a List. P (Some List) ==> P (apt (apt (Some Cons) (Some a)) (Some List)))
   ==> P (Some List)"
apply auto
apply (induct_tac List)
apply (auto)
done

lemmas map_nil' = map_nil [simplified]
declare map_nil' [simp]
declare map_cons [simp]
declare comp [simp]

(* proof by definedness judgements - without tactic *)

theorem map_fuctor: "app (Some map) (pair (apt (Some o) (pair (Some g) (Some f))) (Some xs)) = app (Some map) (pair (Some g) (app (Some map) (pair (Some f) (Some xs))))"
apply (rule_tac List=xs in induct_List_pl)
apply (tactic "Force_tac 1")
apply (rule seqI)
apply (drule st)
apply (drule pairFst)
apply (drule defArg)
apply (erule exE)
apply (simp (no_asm_simp) del: pair.simps app.simps apt.simps defOp.simps comp)
apply (tactic "rotate_tac 1 1")
apply (drule sym)
apply (simp (no_asm_simp) del: pair.simps app.simps apt.simps defOp.simps comp)
apply (rule seqI)
apply (frule stApt2)
apply (drule stApt)
apply (drule stApt)
apply (drule st)
apply (simp only: comp)
apply (simp only: beta)
apply (drule st)
apply (drule pairSnd)
apply (drule defArg)
apply (drule defArg)
apply (erule exE)
apply (erule exE)
apply (simp (no_asm_simp) del: pair.simps app.simps apt.simps defOp.simps comp)

apply (frule st)
apply (drule pairSnd)
apply (frule stApt)
apply (drule stApt2)
apply (drule stApt)
apply (tactic "rotate_tac 4 1")
apply (tactic "rotate_tac 4 1")
apply (drule defArg)
apply (erule exE)
apply (drule defArg)
apply (erule exE)
apply (simp del: pair.simps app.simps apt.simps defOp.simps comp)
apply (tactic "rotate_tac 4 1")
apply (drule sym)
apply (tactic "rotate_tac 3 1")
apply (drule sym)
apply (simp del: pair.simps app.simps apt.simps defOp.simps comp)
apply (simp only: comp)
apply (simp only: beta)

apply (simp only: map_cons)
apply (frule st)
apply (drule pairSnd)
apply (frule stApt)
apply (drule stApt2)
apply (drule stApt)
apply (tactic "rotate_tac 3 1")
apply (tactic "rotate_tac 3 1")
apply (drule defArg)
apply (drule defArg)
apply (erule exE)
apply (erule exE)
apply (simp del: pair.simps app.simps apt.simps defOp.simps comp)(* map_cons)
apply (simp only: map_cons)*)
apply (tactic "rotate_tac 3 1")
apply (tactic "rotate_tac 3 1")
apply (drule sym)
apply (drule sym)
apply (simp del: pair.simps app.simps apt.simps defOp.simps comp map_cons)
apply (drule sym)
apply (simp del: pair.simps app.simps apt.simps defOp.simps comp map_cons)
apply (frule stApt)
apply (drule st)
apply (drule pairFst)
apply (tactic "rotate_tac 4 1")
apply (drule defArg)
apply (erule exE)
apply (simp del: pair.simps app.simps apt.simps defOp.simps comp) (* map_cons)
apply (simp only: map_cons)*)
apply (tactic "rotate_tac 4 1")
apply (drule sym)
apply (simp del: pair.simps app.simps apt.simps defOp.simps map_cons)
apply (simp only: beta)
done

(* same proof by definedness judgements - with tactic *)

theorem map_fuctor: "app (Some map) (pair (apt (Some o) (pair (Some g) (Some f))) (Some xs)) = app (Some map) (pair (Some g) (app (Some map) (pair (Some f) (Some xs))))"
apply (rule_tac List=xs in induct_List_pl)
apply (tactic "Force_tac 1")
apply (rule seqI)
apply (drule st)
apply (drule pairFst)
apply (tactic "HCTactic.my_tac (thm \"map_cons\") 1 false")
apply (rule seqI)
apply (frule stApt2)
apply (drule stApt)
apply (drule stApt)
apply (drule st)
apply (simp only: comp)
apply (simp only: beta)
apply (drule st)
apply (drule pairSnd)
apply (tactic "HCTactic.my_tac (thm \"map_cons\") 2 false")

apply (frule st)
apply (drule pairSnd)
apply (frule stApt)
apply (drule stApt2)
apply (drule stApt)
apply (tactic "rotate_tac 4 1")
apply (tactic "rotate_tac 4 1")
apply (tactic "HCTactic.my_tac (thm \"map_cons\") 2 true")
apply (simp only: comp)
apply (simp only: beta)

apply (simp only: map_cons)
apply (frule st)
apply (drule pairSnd)
apply (frule stApt)
apply (drule stApt2)
apply (drule stApt)
apply (tactic "rotate_tac 3 1")
apply (tactic "rotate_tac 3 1")
apply (tactic "HCTactic.my_tac (thm \"map_cons\") 2 true")
apply (tactic "rotate_tac 1 1")
apply (drule sym)
apply (simp del: pair.simps app.simps apt.simps defOp.simps comp map_cons)
apply (frule stApt)
apply (drule st)
apply (drule pairFst)
apply (tactic "rotate_tac 4 1")
apply (tactic "HCTactic.my_tac (thm \"map_cons\") 1 true")
apply (simp only: comp)
apply (simp only: beta)
done


end
