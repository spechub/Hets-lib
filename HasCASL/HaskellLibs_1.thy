ML "val hetsLib = (OS.Process.getEnv \"HETS_LIB\"); 
case hetsLib of NONE => add_path \".\" 
| SOME s => add_path (s ^ \"/Isabelle\")"

theory HaskellLibs_5 = MainHC:
datatype Nat = X0 | Suc "Nat"

datatype 'a List = Nil | Cons 'a "'a List"

datatype Bool = TrueX | FalseX

consts
"PlusXPlusX" :: "('a List * 'a List) => 'a List"   ( "PlusXPlusX" )
"filter" :: "(('a => Bool option) * 'a List) => 'a List option"   ( "filter" )
"foldl" :: "(((('a * 'b) => 'a option) * 'a) * 'b List) => 'a option"   ( "foldl" )
"foldr" :: "(((('a * 'b) => 'b option) * 'b) * 'a List) => 'b option"   ( "foldr" )
"head" :: "'a List => 'a option"   ( "head" )
"lengtH" :: "'a List => Nat"   ( "lengtH" )
"map" :: "(('a => 'b option) * 'a List) => 'b List option"   ( "map" )
"o" :: "(('b => 'c option) * ('a => 'b option)) => ('a => 'c option)"   ( "o" )
"unzip" :: "('a * 'b) List => ('a List * 'b List)"   ( "unzip" )
"zip" :: "('a List * 'b List) => ('a * 'b) List"   ( "zip" )
lemma case_Nat_SomeProm [simp]:" (case caseVar of X0 => Some (x)
   | Suc nat => Some (s nat)
) =
Some (case caseVar of X0 => x
   | Suc nat => s nat
)"
apply (case_tac caseVar)
apply (auto)
done
lemma case_List_SomeProm [simp]:" (case caseVar of Nil => Some (n)
   | Cons a list => Some (c a list)
) =
Some (case caseVar of Nil => n
   | Cons a list => c a list
)"
apply (case_tac caseVar)
apply (auto)
done
lemma case_Bool_SomeProm [simp]:" (case caseVar of TrueX => Some (t)
   | FalseX => Some (f)
) =
Some (case caseVar of TrueX => t
   | FalseX => f
)"
apply (case_tac caseVar)
apply (auto)
done


axioms
ga_Nat: "True"
ga_Bool: "True"
comp: "apt (Some o) (pair (Some f) (Some g)) = (Some (% x . app (Some f) (app (Some g) (Some x))))"
ga_List: "True"
lengtH_nil: "apt (Some lengtH) (Some Nil) = (Some X0)"
lengtH_cons: "apt (Some lengtH) (apt (apt (Some Cons) (Some x)) (Some xs)) = apt (Some Suc) (apt (Some lengtH) (Some xs))"
not_def_head: "(Not (defOp (app (Some head) (Some Nil))))"
head_def: "app (Some head) (apt (apt (Some Cons) (Some x)) (Some xs)) = (Some x)"
foldr_nil: "app (Some foldr) (pair (pair (Some f) (Some s)) (Some Nil)) = (Some s)"
foldr_cons: "app (Some foldr) (pair (pair (Some f) (Some s)) (apt (apt (Some Cons) (Some x)) (Some xs))) = app (Some f) (pair (Some x) (app (Some foldr) (pair (pair (Some f) (Some s)) (Some xs))))"
foldl_nil: "app (Some foldl) (pair (pair (Some g) (Some t)) (Some Nil)) = (Some t)"
foldl_cons: "app (Some foldl) (pair (pair (Some g) (Some t)) (apt (apt (Some Cons) (Some z)) (Some zs))) = app (Some foldl) (pair (pair (Some g) (app (Some g) (pair (Some t) (Some z)))) (Some zs))"
map_nil: "app (Some map) (pair (Some h) (Some Nil)) = (Some Nil)"
map_cons: "app (Some map) (pair (Some h) (apt (apt (Some Cons) (Some x)) (Some xs))) = apt (apt (Some Cons) (app (Some h) (Some x))) (app (Some map) (pair (Some h) (Some xs)))"
filter_nil: "app (Some filter) (pair (Some p) (Some Nil)) = (Some Nil)"
filter_cons: "app (Some filter) (pair (Some p) (apt (apt (Some Cons) (Some x)) (Some xs))) = (case app (Some p) (Some x) of None => None
   | Some caseVar => (case caseVar of TrueX => apt (apt (Some Cons) (Some x)) (app (Some filter) (pair (Some p) (Some xs)))
   | FalseX => app (Some filter) (pair (Some p) (Some xs))))"
PlusPlus_nil: "apt (Some PlusXPlusX) (pair (Some Nil) (Some l)) = (Some l)"
PlusPlus_cons: "apt (Some PlusXPlusX) (pair (apt (apt (Some Cons) (Some x)) (Some xs)) (Some l)) = apt (apt (Some Cons) (Some x)) (apt (Some PlusXPlusX) (pair (Some xs) (Some l)))"
zip_nil: "apt (Some zip) (pair (Some Nil) (Some l)) = (Some Nil)"
zip_cons: "apt (Some zip) (pair (apt (apt (Some Cons) (Some x)) (Some xs)) (Some l)) = (case l of Nil => (Some Nil)
   | Cons y ys => apt (apt (Some Cons) (pair (Some x) (Some y))) (apt (Some zip) (pair (Some xs) (Some ys))))"
unzip_nil: "apt (Some unzip) (Some Nil) = pair (Some Nil) (Some Nil)"
unzip_cons: "apt (Some unzip) (apt (apt (Some Cons) (pair (Some x) (Some z))) (Some ps)) = app (Some (% (ys, zs) . pair (apt (apt (Some Cons) (Some x)) (Some ys)) (apt (apt (Some ConsS) (Some z)) (Some zs)))) (apt (Some unzip) (Some ps))"

lemmas ga_Nat' = ga_Nat [simplified]
lemmas ga_Bool' = ga_Bool [simplified]
lemmas comp' = comp [simplified]
lemmas ga_List' = ga_List [simplified]
lemmas lengtH_nil' = lengtH_nil [simplified]
lemmas lengtH_cons' = lengtH_cons [simplified]
lemmas not_def_head' = not_def_head [simplified]
lemmas head_def' = head_def [simplified]
lemmas foldr_nil' = foldr_nil [simplified]
lemmas foldr_cons' = foldr_cons [simplified]
lemmas foldl_nil' = foldl_nil [simplified]
lemmas foldl_cons' = foldl_cons [simplified]
lemmas map_nil' = map_nil [simplified]
lemmas map_cons' = map_cons [simplified]
lemmas filter_nil' = filter_nil [simplified]
lemmas filter_cons' = filter_cons [simplified]
lemmas PlusPlus_nil' = PlusPlus_nil [simplified]
lemmas PlusPlus_cons' = PlusPlus_cons [simplified]

declare List.weak_case_cong [cong del]
declare List.case_cong [cong]

lemmas zip_nil' = zip_nil [simplified]
lemmas zip_cons' = zip_cons [simplified]
lemmas unzip_nil' = unzip_nil [simplified]
lemmas unzip_cons' = unzip_cons [simplified]

declare ga_Nat' [simp]
declare ga_Nat [simp]
declare ga_Bool' [simp]
declare ga_Bool [simp]
declare comp' [simp]
declare comp [simp]
declare ga_List' [simp]
declare ga_List [simp]
declare lengtH_nil' [simp]
declare lengtH_nil [simp]
declare lengtH_cons' [simp]
declare lengtH_cons [simp]
declare not_def_head' [simp]
declare not_def_head [simp]
declare head_def' [simp]
declare head_def [simp]
declare foldr_nil' [simp]
declare foldr_nil [simp]
declare foldr_cons' [simp]
declare foldr_cons [simp]
declare foldl_nil' [simp]
declare foldl_nil [simp]
declare foldl_cons' [simp]
declare foldl_cons [simp]
declare map_nil' [simp]
declare map_nil [simp]
declare map_cons' [simp]
declare map_cons [simp]
declare filter_nil' [simp]
declare filter_nil [simp]
declare filter_cons' [simp]
declare filter_cons [simp]
declare PlusPlus_nil' [simp]
declare PlusPlus_nil [simp]
declare PlusPlus_cons' [simp]
declare PlusPlus_cons [simp]
declare zip_nil' [simp]
declare zip_nil [simp]
declare zip_cons' [simp]
declare zip_cons [simp]
declare unzip_nil' [simp]
declare unzip_nil [simp]
declare unzip_cons' [simp]
declare unzip_cons [simp]


theorem foldl_decomp: "app (Some foldl) (pair (pair (Some i) (Some e)) (apt (Some PlusXPlusX) (pair (Some xs) (Some zs)))) = app (Some foldl) (pair (pair (Some i) (app (Some foldl) (pair (pair (Some i) (Some e)) (Some xs)))) (Some zs))"
apply (simp)
apply (rule_tac  x = e in spec)
apply (rule_tac  x = zs in spec)
apply (induct_tac xs)
apply (simp)
apply (simp only: PlusPlus_cons')
apply (simp only: foldl_cons')
apply (case_tac "i(xa,a)")
apply auto
apply (case_tac "i(xaa,a)")
apply auto
apply (case_tac "i(xaa,a)")
apply auto
done
theorem map_decomp: "app (Some map) (pair (Some f) (apt (Some PlusXPlusX) (pair (Some xs) (Some zs)))) = apt (Some PlusXPlusX) (pair (app (Some map) (pair (Some f) (Some xs))) (app (Some map) (pair (Some f) (Some zs))))"
apply (simp)
apply (rule_tac  x = zs in spec)
apply (induct_tac xs)
apply (simp)
apply (rule allI)
apply (case_tac "map (f, x)")
apply (simp_all)
apply (rule allI)
apply (case_tac "f a")
apply (simp_all)
apply (case_tac "map (f, List)")
apply (simp_all)
apply (case_tac "map (f, x)")
apply (simp_all)
done
theorem map_functor: "app (Some map) (pair (apt (Some o) (pair (Some g) (Some f))) (Some xs)) = app (Some map) (pair (Some g) (app (Some map) (pair (Some f) (Some xs))))"
apply (induct_tac xs)
apply (simp_all)
apply (case_tac "f a")
apply (simp_all)
apply (case_tac "g aa")
apply (simp)
apply (case_tac [!] "map (f, List)")
apply (simp_all)
done
theorem filter_prom: "app (Some filter) (pair (Some p) (app (Some map) (pair (Some f) (Some xs)))) = app (Some map) (pair (Some f) (app (Some filter) (pair (apt (Some o) (pair (Some p) (Some f))) (Some xs))))"
apply (induct_tac xs)
apply (auto)
apply (case_tac "option_case None p (f a) = None")
apply (auto)
apply (case_tac [!] "f a  = None")
apply (auto)
apply (case_tac [!] "map (f, List) = None")
apply (auto)
apply (case_tac [!] y)
apply (auto)
apply (case_tac [!] "filter (%x. option_case None p (f x), List)")
apply (auto)
done
lemma option_inj_new: "Some x = Some y ==> x = y"
apply (auto)
done

theorem zip_spec: "apt (Some lengtH) (Some xs) = apt (Some lengtH) (Some ys) --> apt (Some unzip) (apt (Some zip) (pair (Some xs) (Some ys))) = pair (Some xs) (Some ys)"
apply (simp only: apt.simps pair.simps)
apply (simp)
apply (rule_tac  x = ys in spec)
apply (induct_tac xs)
apply simp
apply (rule allI)
apply (case_tac x)
apply (auto)
apply (case_tac x)
apply (simp)
apply (simp)
apply (rule option_inj_new)
apply (simp)
done

end
