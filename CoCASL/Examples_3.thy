theory Examples_3 = Main:
typedecl "Elem"
typedecl "Stream"
consts
"cons" :: "Elem => Stream => Stream"
"even" :: "Stream => Stream"
"hd" :: "Stream => Elem"
"merge" :: "Stream => Stream => Stream"
"odd" :: "Stream => Stream"
"tl" :: "Stream => Stream"


axioms
X: "!! s :: Stream . (hd (odd s)) = (hd s)"
X1: "!! s :: Stream . (tl (odd s)) = (odd (tl (tl s)))"
X2: "!! s :: Stream . (hd (even s)) = (hd (tl s))"
X3: "!! s :: Stream . (tl (even s)) = (even (tl (tl s)))"
X4: "!! s1 :: Stream . !! s2 :: Stream . (hd (merge s1 s2)) = (hd s1)"
X5: "!! s1 :: Stream . !! s2 :: Stream . (tl (merge s1 s2)) = merge s2 (tl s1)"
ga_cogenerated_Stream: "!! R :: Stream => Stream => bool . !! u :: Stream . !! v :: Stream . ! x :: Stream . ! y :: Stream . ((R x) y) --> (hd x) = (hd y) & ((R (tl x)) (tl y)) ==> ((R u) v) ==> u = v"
ga_selector_hd: "!! X1 :: Elem . !! X2 :: Stream . (hd (cons X1 X2)) = X1"
ga_selector_tl: "!! X1 :: Elem . !! X2 :: Stream . (tl (cons X1 X2)) = X2"

lemmas Xa = X [simplified]
declare Xa[simp]
declare X[simp]
lemmas X1a = X1 [simplified]
declare X1a[simp]
declare X1[simp]
lemmas X2a = X2 [simplified]
declare X2a[simp]
declare X2[simp]
lemmas X3a = X3 [simplified]
declare X3a[simp]
declare X3[simp]
lemmas X4a = X4 [simplified]
declare X4a[simp]
declare X4[simp]
lemmas X5a = X5 [simplified]
declare X5a[simp]
declare X5[simp]
lemmas ga_cogenerated_Streama = ga_cogenerated_Stream [simplified]
declare ga_cogenerated_Streama[simp]
declare ga_cogenerated_Stream[simp]
lemmas ga_selector_hda = ga_selector_hd [simplified]
declare ga_selector_hda[simp]
declare ga_selector_hd[simp]
lemmas ga_selector_tla = ga_selector_tl [simplified]
declare ga_selector_tla[simp]
declare ga_selector_tl[simp]


theorem X6: "!! s :: Stream . merge (odd s) (even s) = s"
apply(rule_tac R="% x y . (? t . (x=merge (odd t) (even t) & y=t)) | BinRelImage tl ?R1 x y" in ga_cogenerated_Stream)
defer
ML "set show_types"
apply(simp)
apply(rule allI)
apply(rule allI)
apply(rule impI)
apply(erule disjE)
apply(erule exE)
apply(rule conjI)
apply(simp add: X X1 X2 X3 X4 X5 )
apply(rule disjI2)
apply(tactic "instantiate_tac [(\"R1\" , \" % s x y.(? t.(x=merge (odd t) (even t) & y=t))\" )]")
apply(simp add: BinRelImage_def)
apply(rule_tac x=t in exI)
apply(simp)
apply(rule conjI)
apply(simp add: BinRelImage_def)
apply(erule exE)
ML "set trace_simp"
apply(simp add: X X1 X2 X3 X4 X5)
apply(erule conjE)
apply(drule sym)
apply(drule sym)
apply(simp add: X X1 X2 X3 X4 X5)
apply(simp add: BinRelImage_def)
apply(erule exE)
apply(erule conjE)
apply(drule sym)
apply(drule sym)
apply(simp add: X X1 X2 X3 X4 X5)
done


end
