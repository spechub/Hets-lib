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

constdefs
  BinRelImage :: "('a => 'b) => ('a => 'a => bool) => ('b => 'b => bool)"
  "BinRelImage f R == %x y . EX u v . R u v & f u = x & f v = y"
(*  uncurry :: "('a * 'b) => boo*)
 
axioms
X: "!! s :: Stream . (hd (odd s)) = (hd s)"
X1: "!! s :: Stream . (tl (odd s)) = odd (tl (tl s))"
X2: "!! s :: Stream . (hd (even s)) = (hd (tl s))"
X3: "!! s :: Stream . (tl (even s)) = even (tl (tl s))"
X4: "!! s1 :: Stream . !! s2 :: Stream . (hd (merge s1 s2)) = (hd s1)"
X5: "!! s1 :: Stream . !! s2 :: Stream . (tl (merge s1 s2)) = merge s2 (tl s1)"
ga_cogenerated_Stream: "!! R :: Stream => Stream => bool . !! u :: Stream . !! v :: Stream . ! x :: Stream . ! y :: Stream . ((R x) y) --> ((hd x) = (hd y) & ((R (tl x)) (tl y)))  ==> ((R u) v) ==> u = v"
ga_selector_hd: "!! X1 :: Elem . !! X2 :: Stream . (hd (cons X1 X2)) = X1"
ga_selector_tl: "!! X1 :: Elem . !! X2 :: Stream . (tl (cons X1 X2)) = X2"


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
