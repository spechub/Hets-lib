theory MainHCPairs
imports Main
begin

types 'a partial = "bool * 'a"

constdefs

defOp :: "'a partial => bool"
"defOp p == fst p"

makeTotal :: "'a partial => 'a"
"makeTotal == snd"

makePartial :: "'a => 'a partial"
"makePartial a == (True, a)"

(* undefined is predefined *)
undefinedOp :: "'a partial"
"undefinedOp == (False, arbitrary)"

(* backward compatibility only *)
noneOp :: "'a partial"
"noneOp == undefinedOp"

restrictOp :: "'a partial => bool => 'a partial"
"restrictOp a b == if b then a else undefinedOp"

(* utilities *)
flip :: "('a => 'b => 'c) => 'b => 'a => 'c"
"flip f a b == f b a"

uncurryOp :: "('a => 'b => 'c) => 'a * 'b => 'c"
"uncurryOp f p == f (fst p) (snd p)"

curryOp :: "('a * 'b => 'c) => 'a => 'b => 'c"
"curryOp f a b == f (a, b)"

(* map on pairs *)
mapFst :: "('a => 'b) => 'a * 'c => 'b * 'c"
"mapFst f p == (f (fst p), snd p)"

mapSnd :: "('b => 'c) => 'a * 'b => 'a * 'c"
"mapSnd f p == (fst p, f (snd p))"

(* predefined HasCASL functions *)
ifImplOp :: "bool * bool => bool"
"ifImplOp p == snd p --> fst p"

existEqualOp :: "'a partial => 'a partial => bool" ("(_ =e=/ _)" [50, 51] 50)
"existEqualOp a b == defOp a & defOp b & makeTotal a = makeTotal b"

exEqualOp :: "'a partial * 'a partial => bool"
"exEqualOp == uncurryOp existEqualOp"

strongEqualOp :: "'a partial => 'a partial => bool" ("(_ =s=/ _)" [50, 51] 50)
"strongEqualOp a b == a = b"

whenElseOp :: "('a partial * bool) * 'a partial => 'a partial"
"whenElseOp t == case t of
    (p, e) => if snd p then fst p else e"

resOp :: "'a partial * 'b partial => 'a"
"resOp p == makeTotal (restrictOp (fst p) (defOp (snd p)))"

(* conversions *)
lift2partial :: "('a => 'b partial) => 'a partial => 'b partial"
"lift2partial f s == restrictOp (f (makeTotal s)) (defOp s)"

mapPartial :: "('a => 'b) => 'a partial => 'b partial"
"mapPartial f s == restrictOp (makePartial (f (makeTotal s))) (defOp s)"

unpackPartial :: "(('a => 'b partial) => 'c => 'd partial)
            => ('a => 'b partial) partial => 'c => 'd partial"
"unpackPartial c s a == lift2partial (flip c a) s"

unpackBool :: "(('a => bool) => 'c => bool)
            => ('a => bool) partial => 'c => bool"
"unpackBool c s a == defOp s & c (makeTotal s) a"

unpack2partial :: "(('a => 'b) => 'c => 'd)
            => ('a => 'b) partial => 'c => 'd partial"
"unpack2partial c s a == mapPartial (flip c a) s"

unpack2bool :: "(('a => unit) => 'c => unit)
            => ('a => unit) partial => 'c => bool"
"unpack2bool c s a == defOp s"

bool2partial :: "bool => unit partial"
"bool2partial b == restrictOp (makePartial ()) b"

liftUnit2unit :: "('a => 'b) => bool => bool"
"liftUnit2unit f b == b"

liftUnit2bool :: "(unit => bool) => bool => bool"
"liftUnit2bool f b == b & f ()"

liftUnit2partial :: "(unit => 'a partial) => bool => 'a partial"
"liftUnit2partial f b == restrictOp (f ()) b"

liftUnit :: "(unit => 'a) => bool => 'a partial"
"liftUnit f b == restrictOp (makePartial (f ())) b"

lift2unit :: "('b => 'c) => ('a partial => bool)"
"lift2unit f == defOp"

lift2bool :: "('a => bool) => 'a partial => bool"
"lift2bool f s == defOp s & f (makeTotal s)"

-- "subtype encoding"

consts

subt :: "'a => 'b => bool"
gn_inj :: "'a => 'b"
gn_proj :: "'a => 'b partial"

axioms

-- "general injection projection property"
gn_inj_proj_def [rule_format] :
"!!(x::'a) (y::'b). defOp(gn_proj(gn_inj(x)\<Colon>'b)\<Colon>'a partial) ==>
  makeTotal(gn_proj(gn_inj(x)\<Colon>'b)) = x"

gn_inj_def [rule_format] :
"!!(x::'a) (y::'b). (subt x y) ==
  defOp(gn_proj(gn_inj(x)\<Colon>'b)\<Colon>'a partial)"

gn_proj_def [rule_format] :
"!!(x::'a) (y::'b). (subt x y) ==> (defOp(gn_proj(y)\<Colon>'a partial)
  ==> \<exists>z::'a. y = gn_inj(z))"

subt_subsumption [rule_format] :
"!!(x::'a) (y::'b) (z::'c). (subt x z) & (subt y z)
  ==> (!!(z'::'c). defOp(gn_proj(z')\<Colon>'a partial) ==> defOp(gn_proj(z')\<Colon>'b partial))
  ==> (subt x y)"

subt_identity [rule_format] :
"!!(x::'a). defOp(gn_proj(x)\<Colon>'a partial)"

lemma gn_proj_fact:
"!!(x::'a) (y::'b). (subt x y) ==> (defOp(gn_proj(y)\<Colon>'a partial)
  ==> gn_inj(makeTotal(gn_proj(y)\<Colon>'a partial)) = y)"
  proof-
    fix x::'a
    fix y::'b
    assume hyp1: "subt x y" and hyp2: "defOp(gn_proj y\<Colon>'a partial)"
    have "\<exists>z::'a. y = gn_inj(z)" (is "\<exists>z. ?P z")
      by (rule gn_proj_def [of x y], (simp only: hyp1 hyp2)+)
    then obtain z where y_def: "?P z" ..
    from hyp2 have fact: "defOp(gn_proj(gn_inj(z)\<Colon>'b)\<Colon>'a partial)" by (simp only: y_def)
    show "gn_inj(makeTotal(gn_proj(y)\<Colon>'a partial)) = y"
      by ((subst y_def)+, subst gn_inj_proj_def, simp_all only: fact)
  qed


(*
lemma subt_reflexive:
"!!(x::'a) (y::'a). subt x y"
proof-
  fix x::'a
  fix y::'a
  have "(!!(z::'a). defOp(gn_proj(z)\<Colon>'a partial)) ==> subt x y"
    by (rule subt_subsumption)
  with subt_identity show "subt x y" by blast
qed
*)

lemma gn_inj_defOp: "!!(x\<Colon>'a) (y\<Colon>'b). (subt x y) ==> defOp(gn_proj(gn_inj(x)\<Colon>'b)\<Colon>'a partial)"
  by (simp only: gn_inj_def)

lemma gn_inj_identity: "!!(x\<Colon>'a) (y\<Colon>'b). (subt x y) ==> makeTotal(gn_proj(gn_inj(x)\<Colon>'b)) = x"
  by (simp only: gn_inj_proj_def gn_inj_def)

end
