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

gn_inj_def [rule_format] :
"!!(x::'a) (y::'b). (subt x y) ==>
  (EX z::'b. gn_inj(x) = z & defOp(gn_proj(z)) & makeTotal(gn_proj(z)) = x)"

gn_proj_def [rule_format] :
"!!(x::'a) (y::'b). (subt x y) ==> (defOp(gn_proj(y))
  ==> EX z::'a partial. gn_proj(y) = z & gn_inj(makeTotal(z)) = y)"

lemma gn_inj_fact1: "!!(x\<Colon>'a) (y\<Colon>'b). (subt x y) ==> makeTotal(gn_proj(gn_inj(x)\<Colon>'b)) = x"
proof-
  fix x y
  assume hyp: "subt (x\<Colon>'a) (y\<Colon>'b)"
  have "\<exists>z\<Colon>'b. gn_inj x = z \<and> defOp (gn_proj z) \<and> makeTotal (gn_proj z) = x"
    by (insert gn_inj_def [of x y], simp add: hyp)
  thus "makeTotal(gn_proj(gn_inj(x)\<Colon>'b)) = x" by blast
qed
    (* this instead doesn't work!
	  assume hyp: "subt x y"
	  have "\<exists>z. gn_inj x = z \<and> defOp (gn_proj z) \<and> makeTotal (gn_proj z) = x"
	  thus "makeTotal(gn_proj(gn_inj(x))) = x" by blast
    *)	  

end
