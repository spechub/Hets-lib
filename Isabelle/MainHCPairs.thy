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

-- "SUBTYPE ENCODING"

consts

subt :: "'a => 'b => bool"
gn_inj :: "'a => 'b"
gn_proj :: "'a => 'b partial"

axioms

-- "SUBTYPE RULES"

-- "necessary when omitting the quantifiers in the axioms below"
subtype_constant [rule_format] :
"subt (x\<Colon>'a) (y\<Colon>'b) ==> (!!(u::'a) v::'b. subt u v)"

subtype_reflexive [rule_format] :
"subt (x\<Colon>'a) (y\<Colon>'a)"

subtype_transitive [rule_format] :
"[| subt (x\<Colon>'a) (y\<Colon>'b); subt (z\<Colon>'b) (t\<Colon>'c) |]  ==> subt (u\<Colon>'a) (v\<Colon>'c)"

-- "is used for derivation of subtypes:"
subtype_subsumption [rule_format] :
"[| subt (x\<Colon>'a) (y\<Colon>'c); subt (z\<Colon>'b) (t\<Colon>'c);
  (!!(z'::'c). defOp(gn_proj(z')\<Colon>'a partial) ==> defOp(gn_proj(z')\<Colon>'b partial)) |]
  ==> (subt (u\<Colon>'a) (v\<Colon>'b))"


-- "INJECTION PROJECTION RULES"

-- "is used to derive defining predicate P for a subtype A, P(gn_inj(x::A))"
gn_proj_def [rule_format] :
"subt (x\<Colon>'a) (y\<Colon>'b) ==> defOp(gn_proj(gn_inj(x)\<Colon>'b)\<Colon>'a partial)"

gn_proj_inj [rule_format] :
"subt (x\<Colon>'a) (y\<Colon>'b) ==> (!!(z::'a). makeTotal(gn_proj(gn_inj(z)\<Colon>'b)) = z)"

gn_inj_proj [rule_format] :
"subt (x\<Colon>'a) (y\<Colon>'b) ==> (!!(z::'b). defOp(gn_proj(z)\<Colon>'a partial) ==>
  gn_inj(makeTotal(gn_proj(z)\<Colon>'a partial)) = z)"

gn_inj_diagram [rule_format] :
"[| subt (x\<Colon>'a) (y\<Colon>'b); subt (t\<Colon>'b) (z\<Colon>'c) |]
  ==> (!!(x'::'a). (gn_inj(x')\<Colon>'c) = gn_inj(gn_inj(x')\<Colon>'b))"


lemma gn_inj_injective :
  "subt (u\<Colon>'a) (v\<Colon>'b) ==> inj (gn_inj\<Colon>'a => 'b)"
  proof (rule injI)
    fix x::'a
    fix y::'a
    assume hyp1: "subt (u\<Colon>'a) (v\<Colon>'b)"
      and hyp2: "(gn_inj x\<Colon>'b) = gn_inj y"

    from hyp1 subtype_constant 
    have fact: "!!(z::'a). makeTotal(gn_proj(gn_inj(z)\<Colon>'b)) = z"
      by (rule_tac gn_proj_inj, blast)

    hence "x = makeTotal(gn_proj(gn_inj(x)\<Colon>'b))" ..
    also from hyp2 have "\<dots> = makeTotal(gn_proj(gn_inj(y)\<Colon>'b))" by simp
    also from fact have "\<dots> = y" by simp
    finally show "x = y" by simp
  qed

lemma gn_inj_identity :
"!!x::'a. (gn_inj(x)\<Colon>'a) = x"
proof-
  fix x::'a
  have fact: "(gn_inj(x)\<Colon>'a) = gn_inj(gn_inj(x)\<Colon>'a)"
    by (simp_all add: gn_inj_diagram subtype_reflexive)
  thus "(gn_inj(x)\<Colon>'a) = x"
    by (subst injD [of "(gn_inj\<Colon>'a=>'a)" "(gn_inj(x)\<Colon>'a)" x],
      simp_all only: gn_inj_injective subtype_reflexive fact [symmetric])
qed

end
