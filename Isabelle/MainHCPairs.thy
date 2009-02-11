theory MainHCPairs
imports Main
begin

types 'a partial = "bool * 'a"

constdefs

flip :: "('a => 'b => 'c) => 'b => 'a => 'c"
"flip f a b == f b a"

ifImplOp :: "bool * bool => bool"
"ifImplOp p == snd p --> fst p"

existEqualOp :: "'a partial => 'a partial => bool" ("(_ =e=/ _)" [50, 51] 50)
"existEqualOp a b == fst a & fst b & snd a = snd b"

strongEqualOp :: "'a partial => 'a partial => bool" ("(_ =s=/ _)" [50, 51] 50)
"strongEqualOp a b == fst a = fst b & (~ (fst a) | snd a = snd b)"

whenElseOp :: "('a partial * bool) * 'a partial => 'a partial"
"whenElseOp t == case t of
    (p, e) => if snd p then fst p else e"

makeTotal :: "'a partial => 'a"
"makeTotal p == if fst p then snd p else arbitrary"

makePartial :: "'a => 'a partial"
"makePartial a == (True, a)"

resOp :: "'a partial * 'b partial => 'a"
"resOp p == if fst (snd p) then makeTotal (fst p) else arbitrary"

noneOp :: "'a partial"
"noneOp == (False, arbitrary)"

unpackPartial :: "(('a => 'b partial) => 'c => 'd partial)
            => ('a => 'b partial) partial => 'c => 'd partial"
"unpackPartial c s a == if fst s then c (snd s) a else noneOp"

unpackBool :: "(('a => bool) => 'c => bool)
            => ('a => bool) partial => 'c => bool"
"unpackBool c s a == if fst s then c (snd s) a else False"

unpack2partial :: "(('a => 'b) => 'c => 'd)
            => ('a => 'b) partial => 'c => 'd partial"
"unpack2partial c s a == (fst s, c (snd s) a)"

partial2bool :: "'a partial => bool"
"partial2bool s == fst s"

unpack2bool :: "(('a => unit) => 'c => unit)
            => ('a => unit) partial => 'c => bool"
"unpack2bool c s a == partial2bool s"

uncurryOp :: "('a => 'b => 'c) => 'a * 'b => 'c"
"uncurryOp f p == f (fst p) (snd p)"

curryOp :: "('a * 'b => 'c) => 'a => 'b => 'c"
"curryOp f a b == f (a, b)"

exEqualOp :: "'a partial * 'a partial => bool"
"exEqualOp == uncurryOp existEqualOp"

bool2partial :: "bool => unit partial"
"bool2partial b == (b, ())"

liftUnit2unit :: "('a => 'b) => bool => bool"
"liftUnit2unit f b == b"

liftUnit2bool :: "(unit => bool) => bool => bool"
"liftUnit2bool f b == if b then f () else False"

liftUnit2partial :: "(unit => 'a partial) => bool => 'a partial"
"liftUnit2partial f b == if b then f () else noneOp"

liftUnit :: "(unit => 'a) => bool => 'a partial"
"liftUnit f b == (b, f ())"

lift2unit :: "('b => 'c) => ('a partial => bool)"
"lift2unit f == partial2bool"

lift2bool :: "('a => bool) => 'a partial => bool"
"lift2bool f s == if fst s then f (snd s) else False"

lift2partial :: "('a => 'b partial) => 'a partial => 'b partial"
"lift2partial f s == if fst s then f (snd s) else noneOp"

mapPartial :: "('a => 'b) => 'a partial => 'b partial"
"mapPartial f s == (fst s, f (snd s))"

mapFst :: "('a => 'b) => 'a * 'c => 'b * 'c"
"mapFst f p == (f (fst p), snd p)"

mapSnd :: "('b => 'c) => 'a * 'b => 'a * 'c"
"mapSnd f p == (fst p, f (snd p))"

defOp :: "'a partial => bool"
"defOp p == fst p"

consts

X_gn_inj :: "'a => 'b" ("gn'_inj/'(_')" [3] 999)
X_gn_proj :: "'a => 'b partial" ("gn'_proj/'(_')" [3] 999)


axioms

gn_proj_inj_inverse [rule_format] :
"snd(gn_proj(gn_inj(x))) = x"

gn_inj_proj_inverse [rule_format] :
"defOp(gn_proj(x)) --> (gn_inj(snd(gn_proj(x))) = x)"

end
