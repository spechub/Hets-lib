theory MainHCPairs
imports Main
begin

types 'a partial = "bool * 'a"

constdefs

flip :: "('a => 'b => 'c) => 'b => 'a => 'c"
"flip f a b == f b a"

ifImplOp :: "bool * bool => bool"
"ifImplOp p == snd p --> fst p"

exEqualOp :: "'a partial * 'a partial => bool"
"exEqualOp p == fst (fst p) & fst (snd p)"

whenElseOp :: "('a partial * bool) * 'a partial => 'a partial"
"whenElseOp t == case t of
    (p, e) => if snd p then fst p else e"

resOp :: "'a partial * 'b partial => 'a"
"resOp p == if fst (fst p) then snd (fst p) else arbitrary"

unpackPartial :: "(('a => 'b partial) => 'c => 'd partial)
            => ('a => 'b partial) partial => 'c => 'd partial"
"unpackPartial c s a == if fst s then c (snd s) a else (False, arbitrary)"

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

bool2partial :: "bool => unit partial"
"bool2partial b == (b, ())"

liftUnit2unit :: "('a => 'b) => bool => bool"
"liftUnit2unit f b == b"

liftUnit2bool :: "(unit => bool) => bool => bool"
"liftUnit2bool f b == if b then f () else False"

liftUnit2partial :: "(unit => 'a partial) => bool => 'a partial"
"liftUnit2partial f b == if b then f () else (False, arbitrary)"

liftUnit :: "(unit => 'a) => bool => 'a partial"
"liftUnit f b == (b, f ())"

lift2unit :: "('b => 'c) => ('a partial => bool)"
"lift2unit f == partial2bool"

lift2bool :: "('a => bool) => 'a partial => bool"
"lift2bool f s == if fst s then f (snd s) else False"

lift2partial :: "('a => 'b partial) => 'a partial => 'b partial"
"lift2partial f s == if fst s then f (snd s) else (False, arbitrary)"

mapPartial :: "('a => 'b) => 'a partial => 'b partial"
"mapPartial f s == (fst s, f (snd s))"

mapFst :: "('a => 'b) => 'a * 'c => 'b * 'c"
"mapFst f p == (f (fst p), snd p)"

mapSnd :: "('b => 'c) => 'a * 'b => 'a * 'c"
"mapSnd f p == (fst p, f (snd p))"

defOp :: "'a partial => bool"
"defOp p == fst p"

end
