theory MainHC
imports Main
begin

types 'a partial = "'a option"

constdefs

flip :: "('a => 'b => 'c) => 'b => 'a => 'c"
"flip f a b == f b a"

ifImplOp :: "bool * bool => bool"
"ifImplOp p == snd p --> fst p"

existEqualOp :: "'a partial => 'a partial => bool" ("(_ =e=/ _)" [50, 51] 50)
"existEqualOp a b == case a of
    None => False
  | Some c => (case b of
      None => False
    | Some d => c = d)"

strongEqualOp :: "'a partial => 'a partial => bool" ("(_ =s=/ _)" [50, 51] 50)
"strongEqualOp a b == a = b"

whenElseOp :: "('a partial * bool) * 'a partial => 'a partial"
"whenElseOp t == case t of
    (p, e) => if snd p then fst p else e"

makeTotal :: "'a partial => 'a"
"makeTotal s == case s of
    None => arbitrary
  | Some a => a"

makePartial :: "'a => 'a partial"
"makePartial == Some"

resOp :: "'a partial * 'b partial => 'a"
"resOp p == case snd p of
     None => arbitrary
   | Some _ => makeTotal (fst p)"

noneOp :: "'a partial"
"noneOp == None"

unpackPartial :: "(('a => 'b partial) => 'c => 'd partial)
            => ('a => 'b partial) partial => 'c => 'd partial"
"unpackPartial c s a == case s of
    None => None
  | Some f => c f a"

unpackBool :: "(('a => bool) => 'c => bool)
            => ('a => bool) partial => 'c => bool"
"unpackBool c s a == case s of
    None => False
  | Some f => c f a"

unpack2partial :: "(('a => 'b) => 'c => 'd)
            => ('a => 'b) partial => 'c => 'd partial"
"unpack2partial c s a == case s of
    None => None
  | Some f => Some (c f a)"

partial2bool :: "'a partial => bool"
"partial2bool s == case s of
    None => False
  | Some a => True"

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
"bool2partial b == if b then makePartial () else noneOp"

liftUnit2unit :: "('a => 'b) => bool => bool"
"liftUnit2unit f b == b"

liftUnit2bool :: "(unit => bool) => bool => bool"
"liftUnit2bool f b == if b then f () else False"

liftUnit2partial :: "(unit => 'a partial) => bool => 'a partial"
"liftUnit2partial f b == if b then f () else noneOp"

liftUnit :: "(unit => 'a) => bool => 'a partial"
"liftUnit f b == if b then makePartial (f ()) else noneOp"

lift2unit :: "('b => 'c) => ('a partial => bool)"
"lift2unit f == partial2bool"

lift2bool :: "('a => bool) => 'a partial => bool"
"lift2bool f s == case s of
    None => False
  | Some a => f a"

lift2partial :: "('a => 'b partial) => 'a partial => 'b partial"
"lift2partial f s == case s of
    None => None
  | Some a => f a"

mapPartial :: "('a => 'b) => 'a partial => 'b partial"
"mapPartial f s == case s of
    None => None
  | Some a => Some (f a)"

mapFst :: "('a => 'b) => 'a * 'c => 'b * 'c"
"mapFst f p == (f (fst p), snd p)"

mapSnd :: "('b => 'c) => 'a * 'b => 'a * 'c"
"mapSnd f p == (fst p, f (snd p))"

consts defOp :: "'a option => bool"
primrec
"defOp None = False"
"defOp (Some x) = True"

consts app :: "('a => 'b option) option => 'a option => 'b option"
primrec
  "app None a = None"
  "app (Some f) x = (case x of
                            None => None
                          | Some x' => f x')"

consts apt :: "('a => 'b) option => 'a option => 'b option"
primrec
  "apt None a = None"
  "apt (Some f) x = (case x of
                            None => None
                          | Some x' => Some (f x'))"

consts pApp :: "('a => bool) option => 'a option => bool"
primrec
  "pApp None a = False"
  "pApp (Some f) x = (case x of
                             None => False
                           | Some y => f y)"

consts pair :: "'a option => 'b option => ('a * 'b) option"
primrec
  "pair None a = None"
  "pair (Some x) z = (case z of
                             None => None
                           | Some y => Some (x,y))"

lemma some_inj : "Some x = Some y ==> x = y"
apply (auto)
done

end
