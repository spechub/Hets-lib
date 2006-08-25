theory MainHC
imports Main
begin

constdefs

flip :: "('a => 'b => 'c) => 'b => 'a => 'c"
"flip f a b == f b a"

ifImplOp :: "bool * bool => bool"
"ifImplOp p == snd p --> fst p"

exEqualOp :: "'a option * 'a option => bool"
"exEqualOp p == case fst p of
    None => False
  | Some a => (case snd p of
      None => False
    | Some b => a = b)"

whenElseOp :: "('a option * bool) * 'a option => 'a option"
"whenElseOp t == case t of
    (p, e) => if snd p then fst p else e"

unpackOption :: "(('a => 'b option) => 'c => 'd option)
            => ('a => 'b option) option => 'c => 'd option"
"unpackOption c s a == case s of
    None => None
  | Some f => c f a"

unpackBool :: "(('a => bool) => 'c => bool)
            => ('a => bool) option => 'c => bool"
"unpackBool c s a == case s of
    None => False
  | Some f => c f a"

unpack2option :: "(('a => 'b) => 'c => 'd)
            => ('a => 'b) option => 'c => 'd option"
"unpack2option c s a == case s of
    None => None
  | Some f => Some (c f a)"

option2bool :: "'a option => bool"
"option2bool s == case s of
    None => False
  | Some a => True"

unpack2bool :: "(('a => unit) => 'c => unit)
            => ('a => unit) option => 'c => bool"
"unpack2bool c s a == option2bool s"

uncurryOp :: "('a => 'b => 'c) => 'a * 'b => 'c"
"uncurryOp f p == f (fst p) (snd p)"

curryOp :: "('a * 'b => 'c) => 'a => 'b => 'c"
"curryOp f a b == f (a, b)"

bool2option :: "bool => unit option"
"bool2option b == if b then Some () else None"

liftUnit2unit :: "('a => 'b) => bool => bool"
"liftUnit2unit f b == b"

liftUnit2bool :: "(unit => bool) => bool => bool"
"liftUnit2bool f b == if b then f () else False"

liftUnit2option :: "(unit => 'a option) => bool => 'a option"
"liftUnit2option f b == if b then f () else None"

liftUnit :: "(unit => 'a) => bool => 'a option"
"liftUnit f b == if b then Some (f ()) else None"

lift2unit :: "('b => 'c) => ('a option => bool)"
"lift2unit f == option2bool"

lift2bool :: "('a => bool) => 'a option => bool"
"lift2bool f s == case s of
    None => False
  | Some a => f a"

lift2option :: "('a => 'b option) => 'a option => 'b option"
"lift2option f s == case s of
    None => None
  | Some a => f a"

mapSome :: "('a => 'b) => 'a option => 'b option"
"mapSome f s == case s of
    None => None
  | Some a => Some (f a)"

mapFst :: "('a => 'b) => 'a * 'c => 'b * 'c"
"mapFst f p == (f (fst p), snd p)"

mapSnd :: "('b => 'c) => 'a * 'b => 'a * 'c"
"mapSnd f p == (fst p, f (snd p))"

liftFst :: "(('a => 'c) => 'd => 'e) => ('a * 'b => 'c) => 'd * 'b => 'e"
"liftFst f g p == f (flip (curryOp g) (snd p)) (fst p)"

liftSnd :: "(('b => 'c) => 'f => 'g) => ('a * 'b => 'c) => 'a * 'f => 'g"
"liftSnd f g p == f (curryOp g (fst p)) (snd p)"

liftCurSnd ::
"(('b => 'c) => 'f => 'g) => ('a => 'b => 'c) => 'a => 'f => 'g"
"liftCurSnd f g a == f (g a)"

liftCurFst ::
"(('a => 'c) => 'd => 'e) => ('a => 'b => 'c) => 'd => 'b => 'e"
"liftCurFst f g a == (flip f a o flip g)"

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

consts defOp :: "'a option => bool"
primrec
  "defOp (Some x) = True"
  "defOp None     = False"

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
