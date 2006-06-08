theory MainHC
imports Main
begin

constdefs
unpackOp :: "(('a => 'b) => 'c => 'd) => ('a => 'b) option => 'c => 'd option"
"unpackOp c s a == case s of
    None => None
  | Some f => Some (c f a)"

uncurryOp :: "('a => 'b => 'c) => 'a * 'b => 'c"
"uncurryOp f p == f (fst p) (snd p)"

curryOp :: "('a * 'b => 'c) => 'a => 'b => 'c"
"curryOp f a b == f (a, b)"

flipOp :: "('a => 'b => 'c) => 'b => 'a => 'c" 
"flipOp f a b == f b a"

option2bool :: "'a option => bool"
"option2bool s == case s of 
    None => False
  | Some a => True"

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

(* pApp2 *)
lift2bool :: "('a => bool) => 'a option => bool" 
"lift2bool f s == case s of
    None => False
  | Some a => f a"

(* appl1 *)
lift2option :: "('a => 'b option) => 'a option => 'b option" 
"lift2option f s == case s of
    None => None
  | Some a => f a"

mapSome :: "('a => 'b) => 'a option => 'b option"
"mapSome f s == case s of 
    None => None 
  | Some a => Some (f a)" 

liftFst :: "(('a => 'c) => 'd => 'e) => ('a * 'b => 'c) => 'd * 'b => 'e"
"liftFst f g p == f (flipOp (curryOp g) (snd p)) (fst p)"

liftSnd :: "(('b => 'c) => 'f => 'g) => ('a * 'b => 'c) => 'a * 'f => 'g"
"liftSnd f g p == f (curryOp g (fst p)) (snd p)"

liftPair :: "(('a => 'c) => 'd => 'e) => (('b => 'e) => 'f => 'g) 
             => ('a * 'b => 'c) => 'd * 'f => 'g"
"liftPair f g == liftSnd g o liftFst f"

pairL :: "'a option => 'b => ('a * 'b) option"
"pairL l b == case l of 
    None => None
  | Some a => Some (a, b)"

pairR :: "'a => 'b option => ('a * 'b) option"
"pairR a r == case r of 
    None => None
  | Some b => Some (a, b)"

lift :: "('a option => 'b option) => 'a => 'b option"
"lift g a == g (Some a)"

appl1 :: "('a => 'b option) => 'a option => 'b option"
"appl1 f s == case s of
    None => None
  | Some a => f a"

appl3 :: "('a => 'b) => 'a option => 'b option"
"appl3 f s == case s of
    None => None
  | Some a => Some (f a)"

appl5 :: "('a => 'b option) option => 'a => 'b option"
"appl5 s a == case s of
    None => None
  | Some f => f a"

appl7 :: "('a => 'b) option => 'a => 'b option"
"appl7 s a == case s of
    None => None
  | Some f => Some (f a)"

pApp1 :: "('a => bool) option => 'a => bool"
"pApp1 s a == case s of
    None => False
  | Some f => f a"

pApp2 :: "('a => bool) => 'a option => bool"
"pApp2 f s == case s of
    None => False
  | Some a => f a"

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
