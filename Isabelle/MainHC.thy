theory MainHC = Main:

constdefs
uncurryOp :: "('a => 'b => 'c) => 'a * 'b => 'c"
"uncurryOp f p == f (fst p) (snd p)"

pairL :: "'a option => 'b => ('a * 'b) option"
"pairL l b == case l of 
    None => None
  | Some a => Some (a, b)"

pairR :: "'a => 'b option => ('a * 'b) option"
"pairR a r == case r of 
    None => None
  | Some b => Some (a, b)"

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

app :: "('a => 'b option) option => 'a option => 'b option"
"app s t == case s of
    None => None
  | Some f => (case t of
      None => None
    | Some a => f a)"

apt :: "('a => 'b) option => 'a option => 'b option"
"apt s t == case s of
    None => None
  | Some f => (case t of
      None => None
    | Some a => Some (f a))"

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

pApp :: "('a => bool) option => 'a option => bool"
"pApp s t == case s of
    None => False
  | Some f => (case t of
      None => False
    | Some a => f a)"

defOp1 :: "'a => bool"
"defOp1 a == True"

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
