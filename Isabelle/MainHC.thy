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
