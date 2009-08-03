theory MainHC
imports Main
begin

types 'a partial = "'a option"

(* negation of is_none *)
consts defOp :: "'a partial => bool"
primrec
"defOp None = False"
"defOp (Some x) = True"

constdefs

makeTotal :: "'a partial => 'a"
"makeTotal == the"

makePartial :: "'a => 'a partial"
"makePartial == Some"

(* undefined is predefined *)
undefinedOp :: "'a partial"
"undefinedOp == None"

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

(*resOp :: "'a partial * 'b partial => 'a"
"resOp p == makeTotal (restrictOp (fst p) (defOp (snd p)))"*)

resOp :: "'a partial * 'b partial => 'a partial"
 "resOp p == restrictOp (fst p) (defOp (snd p))"


(* conversions *)
lift2partial :: "('a => 'b partial) => 'a partial => 'b partial"
"lift2partial f s == restrictOp (f (makeTotal s)) (defOp s)"

mapPartial :: "('a => 'b) => 'a partial => 'b partial"
"mapPartial f s == restrictOp (makePartial (f (makeTotal s))) (defOp s)"

unpackPartial :: "(('a => 'b) => 'c => 'd partial)
            => ('a => 'b) partial => 'c => 'd partial"
"unpackPartial c s a == lift2partial (flip c a) s"

unpackBool :: "(('a => 'b) => 'c => bool)
            => ('a => 'b) partial => 'c => bool"
"unpackBool c s a == defOp s & c (makeTotal s) a"

unpack2partial :: "(('a => 'b) => 'c => 'd)
            => ('a => 'b) partial => 'c => 'd partial"
"unpack2partial c s a == mapPartial (flip c a) s"

unpack2bool :: "(('a => 'b) => 'c => 'd)
            => ('a => 'b) partial => 'c => bool"
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
"liftUnit f b ==restrictOp (makePartial (f ())) b"

lift2unit :: "('b => 'c) => ('a partial => bool)"
"lift2unit f == defOp"

lift2bool :: "('a => bool) => 'a partial => bool"
"lift2bool f s == defOp s & f (makeTotal s)"

(* old stuff *)
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

(* Monad law added by Lutz Schroeder *)

lemma partial_monad_unit1[simp]: "lift2partial f (makePartial a) = f a"
apply (simp add: lift2partial_def makePartial_def restrictOp_def makeTotal_def)
done

lemma partial_monad_unit2[simp]: "lift2partial makePartial m = m"
apply (auto simp add: lift2partial_def makePartial_def restrictOp_def makeTotal_def undefinedOp_def)
apply (case_tac "m")
apply (auto)
apply (case_tac "m")
apply (auto)
done

lemma partial_monad_assoc[simp]:
  "lift2partial g (lift2partial f m) =
  lift2partial (%x. lift2partial g (f x)) m"
apply (simp add: lift2partial_def makePartial_def restrictOp_def makeTotal_def undefinedOp_def)
done

lemma strictness_closure:
  "defOp (lift2partial f a) = (defOp (lift2partial f a) & defOp a)"
apply (simp add: lift2partial_def makePartial_def restrictOp_def makeTotal_def undefinedOp_def)
done

consts preDefOp :: "'a partial => bool"

axioms

preDefOp_atom[simp]: "preDefOp a = defOp a"

preDefOp_lift[simp]:
"preDefOp (lift2partial f a) = (defOp (lift2partial f a) & preDefOp a)"

end
