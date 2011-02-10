theory MainHC
imports Main
begin

-- "we need full proof object support to use translate_thm later on"
ML {* proofs := 2 *}

types 'a partial = "'a option"

(* negation of is_none *)
primrec defOp :: "'a partial => bool"
where
"defOp None = False" |
"defOp (Some x) = True"

definition makeTotal :: "'a partial => 'a"
where "makeTotal == the"

definition makePartial :: "'a => 'a partial"
where "makePartial == Some"

(* undefined is predefined *)
definition undefinedOp :: "'a partial"
where "undefinedOp == None"

(* backward compatibility only *)
definition noneOp :: "'a partial"
where "noneOp == undefinedOp"

definition restrictOp :: "'a partial => bool => 'a partial"
where "restrictOp a b == if b then a else undefinedOp"

(* utilities *)
definition flip :: "('a => 'b => 'c) => 'b => 'a => 'c"
where "flip f a b == f b a"

definition uncurryOp :: "('a => 'b => 'c) => 'a * 'b => 'c"
where "uncurryOp f p == f (fst p) (snd p)"

definition curryOp :: "('a * 'b => 'c) => 'a => 'b => 'c"
where "curryOp f a b == f (a, b)"

(* map on pairs *)
definition mapFst :: "('a => 'b) => 'a * 'c => 'b * 'c"
where "mapFst f p == (f (fst p), snd p)"

definition mapSnd :: "('b => 'c) => 'a * 'b => 'a * 'c"
where "mapSnd f p == (fst p, f (snd p))"

(* predefined HasCASL functions *)
definition ifImplOp :: "bool * bool => bool"
where "ifImplOp p == snd p --> fst p"

definition existEqualOp :: "'a partial => 'a partial => bool" 
  ("(_ =e=/ _)" [50, 51] 50)
where "existEqualOp a b == defOp a & defOp b & makeTotal a = makeTotal b"

definition exEqualOp :: "'a partial * 'a partial => bool"
where "exEqualOp == uncurryOp existEqualOp"

definition strongEqualOp :: "'a partial => 'a partial => bool"
  ("(_ =s=/ _)" [50, 51] 50)
where "strongEqualOp a b == a = b"

definition whenElseOp :: "('a partial * bool) * 'a partial => 'a partial"
where "whenElseOp t == case t of
    (p, e) => if snd p then fst p else e"

(*resOp :: "'a partial * 'b partial => 'a"
"resOp p == makeTotal (restrictOp (fst p) (defOp (snd p)))"*)

definition resOp :: "'a partial * 'b partial => 'a partial"
where  "resOp p == restrictOp (fst p) (defOp (snd p))"


(* conversions *)
definition lift2partial :: "('a => 'b partial) => 'a partial => 'b partial"
where "lift2partial f s == restrictOp (f (makeTotal s)) (defOp s)"

definition mapPartial :: "('a => 'b) => 'a partial => 'b partial"
where "mapPartial f s == restrictOp (makePartial (f (makeTotal s))) (defOp s)"

definition unpackPartial :: "(('a => 'b) => 'c => 'd partial)
            => ('a => 'b) partial => 'c => 'd partial"
where "unpackPartial c s a == lift2partial (flip c a) s"

definition unpackBool :: "(('a => 'b) => 'c => bool)
            => ('a => 'b) partial => 'c => bool"
where "unpackBool c s a == defOp s & c (makeTotal s) a"

definition unpack2partial :: "(('a => 'b) => 'c => 'd)
            => ('a => 'b) partial => 'c => 'd partial"
where "unpack2partial c s a == mapPartial (flip c a) s"

definition unpack2bool :: "(('a => 'b) => 'c => 'd)
            => ('a => 'b) partial => 'c => bool"
where "unpack2bool c s a == defOp s"

definition bool2partial :: "bool => unit partial"
where "bool2partial b == restrictOp (makePartial ()) b"

definition liftUnit2unit :: "('a => 'b) => bool => bool"
where "liftUnit2unit f b == b"

definition liftUnit2bool :: "(unit => bool) => bool => bool"
where "liftUnit2bool f b == b & f ()"

definition liftUnit2partial :: "(unit => 'a partial) => bool => 'a partial"
where "liftUnit2partial f b == restrictOp (f ()) b"

definition liftUnit :: "(unit => 'a) => bool => 'a partial"
where "liftUnit f b ==restrictOp (makePartial (f ())) b"

definition lift2unit :: "('b => 'c) => ('a partial => bool)"
where "lift2unit f == defOp"

definition lift2bool :: "('a => bool) => 'a partial => bool"
where "lift2bool f s == defOp s & f (makeTotal s)"

(* old stuff *)
primrec app :: "('a => 'b option) option => 'a option => 'b option"
where
  "app None a = None" |
  "app (Some f) x = (case x of
                            None => None
                          | Some x' => f x')"

primrec apt :: "('a => 'b) option => 'a option => 'b option"
where
  "apt None a = None" |
  "apt (Some f) x = (case x of
                            None => None
                          | Some x' => Some (f x'))"

primrec pApp :: "('a => bool) option => 'a option => bool"
where
  "pApp None a = False" |
  "pApp (Some f) x = (case x of
                             None => False
                           | Some y => f y)"

primrec pair :: "'a option => 'b option => ('a * 'b) option"
where
  "pair None a = None" |
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

(*
   Identities added by Ewaryst Schulz
*)
(* 
lemma defOp_implies_makePartial:
"defOp(x :: 'a partial) ==> (EX (y :: 'a). x = makePartial y)"
-- "for isabelle 2009"
  by (rule Option.option.exhaust [of x], simp, simp add: exI makePartial_def)
-- "for isabelle 2008"
 by (rule Datatype.option.exhaust [of x], simp, simp add: exI makePartial_def)
-- "for both versions:"
  sorry
*)

axioms

defOp_implies_makePartial:
"defOp(x :: 'a partial) ==> (EX (y :: 'a). x = makePartial y)"


-- "need this to expand a term for application of lemmas"
lemma partial_identity: "!!x. makeTotal(makePartial(x)) = x"
  by (simp add: makeTotal_def makePartial_def)

consts preDefOp :: "'a partial => bool"

axioms

preDefOp_atom[simp]: "preDefOp a = defOp a"

preDefOp_lift[simp]:
"preDefOp (lift2partial f a) = (defOp (lift2partial f a) & preDefOp a)"


end
