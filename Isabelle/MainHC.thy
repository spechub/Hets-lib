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


(*
   A facility to reason about subtypes

This doesn't work, because Isabelle doesn't allow polymorphic constants in the
fixes list, i.e., the 'a and 'b are constant inside the context of the locale!
*)

(*
locale subtype = 
  fixes
  iaa :: "'a => 'a"
  and iab :: "'a => 'b"
  and ibc :: "'b => 'c"
  and iac :: "'a => 'c"
  and pba :: "'b => 'a partial"
  and pab :: "'a => 'b partial"
  and saa :: "'a => 'a => bool"
  and sbb :: "'b => 'b => bool"
  and scc :: "'c => 'c => bool"
  and sab :: "'a => 'b => bool"
  and sbc :: "'b => 'c => bool"
  and sac :: "'a => 'c => bool"

  assumes

  refl_a :
  "!!x y. saa x y"
  and refl_b :
  "!!x y. sbb x y"
  and refl_c :
  "!!x y. scc x y"

  and trans_abc :
  "!! x y z. sab x y & sbc y z ==> sac x z"
  and trans_aab :
  "!! x y z. saa x y & sab y z ==> sab x z"
  and trans_bbc :
  "!! x y z. sbb x y & sbc y z ==> sbc x z"
  and trans_acc :
  "!! x y z. sac x y & scc y z ==> sac x z"

  and inj_proj :
  "ALL x y. sab x y --> y = iab(x) = (makePartial x = pba(y))"

  and inj_trans :
  "ALL x. ALL y. ALL z. sab x y & sbc y z & y = iab(x) -->
  (z = iac(x)) = (z = ibc(y))"

begin

lemma subtype_reflexive:
"saa (x:: 'a) (y:: 'a)" by (simp only: refl_a)

lemma subtype_transitive:
"[| sab (x:: 'a) (y:: 'b); sbc (z:: 'b) (t:: 'c) |]  ==> sac (u:: 'a) (v:: 'c)"
proof-
  assume hypAB: "sab (x:: 'a) (y:: 'b)"
  assume hypBC: "sbc (z:: 'b) (t:: 'c)"
  have A: "sab u y" by (rule trans_aab [of u x y], simp add: refl_a hypAB)
  have B: "sbc y t" by (rule trans_bbc [of y z t], simp add: refl_b hypBC)
  have C: "sac u t" by (rule trans_abc [of u y t], simp add: A B)
  show "sac u v" by (rule trans_acc [of u t v], simp add: refl_c C)
qed

-- " until here this can be checked "


-- "necessary when omitting the quantifiers in the axioms below"
lemma subtype_constant:
"X_gn_subt (x:: 'a) (y:: 'b) ==> (!!(u:: 'a) v:: 'b. X_gn_subt u v)"
proof-
  assume hyp: "X_gn_subt x y"
  fix u:: 'a
  fix v:: 'b
  show "X_gn_subt u v" by (rule subtype_transitive [of x x x y u v], simp add: ga_subt_reflexive hyp)
qed


-- "INJECTION PROJECTION RULES"

lemma gn_proj_inj:
"X_gn_subt (x:: 'a) (y:: 'b) ==> (!!(z:: 'a). makePartial(z) = gn_proj(gn_inj(z):: 'b))"
proof-
  assume hyp: "X_gn_subt x y"
  fix z :: 'a

  have "(gn_inj(z) :: 'b) = gn_inj(z) = (makePartial z = gn_proj(gn_inj(z) :: 'b))"
    by (rule ga_subt_inj_proj, rule subtype_constant [of x y], simp only: hyp)
  thus "makePartial z = gn_proj(gn_inj(z) :: 'b)" by simp
qed

lemma gn_makeTotal_proj_inj:
"X_gn_subt (x:: 'a) (y:: 'b) ==> (!!(z:: 'a). makeTotal(gn_proj(gn_inj(z):: 'b)) = z)"
 by (simp only: partial_identity gn_proj_inj [symmetric])


-- "is used to derive defining predicate P for a subtype A, P(gn_inj(x::A))"
lemma gn_proj_def:
"X_gn_subt (x:: 'a) (y:: 'b) ==> defOp(gn_proj(gn_inj(x):: 'b):: 'a partial)"
proof-
  assume hyp: "gn_subt(x, y)"
  hence A: "makePartial(x) = gn_proj(gn_inj(x):: 'b)" by (rule gn_proj_inj [of x y x])
  show "defOp(gn_proj(gn_inj(x):: 'b):: 'a partial)"
    by (simp add: A [symmetric] makePartial_def)
qed

lemma gn_inj_proj:
"X_gn_subt (x:: 'a) (y:: 'b) ==> (!!(z:: 'b). defOp(gn_proj(z):: 'a partial) ==>
  gn_inj(makeTotal(gn_proj(z):: 'a partial)) = z)"
proof-
  assume hyp: "gn_subt(x, y)"
  fix z :: 'b
  assume hyp': "defOp(gn_proj(z):: 'a partial)"
  have "EX (t :: 'a). gn_proj(z) = makePartial t"
    by (rule defOp_implies_makePartial [of "gn_proj(z)"], simp only: hyp')
  then obtain t :: 'a where eq1: "makePartial t = gn_proj(z)" by auto
  from hyp have A: "gn_subt(t, z)" by (simp only: subtype_constant)
  have B: "t=makeTotal(gn_proj(gn_inj(t):: 'b)) "
    by (rule gn_makeTotal_proj_inj [symmetric,of x y], simp only: hyp)
  have C: "z = gn_inj(t)"
    by (simp only: ga_subt_inj_proj subtype_reflexive A eq1)
  also have "\<dots> = gn_inj(makeTotal(gn_proj(gn_inj(t):: 'b)):: 'a)"
    by (subst B, simp)
  also have "\<dots> = gn_inj(makeTotal(gn_proj(z)):: 'a)" by (simp only: C)
  finally show "gn_inj(makeTotal(gn_proj(z)):: 'a) = z" ..
qed


lemma gn_inj_diagram:
"[| X_gn_subt (x:: 'a) (y:: 'b); X_gn_subt (z:: 'b) (t:: 'c) |]
  ==> (!!(x':: 'a). (gn_inj(x'):: 'c) = gn_inj(gn_inj(x'):: 'b))"
proof-
  assume hypAB: "X_gn_subt (x:: 'a) (y:: 'b)"
  assume hypBC: "X_gn_subt (z:: 'b) (t:: 'c)"
  fix x' :: 'a

  def y_def: y' == "gn_inj(x'):: 'b"
  def z_def: z' == "gn_inj(x'):: 'c"

  from hypAB hypBC have A: "gn_subt(x',y') \<and> gn_subt(y',z')"
    by (simp add: subtype_constant)

  have B: "(z' = gn_inj(x')) = (z' = gn_inj(y'))"
    by (rule ga_inj_transitive [of x' y' z'], simp only: A, simp add: y_def)

  show "(gn_inj(x'):: 'c) = gn_inj(gn_inj(x'):: 'b)"
    by (simp only:  y_def [symmetric] z_def [symmetric], subst B [symmetric]
      , simp only: z_def)
qed

lemma gn_inj_injective :
  "X_gn_subt (u :: 'a) (v:: 'b) ==> inj (X_gn_inj :: 'a => 'b)"
  proof (rule injI)
    fix x:: 'a
    fix y:: 'a
    assume hyp1: "X_gn_subt (u:: 'a) (v:: 'b)"
      and hyp2: "(X_gn_inj x :: 'b) = X_gn_inj y"

    from hyp1 subtype_constant 
    have fact: "!!(z:: 'a). makeTotal(gn_proj(gn_inj(z):: 'b)) = z"
      by (rule_tac gn_makeTotal_proj_inj, blast)

    hence "x = makeTotal(gn_proj(gn_inj(x):: 'b))" ..
    also from hyp2 have "... = makeTotal(gn_proj(gn_inj(y):: 'b))" by simp
    also from fact have "... = y" by simp
    finally show "x = y" by simp
  qed

lemma gn_inj_identity :
"!!x:: 'a. (gn_inj(x):: 'a) = x"
proof-
  fix x:: 'a
  have fact: "(gn_inj(x):: 'a) = gn_inj(gn_inj(x):: 'a)"
    by (simp_all add: gn_inj_diagram subtype_reflexive)
  thus "(gn_inj(x):: 'a) = x"
    by (subst injD [of "(X_gn_inj:: 'a=>'a)" "(gn_inj(x):: 'a)" x],
      simp_all only: gn_inj_injective subtype_reflexive fact [symmetric])
qed

end
*)

end
