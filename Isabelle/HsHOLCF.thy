theory HsHOLCF
imports "$ISABELLE_HOME/src/HOLCF/IOA/meta_theory/Abstraction"
begin

(*
axclass BoolC < type
axclass IntC < type

instance bool:: BoolC
by intro_classes

instance int:: IntC
by intro_classes
*)

types
dInt = "int lift"

constdefs
fliftbin ::
"('a => 'b => 'c) => ('a lift -> 'b lift -> 'c lift)"
"fliftbin f == flift1 (%x. flift2 (f x))"

fliftbinA ::
"(('a::pcpo) => ('b::pcpo) => ('c::type)) => ('a -> 'b -> 'c lift)"
"fliftbinA f == LAM y. (LAM x. (Def (f y x)))"

consts
hEq :: "'a -> 'a -> tr"
hNEq :: "'a -> 'a -> tr"

axclass Eq < pcpo
  eqAx: "hEq $ p $ q = neg $ (hNEq $ p $ q)"
(*  ALL x::bool.
        (hEq $ p $ q = Def x) = (hNEq $ p $ q = Def (~x))" *)

constdefs
holEq :: "('a::flat) => 'a => tr"
"holEq == %p q.
   if ~(p=UU) & ~(q=UU) then Def (p=q) else UU"
holNEq :: "('a::flat) => 'a => tr"
"holNEq == %p q.
   if ~(p=UU) & ~(q=UU) then Def (p~=q) else UU"

(* auxiliary *)

lemma beta2_cfun:
  "(ALL x. cont (f x)) --> cont (%w1. (LAM w2. f w1 w2)) --> (LAM w1 w2. f w1 w2) $ z1 $ z2 = f z1 z2"
apply auto
done

(* holEq *)

lemma holEq1_UU: "ALL (y::('a::flat)). (%x. holEq x y) UU = UU"
apply (unfold holEq_def)
apply auto
done

lemma holEq2_UU: "ALL (x::('a::flat)). (%y. holEq x y) UU = UU"
apply (unfold holEq_def)
apply auto
done

lemma holEq_cont1: "ALL (y::('a::flat)). cont (%x. holEq x y)"
apply (simp add: holEq1_UU flatdom_strict2cont)
done

lemma holEq_cont2: "cont (holEq x)"
apply (simp add: holEq2_UU flatdom_strict2cont)
done

lemma holEq_cont1C: "cont (%x. (LAM y. holEq x y))"
apply (simp add: holEq_cont2 holEq1_UU flatdom_strict2cont)
done

lemma holEq_beta2: "(LAM x y. holEq x y) $ z1 $ z2 = holEq z1 z2"
apply (simp add: holEq_cont2 holEq_cont1C beta2_cfun)
done

(* holNE *)

lemma holNEq1_UU: "ALL (y::('a::flat)). (%x. holNEq x y) UU = UU"
apply (unfold holNEq_def)
apply auto
done

lemma holNEq2_UU: "ALL (x::('a::flat)). (%y. holNEq x y) UU = UU"
apply (unfold holNEq_def)
apply auto
done

lemma holNEq_cont1: "ALL (y::('a::flat)). cont (%x. holNEq x y)"
apply (simp add: holNEq1_UU flatdom_strict2cont)
done

lemma holNEq_cont2: "cont (holNEq x)"
apply (simp add: holNEq2_UU flatdom_strict2cont)
done

lemma holNEq_cont1C: "cont (%x. (LAM y. holNEq x y))"
apply (simp add: holNEq_cont2 holNEq1_UU flatdom_strict2cont)
done

lemma holNEq_beta2: "(LAM x y. holNEq x y) $ z1 $ z2 = holNEq z1 z2"
apply (simp add: holNEq_cont2 holNEq_cont1C beta2_cfun)
done

(* lift *)

defs
lift_hEq_def: "hEq == LAM (p::('a :: type) lift) q.
   holEq p q"
lift_hNEq_def: "hNEq == LAM (p::('a :: type) lift) q.
   holNEq p q"

instance lift :: (type) Eq
apply (intro_classes, unfold lift_hEq_def lift_hNEq_def)
apply (simp add: holEq_beta2 holNEq_beta2)
apply (unfold holEq_def holNEq_def)
apply (unfold neg_def)
apply auto
done

lemma double_neg: "x = neg $ (neg $ x)"
apply (rule_tac p = "x" in trE)
apply (simp add: Exh_tr neg_thms trE)
apply auto
done

(* llist *)

domain ('a::pcpo) llist = lNil | "###" (lazy lHd :: 'a)
                       (lazy lTl :: "'a llist") (infixr 65)

constdefs
llEq :: "('a::Eq) llist -> 'a llist -> tr"
"llEq == fix $ (LAM hh (xs::('a::Eq) llist) ys.
  if (xs = UU) | (ys = UU) then UU
  else case xs of
       lNil => case ys of
           lNil => TT
          | w###ws => if (w = UU) then UU
                    else FF
      | z###zs => if (z = UU) then UU
          else case ys of
              lNil => FF
             | w###ws => if (w = UU) then UU
                    else (hEq $ z $ w) andalso (hh $ zs $ ws))"

defs
llist_hEq_def: "hEq == llEq"
llist_hNEq_def: "hNEq == LAM x y. neg $ (llEq $ x $ y)"

instance llist :: (Eq) Eq
apply (intro_classes)
apply (unfold llist_hEq_def llist_hNEq_def)
apply auto
apply (simp add:double_neg)
done


(* seq  - not used *)

constdefs
shEq :: "('a::Eq) seq -> 'a seq -> tr"
"shEq == fix $ (LAM hh (xs::('a::Eq) seq) ys.
  if (xs = UU) | (ys = UU) then UU
  else case xs of
       nil => case ys of
           nil => TT
          | w##ws => if (w = UU) then UU
                    else FF
      | z##zs => if (z = UU) then UU
          else case ys of
              nil => FF
             | w##ws => if (w = UU) then UU
                    else (hEq $ z $ w) andalso (hh $ zs $ ws))"

defs
seq_hEq_def: "hEq == shEq"
seq_hNEq_def: "hNEq == LAM x y. neg $ (shEq $ x $ y)"

instance seq :: (Eq) Eq
apply (intro_classes)
apply (unfold seq_hEq_def seq_hNEq_def)
apply auto
apply (simp add:double_neg)
done

(*
constdefs
seq_el :: "('a::pcpo) seq => nat => 'a"
"seq_el xs n == slast $ ((seq_take n) $ xs)"
*)

end
