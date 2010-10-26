theory CSLSemantics imports Main Real Log Ln Taylor -- "the imports taken from Complex_Main"
begin

(* A Remark on deep embeddings:

The key-point is how binders and bound or free variables are represented.

In different papers there are different approaches:

*** Proving the Completeness Theorem within Isabelle/HOL (2004):
Variables are integers, binders use a deBruijn-Index style without mentioning the bound variable
(least variable is bound by a binder, e.g., All (All ((Var 1) = 2*(Var 2))) = !x. !y. y=2*x)



*** Implementing Z in Isabelle (1995):
Z is deeply embedded in a logic based on Isabelle/Pure (not HOL!).

Looks for me rather shallow than deep (apparently Jigsaw is a deeper embedding,
simulating also the substitution machinery, see p.18(371)).

From p.3(356):
"Variable binding is expressed using higher-order abstract syntax.
This enables us to express inference rules involving substitution
for bound variables in such a way that the usual side conditions are automatically respected.
Thus, for instance, the inference rule ForallIntro: P ==> forall x. P
with the side condition that x does not occur free in the assumptions, can be formalized
in Isabelle as:
!! x. Trueprop(P(x)) ==> Trueprop(forall(%x.P(x))) .
"


* A simple setting to reason about

program: "y := x ^ 2"

program-property to prove: "y >= 0"

*)

subsection {* Preliminaries: Functions for term-interpretation  *}

(* datatype T1 = C | T1 "T1 list" *)


-- "power is only defined for natural number exponents"
definition
  realpow :: "real => real => real" where
 "realpow x y == x^natfloor(y)"

-- "list variants of binary min and max. Works only on non-empty argument lists."
definition
  nMin :: "real list => real" where
 "nMin l == foldl min (hd l) l"
definition
  nMax :: "real list => real" where
 "nMax l == foldl max (hd l) l"


subsection {* State, Terms, Programs *}

types State = "int => real"

datatype CSLnullary = Cpi
datatype CSLunary = Cuminus | Csign | Cabs | Csqrt | Cfthrt | Ccos | Csin | Ctan
datatype CSLbinary = Cplus | Cminus | Ctimes | Cdivide | Cpower
datatype CSLnary = Cmin | Cmax

datatype CSLbinaryP = Cle | Clt | Cge | Cgt | Cneq | Ceq | Cconvergence

datatype Term = Const int | Num real | Fun0 CSLnullary
  | Fun1 CSLunary Term | Fun2 CSLbinary Term Term | FunN CSLnary "Term list"

datatype Boolterm = Ctrue | Cfalse | Pred2 CSLbinaryP Term Term
  | Conj Boolterm Boolterm | Disj Boolterm Boolterm | Neg Boolterm

datatype Command = Assign int Term | Seq Command Command
  | IfCond Boolterm Command Command | Repeat Boolterm Command



fun iFun0 :: "CSLnullary => real" where
"iFun0 Cpi = pi"

fun iFun1 :: "CSLunary => (real => real)" where
"iFun1 Cuminus = uminus" |
"iFun1 Csign = sgn" |
"iFun1 Cabs = abs" |
"iFun1 Csqrt = sqrt" |
"iFun1 Cfthrt = sqrt o sqrt" |
"iFun1 Ccos = cos" |
"iFun1 Csin = sin" |
"iFun1 Ctan = tan"

fun iFun2 :: "CSLbinary => (real => real => real)" where
"iFun2 Cplus = plus" |
"iFun2 Cminus = minus" |
"iFun2 Ctimes = times" |
"iFun2 Cdivide = divide" |
"iFun2 Cpower = realpow"

fun iFunN :: "CSLnary => (real list => real)" where
"iFunN Cmin = nMin" |
"iFunN Cmax = nMax" 

fun iPred2 :: "CSLbinaryP => (real => real => bool)" where
"iPred2 Cle = less_eq" |
"iPred2  Clt =  less" |
"iPred2  Cge =  op >=" |
"iPred2  Cgt =  op >" |
"iPred2  Cneq =  op ~=" |
"iPred2  Ceq = op ="


fun iTerm :: "State => Term => real" where
"iTerm s (Const i) = s i" |
"iTerm _ (Num r) = r" |
"iTerm s (Fun0 c) = iFun0 c" |
"iTerm s (Fun1 c t) = iFun1 c (iTerm s t)" |
"iTerm s (Fun2 c t u) = iFun2 c (iTerm s t) (iTerm s u)" |
"iTerm s (FunN c l) = iFunN c (map (iTerm s) l)"

-- "Because the convergence predicate depends on a before- and after-state we need to pass two states to this function"
fun iBoolterm :: "State => State => Boolterm => bool" where
"iBoolterm _ _ Ctrue = True" |
"iBoolterm _ _ Cfalse = False" |
"iBoolterm s s' (Pred2 Cconvergence t u) = 
  (let tBefore = iTerm s t;
       tAfter = iTerm s' t;
       uVal = iTerm s' u
   in abs(tBefore - tAfter) <= uVal)" |
"iBoolterm _ s' (Pred2 c t u) =  iPred2 c (iTerm s' t) (iTerm s' u)" |
"iBoolterm s s' (Conj p q) = (iBoolterm s s' p & iBoolterm s s' q)" |
"iBoolterm s s' (Disj p q) = (iBoolterm s s' p | iBoolterm s s' q)" |
"iBoolterm s s' (Neg p) = Not (iBoolterm s s' p)"

function iCommand :: "State => Command => State" where
"iCommand s (IfCond p c1 c2) = (if iBoolterm s s p then iCommand s c1 else iCommand s c2)" |
"iCommand s (Assign i t) = (%x . if x = i then iTerm s t else s x)" |
"iCommand s (Seq c1 c2) = (let s' = iCommand s c1 in iCommand s' c2)" |
"iCommand s (Repeat p c) = (let s' = iCommand s c in (if iBoolterm s s' p then s' else iCommand s' (Repeat p c)))"
  by pat_completeness auto
(* alternatively
  by (auto, case_tac "b", auto)
*)


subsection {* The Assignment Store *}

fun constsOf :: "Term => int set" where
"constsOf (Num n) = {}" |
"constsOf (Const i) = {i}" |
"constsOf (Fun0 c) = {}" |
"constsOf (Fun1 c t) = constsOf t" |
"constsOf (Fun2 c t u) = constsOf t Un constsOf u" |
"constsOf (FunN c l) = Union (set (map constsOf l))"


types ConstantTermAssignments = "int ~=> Term"

definition
  -- "flat dependency for the given constant when lookuped in the CTA"
  constsOfLookuped :: "ConstantTermAssignments => int => int set" where
 "constsOfLookuped f i == (case f i of
                            Some t => constsOf t |
                            _ => {})"

definition
  -- "flat dependency relation, not transitive by construction"
  depOrder1 :: "ConstantTermAssignments => (int*int) set" where
 "depOrder1 f == {(x, y) | x y . y: constsOfLookuped f x}"

definition
  -- "transitive closure of depOrder1"
  depOrder :: "ConstantTermAssignments => (int*int) set" where
 "depOrder f == (depOrder1 f)^+"

definition
  -- "set of constants the current term (recursively) depends on"
  dependsOn :: "ConstantTermAssignments => Term => int set" where
 "dependsOn f t == Image (depOrder f) (constsOf t)"

-- "An AssignmentStore is a finite ConstantTermAssignments without cycles"
definition AS_set :: "ConstantTermAssignments set" where
          "AS_set == {f. let ord = depOrder f in wf ord & finite ord}"

lemma emptyAS_has_empty_dep_order : "depOrder empty == {}"
  by (simp add: depOrder1_def depOrder_def constsOfLookuped_def)

lemma emptyAS_in_AS': "empty : AS_set"
  by (simp add: emptyAS_has_empty_dep_order AS_set_def)

typedef (AS) AssignmentStore = AS_set
  morphisms asCTA toAS
  by (rule exI[of _ empty], simp only: emptyAS_in_AS')

lemma emptyAS_in_AS: "empty : AS"
  by (simp add: emptyAS_in_AS' AS_def)


function fullexpand :: "AssignmentStore => Term => Term" where
"fullexpand _ (Num r) = Num r" |
"fullexpand as (Const i) = (case (asCTA as) i of
                              Some y => fullexpand as y
                            | None => Const i)" |
"fullexpand _ (Fun0 c) = Fun0 c" |
"fullexpand as (Fun1 c t) = Fun1 c (fullexpand as t)" |
"fullexpand as (Fun2 c t u) = Fun2 c (fullexpand as t) (fullexpand as u)" |
"fullexpand as (FunN c l) = FunN c (map (fullexpand as) l)"
  by pat_completeness auto

(* 
 fullexpand is total essentially because the lookup in the
 Const-case is terminating because of the wellfoundness of "as" and
 the recursion on the structure of Term also terminates
 *)
lemma fullexpand_is_total : "!! as t . fullexpand_dom (as, t)"
  sorry

(* arg_cong and fun_cong are the crucial axioms
lemma T1:
  assumes H0: "f x = g"
  shows "!!i. f x i = g i"
by (rule arg_cong, simp add: H0)
by (rule fun_cong, simp add: H0)
*)

lemma fullexpand_disjoint_as_identity':
  "(!x. x : constsOf t --> (asCTA as) x = None) --> fullexpand as t = t"
  by (rule fullexpand.pinduct[OF fullexpand_is_total], auto simp add: fullexpand_is_total, rule map_idI, auto)

lemma fullexpand_disjoint_as_identity:
  "(!!x. x : constsOf t ==> (asCTA as) x = None) ==> fullexpand as t = t"
  using fullexpand_disjoint_as_identity' by simp

lemma "!!t . fullexpand (toAS empty) t = t"
  using fullexpand_disjoint_as_identity toAS_inverse emptyAS_in_AS by simp


nonterminals
  updbinds2 updbind2
syntax
  "_updbind2" :: "['a, 'a] => updbind2"             ("(2_ ::=/ _)")
  ""         :: "updbind2 => updbinds2"             ("_")
  "_updbinds2":: "[updbind2, updbinds2] => updbinds2" ("_,/ _")
  "_Update2"  :: "['a, updbinds2] => 'a"            ("_/'((_)')" [1000,0] 900)

translations
  "_Update2 f (_updbinds2 b bs)"  == "_Update2 (_Update2 f b) bs"
  "f(x::=y)"                     == "toAS ((asCTA f)(x |-> y))"


-- "If we encounter a cycle in an assignment we return None"
fun iProg :: "AssignmentStore => Command ~=> AssignmentStore" where
   "iProg as (Assign i t) = (let t' = fullexpand as t
                             in if i : constsOf t' then None else Some (as(i ::= t')))" |
   "iProg as (Seq c c') = (case iProg as c of
                             Some as' => iProg as' c'
                           | None => None)"

subsection {* Respectful States *}

definition respectsAS :: "State => AssignmentStore => bool" (infixl "resp" 50) where
         "s resp as == !x t . (asCTA as) x = Some t --> s x = iTerm s t"

theorem State_AssertionStore_interpretation_respect_preserving:
  "[|s resp as; iProg as p = Some as'|] ==> (iCommand s p) resp as'"
  sorry

theorem iTerm_invariant_under_full_expansion:
  "s resp as ==> !t. iTerm s t = iTerm s (fullexpand as t)"
proof-
  fix s as
  assume H0: "s resp as"
  show ?thesis
    sorry
(* continue work here:

    apply (rule allI, induct_tac "t")
    apply(simp add: fullexpand_is_total fullexpand.psimps)
    apply (case_tac "asCTA as int")
    proof-
      fix i
      assume H1: "asCTA as i = None"
      hence H2: "(case (asCTA as) i of
                   Some y => fullexpand as y
                 | None => Const i)=Const i" (is "?cc = ?ci")
	by simp
      have "s i = iTerm s (Const i)" by simp
      also have "... = iTerm s ?cc" by (simp add: H2)

      -- "TODO: show macht probleme!"
      finally show "s i = iTerm s ?cc"
*)


constdefs c3 :: Command -- "The command for  x := 0; x := x + 1"
         "c3 == Seq (Assign 1 (Num 0)) (Assign 1 (Add (Const 1) (Num 1)))"

constdefs p3 :: ProgCond -- "The property for  x > 0"
         "p3 == Gt (Const 1) (Num 0)"

lemma soundProg3:
  "!! s :: State . 
   let s' = iCommand s c3
   in iProgCond s' p3"
