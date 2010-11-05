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
  | Conj Boolterm Boolterm (infixl "&&" 35) | Disj Boolterm Boolterm (infixl "||" 30) | Neg Boolterm

datatype Command = Assign int Term (infix ":=" 30) | Seq Command Command
  | IfCond Boolterm Command Command | Repeat Boolterm Command

(*
ML {* Display.print_syntax (the_context()) *}

*)

constdefs true :: bool
  "true == True"
  false :: bool
  "false == False"

nonterminals
  semiargs glyx



syntax
  "_semiargs2" :: "['a, 'a] => semiargs"             ("_;/ _" [10, 10] 9)
  "_semiargs" :: "['a, semiargs] => semiargs"        ("_;/ _" [10, 9] 9)

  "_cslle" :: "[glyx, glyx]\<Rightarrow>glyx" (infix "<=" 50)
  "_csllt" :: "[glyx, glyx]\<Rightarrow>glyx" (infix "<" 50)
  "_cslge" :: "[glyx, glyx]\<Rightarrow>glyx" (infix ">=" 50)
  "_cslgt" :: "[glyx, glyx]\<Rightarrow>glyx" (infix ">" 50)
  "_csleq" :: "[glyx, glyx]\<Rightarrow>glyx" (infix "=" 50)
  "_cslneq" :: "[glyx, glyx]\<Rightarrow>glyx" (infix "~=" 50)

  "_cslplus" :: "[glyx, glyx]\<Rightarrow>glyx" (infixl "+" 65)
  "_cslminus" :: "[glyx, glyx]\<Rightarrow>glyx" (infixl "-" 65)
  "_csltimes" :: "[glyx, glyx]\<Rightarrow>glyx" (infixl "*" 70)
  "_csldivide" :: "[glyx, glyx]\<Rightarrow>glyx" (infixl "'/" 70)
  "_cslpower" :: "[glyx, glyx]\<Rightarrow>glyx" (infixl "^" 75)

  "_csluminus" :: "glyx\<Rightarrow>glyx"     ("(- _)" [81] 80)

  "_isatrue" :: "'a"             ("True" 1000)
  "_isafalse" :: "'a"            ("False" 1000)
  "_csltrue" :: "glyx"             ("True" 1000)
  "_cslfalse" :: "glyx"            ("False" 1000)
  "_cslneg" :: "glyx\<Rightarrow>glyx"        ("(~_)" [40] 40)

  "" :: "glyx \<Rightarrow> 'a" ("_") -- "We need this for glyx to be valid terms"
  "" :: "'a \<Rightarrow> glyx" ("_")
(*
  "_cslle" :: "['a, 'a]\<Rightarrow>'a" (infix "<<=" 50)
  "_csllt" :: "['a, 'a]\<Rightarrow>'a" (infix "<<" 50)
  "_cslge" :: "['a, 'a]\<Rightarrow>'a" (infix ">>=" 50)
  "_cslgt" :: "['a, 'a]\<Rightarrow>'a" (infix ">>" 50)
  "_csleq" :: "['a, 'a]\<Rightarrow>'a" (infix "===" 50)
  "_cslneq" :: "['a, 'a]\<Rightarrow>'a" (infix "~==" 50)

  "_cslplus" :: "['a, 'a]\<Rightarrow>'a" (infixl "+++" 65)
  "_cslminus" :: "['a, 'a]\<Rightarrow>'a" (infixl "--" 65)
  "_csltimes" :: "['a, 'a]\<Rightarrow>'a" (infixl "**" 70)
  "_csldivide" :: "['a, 'a]\<Rightarrow>'a" (infixl "'/'/'/" 70)
  "_cslpower" :: "['a, 'a]\<Rightarrow>'a" (infixl "^^" 75)

  "_csluminus" :: "'a\<Rightarrow>'a"     ("(-- _)" [81] 80)
*)


  "_cslpi" :: "'a"             ("Pi" 999)
  "_cslsign" :: "'a\<Rightarrow>'a"       ("(sign'(_'))" 999)
  "_cslabs" :: "'a\<Rightarrow>'a"        ("(abs'(_'))" 999)
  "_cslsqrt" :: "'a\<Rightarrow>'a"       ("(sqrt'(_'))" 999)
  "_cslfthrt" :: "'a\<Rightarrow>'a"      ("(fthrt'(_'))" 999)
  "_cslsin" :: "'a\<Rightarrow>'a"        ("(sin'(_'))" 999)
  "_cslcos" :: "'a\<Rightarrow>'a"        ("(cos'(_'))" 999)
  "_csltan" :: "'a\<Rightarrow>'a"        ("(tan'(_'))" 999)

  "_cslconv" :: "['a, 'a]\<Rightarrow>'a" ("(convergence'(_, _'))" 999)

  "_cslmin" :: "args\<Rightarrow>'a"      ("(min'(_'))" 999)
  "_cslmax" :: "args\<Rightarrow>'a"      ("(max'(_'))" 999)

  "" :: "semiargs \<Rightarrow> 'a" ("_") -- "We need this for a sequence to be a logical"

  -- "We need to write the rule for repeat here because the arguments are switched"
  "_cslrepeat" :: "['a, 'a]\<Rightarrow>'a"              ("(repeat _ until _)" [9, 20] 10)

translations

(*
  "_cslle x y"              == "Pred2 Cle x y"
  "_csllt x y"              == "Pred2 Clt x y"
  "_cslge x y"              == "Pred2 Cge x y"
  "_cslgt x y"              == "Pred2 Cgt x y"
  "_csleq x y"              == "Pred2 Ceq x y"
  "_cslneq x y"             == "Pred2 Cneq x y"

  "_cslplus x y"            == "Fun2 Cplus x y"
  "_cslminus x y"           == "Fun2 Cminus x y"
  "_csltimes x y"           == "Fun2 Ctimes x y"
  "_csldivide x y"          == "Fun2 Cdivide x y"
  "_cslpower x y"           == "Fun2 Cpower x y"

  "_csluminus x"            == "Fun1 Cuminus x"
*)
  "_cslle x y"              == "Pred2 Cle x y"
  "_csllt x y"              == "Pred2 Clt x y"
  "_cslge x y"              == "Pred2 Cge x y"
  "_cslgt x y"              == "Pred2 Cgt x y"
  "_csleq x y"              == "Pred2 Ceq x y"
  "_cslneq x y"             == "Pred2 Cneq x y"

  "_cslplus x y"            == "Fun2 Cplus x y"
  "_cslminus x y"           == "Fun2 Cminus x y"
  "_csltimes x y"           == "Fun2 Ctimes x y"
  "_csldivide x y"          == "Fun2 Cdivide x y"
  "_cslpower x y"           == "Fun2 Cpower x y"

  "_csluminus x"            == "Fun1 Cuminus x"

  "sign(x)"                 == "Fun1 Csign x"
  "abs(x)"                  == "Fun1 Cabs x"
  "sqrt(x)"                 == "Fun1 Csqrt x"
  "fthrt(x)"                == "Fun1 Cfthrt x"
  "sin(x)"                  == "Fun1 Csin x"
  "cos(x)"                  == "Fun1 Ccos x"
  "tan(x)"                  == "Fun1 Ctan x"

  "min(x)"                  == "FunN Cmin [x]"
  "min(x,xs)"               == "FunN Cmin (concat x xs)"
  "max(x)"                  == "FunN Cmax [x]"
  "max(x,xs)"               == "FunN Cmax (concat x xs)"

  "Pi"                      == "Fun0 Cpi"
  "_isatrue"                == "true"
  "_isafalse"               == "false"
  "_csltrue"                == "Ctrue"
  "_cslfalse"               == "Cfalse"
  "_cslneg x"               == "Neg x"
  "_Numeral x"              == "Num x"

  "_cslrepeat b u" == "Repeat u b"
  "_semiargs2 x y" == "Seq x y"
  "_semiargs x y" == "Seq x y"


term "!x. f(FF && (TT && (FF || - abs(x + x / Pi) <= (Pi+ Pi + max(Pi)))))"

(*
term "!x. f(FF && (TT && (FF || -- abs(x+++ x /// Pi) <<= (Pi+++ Pi +++ max(Pi)))))"
*)

term "x:=a;x:=a"
term "x:=a;x:=a;x:=a"
term "x:=a;x:=a;x:=a;x:=a"
(*
term "x:=a; repeat y:=c;z:=c until Const x >> Pi; x:=a"
term "x:=a; repeat y:=c;z:=c until Const x >> Pi; repeat y:=c;repeat y:=c;z:=c until Const x >> Pi until Const x >> Pi"

ML {* Display.print_syntax (the_context()) *}
*)
term "(x::Term)<u"
term "(x::real) < b"

term "x:=a;x:=a"
term "x:=a;x:=a;x:=a"
term "x:=a;x:=a;x:=a;x:=a"
term "x:=a; repeat y:=c;z:=c until Const x > Pi; x:=a"
term "x:=a; repeat y:=c;z:=c until Const x > Pi; repeat y:=c;repeat y:=c;z:=c until Const x > Pi until Const x > Pi"

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

(*
ML {* Display.print_syntax (the_context()) *}
*)

ML {* @{term "!y::real. x <= y"} *}
fun iTerm :: "State => Term => real" where
"iTerm s (Const i) = s i" |
"iTerm s (Num r) = r" |
"iTerm s (Fun0 c) = iFun0 c" |
"iTerm s (Fun1 c t) = iFun1 c (iTerm s t)" |
"iTerm s (Fun2 c t u) = iFun2 c (iTerm s t) (iTerm s u)" |
"iTerm s (FunN c l) = iFunN c (map (iTerm s) l)"

-- "Because the convergence predicate depends on a before- and after-state we need to pass two states to this function"
-- "The second state is always the current state"
fun iBoolterm :: "State => State => Boolterm => bool" where
"iBoolterm s s' Ctrue = True" |
"iBoolterm s s' Cfalse = False" |
"iBoolterm s s' (Pred2 Cconvergence t u) = 
  (let tBefore = iTerm s t;
       tAfter = iTerm s' t;
       uVal = iTerm s' u
   in abs (tBefore - tAfter) <= uVal)" |
"iBoolterm s s' (Pred2 c t u) =  iPred2 c (iTerm s' t) (iTerm s' u)" |
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
"fullexpand as (Num r) = Num r" |
"fullexpand as (Const i) = (case (asCTA as) i of
                              Some y => fullexpand as y
                            | None => Const i)" |
"fullexpand as (Fun0 c) = Fun0 c" |
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

ML {* print_mode *}


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
qed
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


ML {* Display.print_syntax (the_context()) *}
ML {* ProofDisplay.print_theory (the_context()) *}
ML {* ProofDisplay.print_theory (theory "Main") *}

constdefs c3 :: Command -- "The command for  x := 0; x := x + 1"
         "c3 == 1 := Num 0; 1 := Const 1 + Num 1" --"Seq (Assign 1 (Num 0)) (Assign 1 (Add (Const 1) (Num 1)))"

constdefs p3 :: Boolterm -- "The property for  x > 0"
         "p3 == Const 1 > Num 0"



lemma soundProg3:
  "!! s :: State . 
   let s' = iCommand s c3
   in iBoolterm s s' p3"
  sorry

subsection {* Extended Parameters *}

datatype EPC =  EP CSLbinaryP nat nat | EPStar nat | EPBot nat

datatype RS = RS "EPC list"




