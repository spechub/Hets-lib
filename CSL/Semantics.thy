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


(**********************  Toy development 1  **********************)

types State = "int => real"

datatype Term = Const int | Num real | Mult Term Term | Add Term Term

fun iTerm :: "State => Term => real" where
"iTerm _ (Num r) = r" |
"iTerm s (Mult t u) = (iTerm s t) * (iTerm s u)" |
"iTerm s (Add t u) = (iTerm s t) + (iTerm s u)" |
"iTerm s (Const i) = s i"

datatype Command = Assign int Term | Seq Command Command

fun iCommand :: "State => Command => State" where
"iCommand s (Assign i t) = (%x . if x = i then iTerm s t else s x)" |
"iCommand s (Seq c1 c2) = (let s' = iCommand s c1 in iCommand s' c2)"

datatype ProgCond = Ge Term Term | Gt Term Term


fun iProgCond :: "State => ProgCond => bool" where
"iProgCond s (Ge t u) = (iTerm s t >= iTerm s u)" |
"iProgCond s (Gt t u) = (iTerm s t > iTerm s u)"

constdefs c1 :: Command -- "The command for  y := x * x"
         "c1 == Assign 2 (Mult (Const 1) (Const 1))"

constdefs p1 :: ProgCond -- "The property for  y >= 0"
         "p1 == Ge (Const 2) (Num 0)"


lemma soundProg:
  "!! s :: State . 
   let s' = iCommand s c1
   in iProgCond s' p1"

apply (subst Let_def, subst c1_def, subst p1_def)
apply (simp only: iCommand.simps)
apply (simp only: iProgCond.simps)
apply (simp only: iTerm.simps)
apply (simp only: if_P)
by simp
(*

by (simp add: c1_def p1_def iCommand.simps iProgCond.simps)
*)

constdefs c2 :: Command -- "The command for  x := x * x"
         "c2 == Assign 1 (Mult (Const 1) (Const 1))"

constdefs p2 :: ProgCond -- "The property for  x >= 0"
         "p2 == Ge (Const 1) (Num 0)"

lemma soundProg2:
  "!! s :: State . 
   let s' = iCommand s c2
   in iProgCond s' p2"
by (simp add: c2_def p2_def iCommand.simps iProgCond.simps)

constdefs c3 :: Command -- "The command for  x := 0; x := x + 1"
         "c3 == Seq (Assign 1 (Num 0)) (Assign 1 (Add (Const 1) (Num 1)))"

constdefs p3 :: ProgCond -- "The property for  x > 0"
         "p3 == Gt (Const 1) (Num 0)"

lemma soundProg3:
  "!! s :: State . 
   let s' = iCommand s c3
   in iProgCond s' p3"

apply (subst Let_def, subst c3_def, subst p3_def)
apply (simp only: iCommand.simps)
apply (subst Let_def)
apply (simp only: iProgCond.simps)
apply (simp only: iTerm.simps)
by (simp only: if_P)


lemma soundProgExplicit:
  "!! (s :: State) (x :: real) (y :: real). 
   let s' = (%z . if z = 1 then x else if z = 2 then y else s z);
       s'' = iCommand s' c1
   in iProgCond s'' p1"

apply (simp only: Let_def c1_def p1_def iCommand.simps iProgCond.simps iTerm.simps if_P)
by simp

(**********************  Toy development with Assignment store  **********************)

fun dependsOn :: "Term => int set" where
"dependsOn (Num n) = {}" |
"dependsOn (Mult t u) = dependsOn t Un dependsOn u" |
"dependsOn (Add t u) = dependsOn t Un dependsOn u" |
"dependsOn (Const i) = {i}"


types ConstantTermAssignments = "int ~=> Term"

constdefs
  -- "flat dependency for the given constant when lookuped in the CTA"
  dependsOnWithCTALookup :: "ConstantTermAssignments => int => int set"
 "dependsOnWithCTALookup f i == (case f i of
                            Some t => dependsOn t |
                            _ => {})"

  -- "flat dependency relation, not transitive by construction"
  depOrder1 :: "ConstantTermAssignments => (int*int) set"
 "depOrder1 f == {(x, y) | x y . y: dependsOnWithCTALookup f x}"

  -- "transitive closure of depOrder1"
  depOrder :: "ConstantTermAssignments => (int*int) set"
 "depOrder f == (depOrder1 f)^+"

  -- "set of constants the current term (recursively) depends on"
  dependsOnWithCTA :: "ConstantTermAssignments => Term => int set"
 "dependsOnWithCTA f t == Image (depOrder f) (dependsOn t)"

-- "An AssignmentStore is a finite ConstantTermAssignments without cycles"
constdefs AS_set :: "ConstantTermAssignments set"
         "AS_set == {f. let ord = depOrder f in wf ord & finite ord}"

lemma emptyAS_has_empty_dep_order : "depOrder empty == {}"
  by (simp add: depOrder1_def depOrder_def dependsOnWithCTALookup_def)

lemma emptyAS_in_AS': "empty : AS_set"
  by (simp add: emptyAS_has_empty_dep_order AS_set_def)

typedef (AS) AssignmentStore = AS_set
  morphisms asCTA toAS
  by (rule exI[of _ empty], simp only: emptyAS_in_AS')

lemma emptyAS_in_AS: "empty : AS"
  by (simp add: emptyAS_in_AS' AS_def)


function fullexpand :: "AssignmentStore => Term => Term" where
"fullexpand _ (Num r) = Num r" |
"fullexpand as (Mult t u) = Mult (fullexpand as t) (fullexpand as u)" |
"fullexpand as (Add t u) = Add (fullexpand as t) (fullexpand as u)" |
"fullexpand as (Const i) = (case (asCTA as) i of
                              Some y => fullexpand as y
                            | None => Const i)"
  by (auto, case_tac "b", auto)

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

lemma "!!t . fullexpand (toAS empty) t = t"
proof (induct_tac "t", auto)
  fix i
  have H0: "asCTA (toAS empty) = empty" 
    by (simp only: emptyAS_in_AS toAS_inverse)
  have H1: "asCTA (toAS empty) i = empty i"
    by (rule arg_cong, simp add: H0)
  have H2: "asCTA (toAS empty) i = None" by (simp only: H1)
  hence "(case (asCTA (toAS empty) i) of Some y => fullexpand (toAS empty) y | None => Const i) = Const i" by simp
  thus "fullexpand (toAS empty) (Const i) = Const i"
    by(simp add: fullexpand_is_total fullexpand.psimps)
next
  fix r
  show "fullexpand (toAS empty) (Num r) = Num r"
    by (simp add: fullexpand_is_total fullexpand.psimps)
next
  fix t1 t2
  assume "fullexpand (toAS empty) t1 = t1" and "fullexpand (toAS empty) t2 = t2"
  thus "fullexpand (toAS empty) (Mult t1 t2) = (Mult t1 t2)"
    by (simp add: fullexpand_is_total fullexpand.psimps)
next
  fix t1 t2
  assume "fullexpand (toAS empty) t1 = t1" and "fullexpand (toAS empty) t2 = t2"
  thus "fullexpand (toAS empty) (Add t1 t2) = (Add t1 t2)"
    by (simp add: fullexpand_is_total fullexpand.psimps)
qed

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
                             in if i : dependsOn t then None else Some (as(i ::= t')))" |
   "iProg as (Seq c c') = (case iProg as c of
                             Some as' => iProg as' c'
                           | None => None)"

(**********************  Respectful States  **********************)

constdefs respectsAS :: "State => AssignmentStore => bool" (infixl "resp" 50)
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
	

(*
      show " s i =
           iTerm s
            (option_case (Const i)
              (fullexpand as) (asCTA as i))"

*)




(**********************  Test stuff  **********************)

-- "just for testing"

lemma "!!v x y z. (empty(v |-> x)) y = Some z ==> y = v & z = x"
  by (case_tac "y=v", simp+)


(**********************  Main development  **********************)
term "(1, Num 2) :ts"

types CSLid = int

datatype CSLpredefined = Cplus | Cminus | Ctimes | Cdivide | Cpower
  | Csign | Cmin | Cmax | Cabs | Csqrt | Cfthrt | Cpi | Ccos | Csin | Ctan

datatype CSLconst = CSLpredef CSLpredefined | CSLuserdef CSLid

datatype CSLvar = CSLvar CSLid

datatype CSLexpr = Op CSLconst "CSLexpr list" | Num real | Var CSLid

datatype CSLass = Ass CSLid "CSLvar list" CSLexpr

datatype CSLcmd = AssCmd CSLass
                | Repeat CSLexpr "CSLcmd list"

datatype AssignmentStore = ASempty | ASinsert CSLass AssignmentStore

types CSLprog = "CSLcmd list"

fun foosel :: "nat list => nat" where
 "foosel [a, b, _] = a + b" |
 "foosel [a, b] = a * b" |
 "foosel (x#z) = x + foosel z"
thm foosel.simps

primrec lookupDefinition :: "AssignmentStore => CSLid => CSLass option" where
"lookupDefinition ASempty _ = None" |
"lookupDefinition (ASinsert ass as) y = None" -- "TODO: further pattern matching on ass = (Ass x vl e)"

(* Full evaluation of expressions   *)
function evalF :: "AssignmentStore => CSLexpr => CSLexpr" where
"evalF as (Op x l) =
  (let l' = map (evalF as) l
  in case x of
       CSLuserdef cid => (case lookupDefinition as cid of
                           Some (Ass _ _ e) => evalF as e
                         | None => Op x l)
     | CSLpredef _ => Op x l)
" |
"evalF _ (Var _) = Num 1" |
"evalF _ (Num x) = Num 2"

by pat_completeness auto

(* thm "evalF.simps" *)

