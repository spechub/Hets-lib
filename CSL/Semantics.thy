theory CSLSemantics imports Main Real Log Ln Taylor
-- Integration
-- Complex
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

datatype Term = Const int | Num real | Mult Term Term

fun iTerm :: "State => Term => real" where
"iTerm _ (Num r) = r" |
"iTerm s (Mult t u) = (iTerm s t) * (iTerm s u)" |
"iTerm s (Const i) = s i"

datatype Command = Assign int Term

fun iCommand :: "State => Command => State" where
"iCommand s (Assign i t) = (%x . if x = i then iTerm s t else s x)"

datatype ProgCond = Ge Term Term


fun iProgCond :: "State => ProgCond => bool" where
"iProgCond s (Ge t u) = (iTerm s t >= iTerm s u)"

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
"dependsOn (Const i) = {i}"


types ConstantTermAssignments = "int ~=> Term"

constdefs
  dependsOnWithCTA :: "ConstantTermAssignments => int => int set"
 "dependsOnWithCTA f i == (case f i of
                            Some t => dependsOn t |
                            _ => {})"

  depOrder1 :: "ConstantTermAssignments => (int*int) set"
 "depOrder1 f == {(x, y) | x y . y: dependsOnWithCTA f x}"

  depOrder :: "ConstantTermAssignments => (int*int) set"
 "depOrder f == (depOrder1 f)^+"

constdefs emptyAS :: ConstantTermAssignments
         "emptyAS == %x . None"
          AS_set :: "ConstantTermAssignments set"
         "AS_set == {f. let ord = depOrder f in wf ord & finite ord}"

lemma emptyASempty: "!!x y. ~(emptyAS x = Some y)" by (simp add: emptyAS_def)

lemma emptyAS_has_empty_dep_order : "depOrder emptyAS == {}"
  by (simp add: emptyAS_def depOrder1_def depOrder_def dependsOnWithCTA_def)

lemma emptyAS_in_AS': "emptyAS : AS_set"
  by (simp add: emptyAS_has_empty_dep_order AS_set_def)

typedef AssignmentStore = AS_set
  by (rule exI[of _ emptyAS], simp only: emptyAS_in_AS')

lemma emptyAS_in_AS: "emptyAS : AssignmentStore"
  by (simp add: emptyAS_in_AS' AssignmentStore_def)

(* copied from Fun.thy, see section Function Updating *)
nonterminals
  upd2binds upd2bind
syntax
  "_upd2bind" :: "['a, 'a] => upd2bind"             ("(2_ ::=/ _)")
  ""         :: "upd2bind => upd2binds"             ("_")
  "_upd2binds":: "[upd2bind, upd2binds] => upd2binds" ("_,/ _")
  "_Update2"  :: "['a, upd2binds] => 'a"            ("_/'((_)')" [1000,0] 900)

translations
  "_Update2 f (_upd2binds b bs)"  == "_Update2 (_Update2 f b) bs"
  "f(x::=y)"                     == "fun_upd f x (Some y)"

function fullexpand :: "AssignmentStore => Term => Term" where
"fullexpand _ (Num r) = Num r" |
"fullexpand as (Mult t u) = Mult (fullexpand as t) (fullexpand as u)" |
"fullexpand as (Const i) = (case (Rep_AssignmentStore as) i of
                              Some y => fullexpand as y
                            | None => Const i)"
  sorry

lemma fullexpand_is_total : "!! as t . fullexpand_dom (as, t)"
  sorry

lemma "!!t . fullexpand (Abs_AssignmentStore emptyAS) t = t"
apply (induct_tac "t")
apply auto
apply (simp add: fullexpand_is_total fullexpand.psimps)
apply (subst Abs_AssignmentStore_inverse)
apply auto
apply (rule emptyAS_in_AS)

-- "TODO: continue here:"

apply auto
apply (rule fullexpand.pinduct)

apply (simp add: fullexpand.psimps)

lemma
-- "just for testing"

lemma "!!v x y z. (emptyAS(v::=x)) y = Some z ==> y = v & z = x"
  by (case_tac "y=v", (simp add: emptyASempty)+)


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

