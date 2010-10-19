theory CSLSemantics imports Main Real Log Ln Taylor
-- Integration
-- Complex
begin

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

thm "evalF.simps"



