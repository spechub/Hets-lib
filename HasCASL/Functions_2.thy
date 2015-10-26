theory Functions_2
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

consts
X__o__X :: "('b => 'c partial) * ('a => 'b partial) => 'a => 'c partial"
X_id :: "'a => 'a partial" ("id''/'(_')" [3] 999)

axioms
o_def [rule_format] :
"ALL f.
 ALL g.
 X__o__X (f, g) =
 (% x. case g x of
       None => noneOp |
       Some Xc0 => f Xc0)"

id_def [rule_format] : "X_id = makePartial o (% x. x)"

lemmas o_def' = o_def [simplified]
lemmas id_def' = id_def [simplified]

(*declare o_def' [simp]*)
declare o_def [simp]
(*declare id_def' [simp]*)
declare id_def [simp]


theorem o_assoc :
"ALL f.
 ALL g.
 ALL h. X__o__X (f, X__o__X (g, h)) = X__o__X (X__o__X (f, g), h)"
apply (simp only: o_def)
(* (%x. option_case None f (option_case None g (h x))) = (%x. case h x of None => None | Some x => option_case None f (g x))*)
apply (auto)
apply (rule ext)
apply (case_tac "h x")
defer
apply (simp)
apply (simp add: noneOp_def)
done

theorem id_neut : "ALL f'. X__o__X (f', X_id) = f'"
oops

theorem inj :
"ALL f'.
 X__o__X (f', f') = X_id -->
 (ALL x. ALL y. f' x =s= f' y --> x = y)"
oops

theorem surj :
"ALL f'.
 X__o__X (f', f') = X_id --> (ALL x. EX y. f' y = makePartial x)"
oops
