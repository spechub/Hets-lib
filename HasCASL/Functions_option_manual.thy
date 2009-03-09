theory Functions_Functions
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"o_def\", \"id_def\", \"o_assoc\", \"id_neut\", \"inj\",
     \"surj\"]"

consts
X__o__X :: "('b => 'c partial) * ('a => 'b partial) => 'a => 'c partial"
X_id :: "'a => 'a partial" ("id''/'(_')" [3] 999)


axioms
o_def [rule_format] :
"ALL f.
 ALL g.
 X__o__X (f, g) =
 (% x. restrictOp ( (makeTotal  o f) ((makeTotal o g) x)) ( (defOp (g x)) & defOp (f (makeTotal o g) x)))"

id_def [rule_format] : "X_id = makePartial o (% x. x)"

theorem o_assoc :
"ALL f.
 ALL g.
 ALL h. X__o__X (f, X__o__X (g, h)) = X__o__X (X__o__X (f, g), h)"
done

theorem id_neut : "ALL f'. X__o__X (f', X_id) = f'"
done


theorem inj  :
"ALL f'.
 X__o__X (f', f') = X_id -->
 (ALL x. ALL y. f' x =s= f' y --> x = y)"
done


theorem surj  :
"ALL f'.
 X__o__X (f', f') = X_id --> (ALL x. EX y. f' y = makePartial x)"
done


end
