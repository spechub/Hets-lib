theory Map_Map_E2
imports "$HETS_ISABELLE_LIB/MainHC"
uses "$HETS_ISABELLE_LIB/prelude"
begin

ML "Header.initialize
    [\"Ax1\", \"Ax2\", \"Ax3\", \"Ax1_4\", \"Ax2_5\"]"

typedecl ('a1) List

consts
X_filter :: "'a List => ('a => bool) => 'a List"
X_map :: "('a => 'b partial) => 'a List => 'b List partial"
cons :: "'a => 'a List => 'a List"
nil :: "'a List"

axioms
Ax1 [rule_format] :
"ALL (f :: 'a => 'b partial). X_map f nil = makePartial nil"

Ax2 [rule_format] :
"ALL (f :: 'a => 'b partial).
 ALL (l :: 'a List).
 ALL (x :: 'a).
 X_map f (cons x l) =
 restrictOp
 (makePartial (cons (makeTotal (f x)) (makeTotal (X_map f l))))
 (defOp (f x) & defOp (X_map f l))"

Ax3 [rule_format] :
"ALL (P :: 'a => bool).
 ALL (l :: 'a List).
 ALL (x :: 'a).
 X_filter (cons x l) P =
 (if P x then cons x (X_filter l P) else X_filter l P)"

declare Ax1 [simp]

theorem Ax1_4 :
"ALL (P :: 'a => bool).
 ALL (f :: 'a => 'b partial).
 ALL (l :: 'a List).
 defOp (X_map f l) --> defOp (X_map f (X_filter l P))"
by (auto)

ML "Header.record \"Ax1_4\""

theorem Ax2_5 :
"ALL (Q :: 'b => bool).
 ALL (f :: 'a => 'b partial).
 ALL (l :: 'a List).
 defOp (X_map f l) -->
 restrictOp (makePartial (X_filter (makeTotal (X_map f l)) Q))
 (defOp (X_map f l)) =
 restrictOp (makePartial (X_filter (makeTotal (X_map f l)) Q))
 (defOp (X_map f l))"
by (auto)

ML "Header.record \"Ax2_5\""

end
