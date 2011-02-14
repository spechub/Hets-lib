theory RelationsAndOrders_ExtBooleanAlgebra_U1E1
imports Main
uses "$HETS_ISABELLE_LIB/prelude.ML"
begin

ML "Header.initialize [\"de_Morgan1\",\"de_Morgan2\",\"compl_def_ExtBooleanAlgebra\",\"involution_compl_ExtBooleanAlgebra\",\"ga_idem___cup__\",\"ga_idem___cap__\",\"uniqueComplement_BooleanAlgebra\",\"ga_assoc___cap__\",\"ga_comm___cap__\",\"ga_right_unit___cap__\",\"ga_left_unit___cap__\",\"ga_assoc___cup__\",\"ga_comm___cup__\",\"ga_right_unit___cup__\",\"ga_left_unit___cup__\",\"absorption_def1\",\"absorption_def2\",\"zeroAndCap\",\"oneAndCup\",\"distr1_BooleanAlgebra\",\"distr2_BooleanAlgebra\",\"inverse_BooleanAlgebra\"]"

typedecl Elem

consts
X0 :: "Elem" ("0''")
X1 :: "Elem" ("1''")
XXcapXX :: "Elem => Elem => Elem" ("(_ cap/ _)" [57,57] 56)
XXcupXX :: "Elem => Elem => Elem" ("(_ cup/ _)" [55,55] 54)
complXX :: "Elem => Elem" ("(compl/ _)" [62] 62)

axioms
compl_def_ExtBooleanAlgebra  : "ALL x. ALL y. compl x = y = (x cup y = 1' & x cap y = 0')"

involution_compl_ExtBooleanAlgebra [simp] : "ALL x. compl compl x = x"

ga_idem___cup__ [simp] : "ALL x. x cup x = x"

ga_idem___cap__ [simp] : "ALL x. x cap x = x"

uniqueComplement_BooleanAlgebra : "ALL x. EX! x'. x cup x' = 1' & x cap x' = 0'"

ga_assoc___cap__  : "ALL x. ALL y. ALL z. x cap (y cap z) = (x cap y) cap z"

ga_comm___cap__  : "ALL x. ALL y. x cap y = y cap x"

ga_right_unit___cap__ [simp] : "ALL x. x cap 1' = x"

ga_left_unit___cap__ [simp] : "ALL x. 1' cap x = x"

ga_assoc___cup__  : "ALL x. ALL y. ALL z. x cup (y cup z) = (x cup y) cup z"

ga_comm___cup__  : "ALL x. ALL y. x cup y = y cup x"

ga_right_unit___cup__ [simp] : "ALL x. x cup 0' = x"

ga_left_unit___cup__ [simp] : "ALL x. 0' cup x = x"

absorption_def1 [simp] : "ALL x. ALL y. x cap (x cup y) = x"

absorption_def2 [simp] : "ALL x. ALL y. x cup x cap y = x"

zeroAndCap [simp] : "ALL x. x cap 0' = 0'"

oneAndCup [simp] : "ALL x. x cup 1' = 1'"

distr1_BooleanAlgebra  : "ALL x. ALL y. ALL z. x cap (y cup z) = x cap y cup x cap z"

distr2_BooleanAlgebra  : "ALL x. ALL y. ALL z. x cup y cap z = (x cup y) cap (x cup z)"

inverse_BooleanAlgebra : "ALL x. EX x'. x cup x' = 1' & x cap x' = 0'"

lemma compl_cap [simp] : "x cap (compl x) = 0'"
using compl_def_ExtBooleanAlgebra apply auto
done
lemma compl_cup [simp]: "x cup (compl x) = 1'"
using compl_def_ExtBooleanAlgebra apply auto
done

lemma compl_cap1 [simp]: "(compl x) cap x = 0'"
using compl_cap ga_comm___cap__ apply auto
done

lemma compl_cup1 [simp]: "(compl x) cup x = 1'"
using compl_cup ga_comm___cup__ apply auto
done

lemmas ga_assoc___cap__rev =
  ga_assoc___cap__[THEN spec, THEN spec, THEN spec, THEN sym]

lemmas ga_assoc___cup__rev =
  ga_assoc___cup__[THEN spec, THEN spec, THEN spec, THEN sym]

theorem de_Morgan1 : "ALL x. ALL y. compl (x cap y) = compl x cup compl y"
apply(simp add: compl_def_ExtBooleanAlgebra)
apply((rule allI)+)
apply(rule conjI)
apply(subst ga_comm___cup__)
apply(simp add: distr2_BooleanAlgebra ga_assoc___cup__rev)
apply(simp add: ga_assoc___cup__)
apply(subst ga_comm___cup__ )
apply(simp add: ga_assoc___cup__rev)

apply(simp add: distr1_BooleanAlgebra ga_assoc___cap__rev)
apply(simp add: ga_assoc___cap__)
apply(simp add: ga_comm___cap__)
apply(simp add: ga_assoc___cap__)
apply(simp add: ga_comm___cap__)
done

ML "Header.record \"de_Morgan1\""

theorem de_Morgan2 : "ALL x. ALL y. compl (x cup y) = compl x cap compl y"
apply((rule allI)+)
apply (subst de_Morgan1[THEN spec,THEN spec, THEN sym, of "compl x", of "compl y", simplified])
by auto

ML "Header.record \"de_Morgan2\""


end
