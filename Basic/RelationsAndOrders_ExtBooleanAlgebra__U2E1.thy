theory RelationsAndOrders_ExtBooleanAlgebra__U2E1
imports Main
begin

ML_file "$HETS_ISABELLE_LIB/prelude.ML"

setup "Header.initialize
       [\"compl_def_ExtBooleanAlgebra\",
        \"involution_compl_ExtBooleanAlgebra\", \"ga_idem___cup__\",
        \"ga_idem___cap__\", \"uniqueComplement_BooleanAlgebra\",
        \"ga_assoc___cap__\", \"ga_comm___cap__\",
        \"ga_right_unit___cap__\", \"ga_left_unit___cap__\",
        \"ga_left_comm___cap__\", \"ga_assoc___cup__\",
        \"ga_comm___cup__\", \"ga_right_unit___cup__\",
        \"ga_left_unit___cup__\", \"ga_left_comm___cup__\",
        \"absorption_def1\", \"absorption_def2\", \"zeroAndCap\",
        \"oneAndCup\", \"distr1_BooleanAlgebra\",
        \"distr2_BooleanAlgebra\", \"inverse_BooleanAlgebra\",
        \"de_Morgan1\", \"de_Morgan2\"]"

typedecl Elem

consts
X0 :: "Elem" ("0''")
X1 :: "Elem" ("1''")
X__cap__X :: "Elem => Elem => Elem" ("(_/ cap/ _)" [57,57] 56)
X__cup__X :: "Elem => Elem => Elem" ("(_/ cup/ _)" [55,55] 54)
compl__X :: "Elem => Elem" ("(compl/ _)" [62] 62)

axiomatization
where
compl_def_ExtBooleanAlgebra [rule_format] :
"ALL x. ALL y. compl x = y = (x cup y = 1' & x cap y = 0')"
and
involution_compl_ExtBooleanAlgebra [rule_format] :
"ALL x. compl compl x = x"
and
ga_idem___cup__ [rule_format] : "ALL x. x cup x = x"
and
ga_idem___cap__ [rule_format] : "ALL x. x cap x = x"
and
uniqueComplement_BooleanAlgebra [rule_format] :
"ALL x. EX! x'. x cup x' = 1' & x cap x' = 0'"
and
ga_assoc___cap__ :
"ALL x. ALL y. ALL z. (x cap y) cap z = x cap (y cap z)"
and
ga_comm___cap__ [rule_format] : "ALL x. ALL y. x cap y = y cap x"
and
ga_right_unit___cap__ [rule_format] : "ALL x. x cap 1' = x"
and
ga_left_unit___cap__ [rule_format] : "ALL x. 1' cap x = x"
and
ga_left_comm___cap__ [rule_format] :
"ALL x. ALL y. ALL z. x cap (y cap z) = y cap (x cap z)"
and
ga_assoc___cup__ :
"ALL x. ALL y. ALL z. (x cup y) cup z = x cup (y cup z)"
and
ga_comm___cup__ [rule_format] : "ALL x. ALL y. x cup y = y cup x"
and
ga_right_unit___cup__ [rule_format] : "ALL x. x cup 0' = x"
and
ga_left_unit___cup__ [rule_format] : "ALL x. 0' cup x = x"
and
ga_left_comm___cup__ [rule_format] :
"ALL x. ALL y. ALL z. x cup (y cup z) = y cup (x cup z)"
and
absorption_def1 [rule_format] : "ALL x. ALL y. x cap (x cup y) = x"
and
absorption_def2 [rule_format] : "ALL x. ALL y. x cup x cap y = x"
and
zeroAndCap [rule_format] : "ALL x. x cap 0' = 0'"
and
oneAndCup [rule_format] : "ALL x. x cup 1' = 1'"
and
distr1_BooleanAlgebra [rule_format] :
"ALL x. ALL y. ALL z. x cap (y cup z) = x cap y cup x cap z"
and
distr2_BooleanAlgebra [rule_format] :
"ALL x. ALL y. ALL z. x cup y cap z = (x cup y) cap (x cup z)"
and
inverse_BooleanAlgebra [rule_format] :
"ALL x. EX x'. x cup x' = 1' & x cap x' = 0'"

declare involution_compl_ExtBooleanAlgebra [simp]
declare ga_idem___cup__ [simp]
declare ga_idem___cap__ [simp]
declare ga_right_unit___cap__ [simp]
declare ga_left_unit___cap__ [simp]
declare ga_right_unit___cup__ [simp]
declare ga_left_unit___cup__ [simp]
declare absorption_def1 [simp]
declare absorption_def2 [simp]
declare zeroAndCap [simp]
declare oneAndCup [simp]

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

theorem de_Morgan1 :
"ALL x. ALL y. compl (x cap y) = compl x cup compl y"
apply(simp add: compl_def_ExtBooleanAlgebra)
apply((rule allI)+)
apply(rule conjI)
apply(subst ga_comm___cup__)
apply(simp add: distr2_BooleanAlgebra ga_assoc___cup__)
apply(simp add: ga_assoc___cup__rev)
apply(subst ga_comm___cup__)
apply(simp add: ga_assoc___cup__)

apply(simp add: distr1_BooleanAlgebra ga_assoc___cap__)
apply(simp add: ga_assoc___cap__rev)
apply(simp add: ga_comm___cap__)
apply(simp add: ga_assoc___cap__rev)
apply(simp add: ga_comm___cap__)
done

setup "Header.record \"de_Morgan1\""

theorem de_Morgan2 :
"ALL x. ALL y. compl (x cup y) = compl x cap compl y"
apply((rule allI)+)
apply (subst de_Morgan1[THEN spec,THEN spec, THEN sym,
  of "compl x", of "compl y", simplified])
by auto

setup "Header.record \"de_Morgan2\""

end
