theory SinCos_FieldWithSinCos_E1
imports Main
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize [\"th_sc1\",\"ga_nonEmpty\",\"ga_notDefBottom\",\"ga_totality\",\"ga_totality_1\",\"ga_totality_2\",\"ga_totality_3\",\"ga_totality_4\",\"ga_totality_5\",\"ga_totality_6\",\"ga_totality_7\",\"ga_totality_8\",\"ga_totality_9\",\"ga_strictness\",\"ga_strictness_1\",\"Ax1\",\"Ax2\",\"th_ef1\",\"th_ef2\",\"th_ef3\",\"th_ef4\",\"Ax1_1\",\"Ax2_1\",\"Ax3\",\"Ax4\",\"Ax5\",\"th_f0\",\"th_f1\",\"th_f2\",\"th_f3\",\"th_f4\",\"th_f5\",\"th_f6_h\",\"th_f6\",\"th_f7\",\"th_f8\",\"th_f10\",\"th_f11\",\"th_f12\",\"ga_assoc___PlusX__\",\"ga_comm___PlusX__\",\"ga_right_unit___PlusX__\",\"ga_left_unit___PlusX__\",\"ga_assoc___xX__\",\"ga_comm___xX__\",\"ga_right_unit___xX__\",\"ga_left_unit___xX__\",\"Ax9\",\"Ax10\",\"Ax11\",\"Ax12\",\"Ax13\"]"

typedecl Elem

consts
MinusXXX :: "Elem => Elem" ("(-''/ _)" [62] 62)
X0 :: "Elem" ("0''")
X1 :: "Elem" ("1''")
X2 :: "Elem" ("2")
XXMinusXXX :: "Elem => Elem => Elem" ("(_ -''/ _)" [55,55] 54)
XXPlusXXX :: "Elem => Elem => Elem" ("(_ +''/ _)" [54,55] 54)
XXSlashXXX :: "Elem => Elem => Elem" ("(_ '/''/ _)" [57,57] 56)
XXxXXX :: "Elem => Elem => Elem" ("(_ *''/ _)" [56,57] 56)
cosXX :: "Elem => Elem" ("(cos/ _)" [62] 62)
g__bottom :: "Elem" ("g'_'_bottom")
g__defined :: "Elem => bool" ("g'_'_defined'(_')" [10] 999)
invXXX :: "Elem => Elem" ("(inv''/ _)" [62] 62)
qdrXX :: "Elem => Elem" ("(qdr/ _)" [62] 62)
sinXX :: "Elem => Elem" ("(sin/ _)" [62] 62)

instance Elem::type
by intro_classes

axioms
ga_nonEmpty : "EX x. g__defined(x)"

ga_notDefBottom [simp] : "ALL x. (~ g__defined(x)) = (x = g__bottom)"

ga_totality [simp] : "ALL x_1. g__defined(-' x_1) = g__defined(x_1)"

ga_totality_1 [simp] : "g__defined(0')"

ga_totality_2 [simp] : "g__defined(1')"

ga_totality_3 [simp] : "g__defined(2)"

ga_totality_4 [simp] : "ALL x_1. ALL x_2. g__defined(x_1 *' x_2) = (g__defined(x_1) & g__defined(x_2))"

ga_totality_5 [simp] : "ALL x_1. ALL x_2. g__defined(x_1 +' x_2) = (g__defined(x_1) & g__defined(x_2))"

ga_totality_6 [simp] : "ALL x_1. ALL x_2. g__defined(x_1 -' x_2) = (g__defined(x_1) & g__defined(x_2))"

ga_totality_7 [simp] : "ALL x_1. g__defined(cos x_1) = g__defined(x_1)"

ga_totality_8 [simp] : "ALL x_1. g__defined(qdr x_1) = g__defined(x_1)"

ga_totality_9 [simp] : "ALL x_1. g__defined(sin x_1) = g__defined(x_1)"

ga_strictness  : "ALL x_1. ALL x_2. g__defined(x_1 /' x_2) --> g__defined(x_1) & g__defined(x_2)"

ga_strictness_1  : "ALL x_1. g__defined(inv' x_1) --> g__defined(x_1)"

Ax1  : "ALL x. ALL y. g__defined(x) & g__defined(y) --> sin (x -' y) = sin x *' cos y -' cos x *' sin y"

Ax2  : "ALL x. ALL y. g__defined(x) & g__defined(y) --> cos (x -' y) = cos x *' cos y +' sin x *' sin y"

th_ef1 : "ALL x. g__defined(x) --> 2 *' x = x +' x"

th_ef2  : "ALL x. ALL y. g__defined(x) & g__defined(y) --> qdr (x +' y) = qdr x +' 2 *' x *' y +' qdr y"

th_ef3  : "ALL x. ALL y. g__defined(x) & g__defined(y) --> qdr (x -' y) = qdr x +' -' 2 *' x *' y +' qdr y"

th_ef4  : "ALL x. ALL y. g__defined(x) & g__defined(y) --> (x +' y) *' (x -' y) = qdr x -' qdr y"

Ax1_1  : "2 = 1' +' 1'"

Ax2_1 [simp]  : "ALL x. ALL y. g__defined(x) & g__defined(y) --> x -' y = x +' -' y"

Ax3  : "ALL x. g__defined(x) --> qdr x = x *' x"

Ax4 [simp] : "ALL x. ALL y. g__defined(x) & g__defined(y) --> g__defined(x /' y) = (~ y = 0')"

Ax5  : "ALL x. ALL y. g__defined(x) & g__defined(y) --> g__defined(x /' y) --> x /' y = inv' y *' x"

th_f0 [simp] : "ALL x. g__defined(x) --> -' -' x = x"

th_f1  : "ALL x. g__defined(x) --> -' x = -' 1' *' x"

th_f2 [simp] : "ALL x. g__defined(x) --> 0' *' x = 0'"

th_f3 [simp] : "ALL x. g__defined(x) --> 1' *' x = x"

th_f4 [simp] : "ALL x. ALL y. g__defined(x) & g__defined(y) --> -' x *' y = -' (x *' y)"

th_f5 [simp] : "ALL x. ALL y. g__defined(x) & g__defined(y) --> x *' y = 0' --> x = 0' | y = 0'"

th_f6_h : "ALL x. ALL y. ALL z. g__defined(x) & g__defined(y) & g__defined(z) --> (y +' z) *' x = x *' (y +' z)"

th_f6  : "ALL x. ALL y. ALL z. g__defined(x) & g__defined(y) & g__defined(z) --> (y +' z) *' x = y *' x +' z *' x"

th_f7 [simp] : "ALL x. g__defined(x) --> g__defined(inv' x) & g__defined(inv' inv' x) --> inv' inv' x = x"

th_f8 [simp] : "-' 1' *' -' 1' = 1'"

th_f10 [simp] : "ALL x. ALL y. g__defined(x) & g__defined(y) --> x *' -' y = -' (x *' y)"

th_f11 [simp] : "ALL x. ALL y. g__defined(x) & g__defined(y) --> -' x *' -' y = -' -' (x *' y)"

th_f12 [simp] : "ALL x. ALL y. g__defined(x) & g__defined(y) --> -' x *' -' y = x *' y"

ga_assoc___PlusX__ [simp] : "ALL x. ALL y. ALL z. g__defined(x) & g__defined(y) & g__defined(z) --> x +' (y +' z) = x +' y +' z"

ga_comm___PlusX__  : "ALL x. ALL y. g__defined(x) & g__defined(y) --> x +' y = y +' x"

ga_right_unit___PlusX__ [simp] : "ALL x. g__defined(x) --> x +' 0' = x"

ga_left_unit___PlusX__ [simp] : "ALL x. g__defined(x) --> 0' +' x = x"

ga_assoc___xX__ [simp] : "ALL x. ALL y. ALL z. g__defined(x) & g__defined(y) & g__defined(z) --> x *' (y *' z) = x *' y *' z"

ga_comm___xX__ : "ALL x. ALL y. g__defined(x) & g__defined(y) --> x *' y = y *' x"

ga_right_unit___xX__ [simp] : "ALL x. g__defined(x) --> x *' 1' = x"

ga_left_unit___xX__ [simp] : "ALL x. g__defined(x) --> 1' *' x = x"

Ax9 [simp] : "~ 0' = 1'"

Ax10 [simp] : "ALL x. g__defined(x) --> x +' -' x = 0'"

Ax11 [simp] : "ALL x. g__defined(x) --> g__defined(inv' x) = (~ x = 0')"

Ax12 : "ALL x. g__defined(x) --> g__defined(inv' x) --> x *' inv' x = 1'"

Ax13  : "ALL x. ALL y. ALL z. g__defined(x) & g__defined(y) & g__defined(z) --> x *' (y +' z) = x *' y +' x *' z"

ML "reset trace_simp"
theorem th_sc1 : "sin 0' = 0'"
apply(insert ga_nonEmpty)
apply(erule exE)
apply (subst Ax1[THEN spec, THEN spec, of "x", of "x", simplified])
apply (simp)
using ga_comm___xX__ apply(simp)
done

ML "Header.record \"th_sc1\""

end
