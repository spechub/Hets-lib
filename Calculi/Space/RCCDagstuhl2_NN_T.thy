theory RCCDagstuhl2_NN_T
imports "/home/lschrode/CS/CASL/CASL-lib/Isabelle/MainHC"
uses "/home/lschrode/CS/CASL/CASL-lib/Isabelle/prelude"
begin

ML "Header.initialize [\"P_def_1\",\"O_def_1\",\"NTP_def_1\",\"C_non_null\",\"C_sym\",\"C_id\",\"cp_ex\",\"no_atoms\",\"C_non_triv\",\"Ax1\",\"def_nonempty\",\"C_def\",\"P_def\",\"O_def\",\"NTP_def\",\"MS_pos_definite\",\"MS_symm\",\"MS_triangle\",\"Real_abs_def\",\"Real_sqr_def\",\"Real_sqrt_dom\",\"Real_sqrt_def\",\"Real_2_def\",\"Real_minus_def\",\"Real_divide_dom\",\"Real_divide_def\",\"Real_half_def\",\"ga_Nat\",\"Real_ub_def\",\"Real_lb_def\",\"Real_inf_def\",\"Real_sup_def\",\"Real_isBounded_defCBrX\",\"Real_inj_0\",\"Real_inj_suc\",\"Real_archimedian\",\"FWO_plus\",\"FWO_times\",\"Field_unary_minus_def\",\"dichotomy_TotalOrder\",\"antisym\",\"trans\",\"refl\",\"min_inf_relation\",\"max_sup_relation\",\"ga_comm_min\",\"ga_comm_max\",\"ga_assoc_min\",\"ga_assoc_max\",\"min_def_ExtTotalOrder\",\"max_def_ExtTotalOrder\",\"ga_comm_inf\",\"ga_comm_sup\",\"inf_def_ExtPartialOrder\",\"sup_def_ExtPartialOrder\",\"geq_def_ExtPartialOrder\",\"less_def_ExtPartialOrder\",\"greater_def_ExtPartialOrder\",\"EMSCD_rep_pos\",\"EMSCD_rep_0\",\"EMSCD_rep_inj\",\"Ax4\",\"ga_Nat_1\"]"

typedecl ClosedBall
typedecl Real
typedecl S

datatype Nat = X0 | suc "Nat"

consts
MinusXXX :: "Real => Real"
VBarX__VBarX :: "Real => Real"
X0_2 :: "Real"
X1 :: "Real"
X2 :: "Real"
XXCXX :: "ClosedBall * ClosedBall => bool"
XXGtXEqXXX :: "Real * Real => bool"
XXGtXXX :: "Real * Real => bool"
XXLtXEqXXX_1 :: "(Real => bool) * Real => bool"
XXLtXEqXXX_2 :: "Real * (Real => bool) => bool"
XXLtXEqXXX_3 :: "Real * Real => bool"
XXLtXXX :: "Real * Real => bool"
XXMinusXXX :: "Real * Real => Real"
XXNTPXX :: "ClosedBall * ClosedBall => bool"
XXOXXX :: "ClosedBall * ClosedBall => bool"
XXPXX :: "ClosedBall * ClosedBall => bool"
XXPlusXXX :: "Real * Real => Real"
XXSlashXXX :: "Real * Real => Real option"
XXxXXX :: "Real * Real => Real"
closedBall :: "S * Real => ClosedBall"
d :: "S * S => Real"
half :: "Real => Real"
inf_1 :: "(Real => bool) => Real option"
inf_2 :: "Real * Real => Real option"
injX :: "Nat => Real"
isBounded :: "(Real => bool) => bool"
maxX :: "Real * Real => Real"
minX :: "Real * Real => Real"
nonempty :: "ClosedBall => bool"
rep :: "ClosedBall => S => bool"
sqrXX :: "Real => Real"
sqrtXX :: "Real => Real option"
sup_1 :: "(Real => bool) => Real option"
sup_2 :: "Real * Real => Real option"

lemma case_Nat_SomeProm [simp]:" (case caseVar of X0 => Some (x)
   | suc nat => Some (s nat)
) =
Some (case caseVar of X0 => x
   | suc nat => s nat
)"
apply (case_tac caseVar)
apply (auto)
done


instance ClosedBall::type
by intro_classes
instance Real::type
by intro_classes
instance S::type
by intro_classes

axioms
def_nonempty : "ALL x. op = (pApp (Some nonempty) (Some x)) (pApp (Some XXCXX) (pair (Some x) (Some x)))"

C_def : "pApp (Some XXCXX) (pair (Some x) (Some y)) = (EX s. pApp (apt (Some rep) (Some x)) (Some s) & pApp (apt (Some rep) (Some y)) (Some s))"

P_def : "pApp (Some XXPXX) (pair (Some x) (Some y)) = (ALL z. pApp (Some XXCXX) (pair (Some z) (Some x)) --> pApp (Some XXCXX) (pair (Some z) (Some y)))"

O_def : "pApp (Some XXOXXX) (pair (Some x) (Some y)) = (EX z. (pApp (Some XXCXX) (pair (Some z) (Some z)) & pApp (Some XXPXX) (pair (Some z) (Some x))) & pApp (Some XXPXX) (pair (Some z) (Some y)))"

NTP_def : "pApp (Some XXNTPXX) (pair (Some x) (Some y)) = (ALL z. pApp (Some XXCXX) (pair (Some z) (Some x)) --> pApp (Some XXOXXX) (pair (Some z) (Some y)))"

MS_pos_definite [simp] : "op = (apt (Some d) (pair (Some x) (Some y))) (Some X0_2) = op = (Some x) (Some y)"

MS_symm [simp] : "op = (apt (Some d) (pair (Some x) (Some y))) (apt (Some d) (pair (Some y) (Some x)))"

MS_triangle [simp] : "pApp (Some XXLtXEqXXX_3) (pair (apt (Some d) (pair (Some x) (Some z))) (apt (Some XXPlusXXX) (pair (apt (Some d) (pair (Some x) (Some y))) (apt (Some d) (pair (Some y) (Some z))))))"

Real_abs_def [simp] : "op = (apt (Some VBarX__VBarX) (Some r)) (apt (Some maxX) (pair (Some r) (apt (Some MinusXXX) (Some r))))"

Real_sqr_def [simp] : "op = (apt (Some sqrXX) (Some r)) (apt (Some XXxXXX) (pair (Some r) (Some r)))"

Real_sqrt_dom [simp] : "defOp (app (Some sqrtXX) (Some r)) = pApp (Some XXGtXEqXXX) (pair (Some r) (Some X0_2))"

Real_sqrt_def [simp] : "op = (app (Some sqrtXX) (apt (Some sqrXX) (Some r))) (apt (Some VBarX__VBarX) (Some r))"

Real_2_def [simp] : "op = (Some X2) (apt (Some XXPlusXXX) (pair (Some X1) (Some X1)))"

Real_minus_def [simp] : "op = (apt (Some XXMinusXXX) (pair (Some r) (Some r'))) (apt (Some XXPlusXXX) (pair (Some r) (apt (Some MinusXXX) (Some r'))))"

Real_divide_dom [simp] : "~ defOp (app (Some XXSlashXXX) (pair (Some r) (Some X0_2)))"

Real_divide_def [simp] : "op = (app (Some XXSlashXXX) (pair (Some r) (Some r'))) (Some r'') = op = (apt (Some XXxXXX) (pair (Some r'') (Some r'))) (Some r)"

Real_half_def [simp] : "op = (apt (Some XXxXXX) (pair (Some X2) (apt (Some half) (Some r)))) (Some r)"

ga_Nat [simp] : "True"

Real_ub_def : "pApp (Some XXLtXEqXXX_1) (pair (Some M) (Some r)) = (ALL s. pApp (Some M) (Some s) --> pApp (Some XXLtXEqXXX_3) (pair (Some s) (Some r)))"

Real_lb_def : "pApp (Some XXLtXEqXXX_2) (pair (Some r) (Some M)) = (ALL s. pApp (Some M) (Some s) --> pApp (Some XXLtXEqXXX_3) (pair (Some r) (Some s)))"

Real_inf_def : "op = (app (Some inf_1) (Some M)) (Some r) = (pApp (Some XXLtXEqXXX_2) (pair (Some r) (Some M)) & (ALL s. pApp (Some XXLtXEqXXX_2) (pair (Some s) (Some M)) --> pApp (Some XXLtXEqXXX_3) (pair (Some s) (Some r))))"

Real_sup_def : "op = (app (Some sup_1) (Some M)) (Some r) = (pApp (Some XXLtXEqXXX_1) (pair (Some M) (Some r)) & (ALL s. pApp (Some XXLtXEqXXX_1) (pair (Some M) (Some s)) --> pApp (Some XXLtXEqXXX_3) (pair (Some r) (Some s))))"

Real_isBounded_defCBrX : "pApp (Some isBounded) (Some M) = (EX ub. EX lb. pApp (Some XXLtXEqXXX_2) (pair (Some lb) (Some M)) & pApp (Some XXLtXEqXXX_1) (pair (Some M) (Some ub)))"

Real_inj_0 [simp] : "op = (apt (Some injX) (Some X0_1)) (Some X0_2)"

Real_inj_suc [simp] : "op = (apt (Some injX) (apt (Some suc) (Some nX))) (apt (Some XXPlusXXX) (pair (Some X1) (apt (Some injX) (Some nX))))"

Real_archimedian : "EX nX. pApp (Some XXLtXEqXXX_3) (pair (Some r) (apt (Some injX) (Some nX)))"

FWO_plus : "ALL a. ALL b. ALL c. pApp (Some XXLtXEqXXX_3) (pair (Some a) (Some b)) --> pApp (Some XXLtXEqXXX_3) (pair (apt (Some XXPlusXXX) (pair (Some a) (Some c))) (apt (Some XXPlusXXX) (pair (Some b) (Some c))))"

FWO_times : "ALL a. ALL b. ALL c. pApp (Some XXLtXEqXXX_3) (pair (Some a) (Some b)) & pApp (Some XXLtXEqXXX_3) (pair (Some X0_2) (Some c)) --> pApp (Some XXLtXEqXXX_3) (pair (apt (Some XXxXXX) (pair (Some a) (Some c))) (apt (Some XXxXXX) (pair (Some b) (Some c))))"

Field_unary_minus_def : "ALL x. op = (apt (Some XXPlusXXX) (pair (apt (Some MinusXXX) (Some x)) (Some x))) (Some X0_2)"

dichotomy_TotalOrder : "ALL x. ALL y. pApp (Some XXLtXEqXXX_3) (pair (Some x) (Some y)) | pApp (Some XXLtXEqXXX_3) (pair (Some y) (Some x))"

antisym : "ALL x. ALL y. pApp (Some XXLtXEqXXX_3) (pair (Some x) (Some y)) & pApp (Some XXLtXEqXXX_3) (pair (Some y) (Some x)) --> op = (Some x) (Some y)"

trans : "ALL x. ALL y. ALL z. pApp (Some XXLtXEqXXX_3) (pair (Some x) (Some y)) & pApp (Some XXLtXEqXXX_3) (pair (Some y) (Some z)) --> pApp (Some XXLtXEqXXX_3) (pair (Some x) (Some z))"

refl : "ALL x. pApp (Some XXLtXEqXXX_3) (pair (Some x) (Some x))"

min_inf_relation : "ALL x. ALL y. op = (apt (Some minX) (pair (Some x) (Some y))) (app (Some inf_2) (pair (Some x) (Some y)))"

max_sup_relation : "ALL x. ALL y. op = (apt (Some maxX) (pair (Some x) (Some y))) (app (Some sup_2) (pair (Some x) (Some y)))"

ga_comm_min : "ALL x. ALL y. op = (apt (Some minX) (pair (Some x) (Some y))) (apt (Some minX) (pair (Some y) (Some x)))"

ga_comm_max : "ALL x. ALL y. op = (apt (Some maxX) (pair (Some x) (Some y))) (apt (Some maxX) (pair (Some y) (Some x)))"

ga_assoc_min : "ALL x. ALL y. ALL z. op = (apt (Some minX) (pair (Some x) (apt (Some minX) (pair (Some y) (Some z))))) (apt (Some minX) (pair (apt (Some minX) (pair (Some x) (Some y))) (Some z)))"

ga_assoc_max : "ALL x. ALL y. ALL z. op = (apt (Some maxX) (pair (Some x) (apt (Some maxX) (pair (Some y) (Some z))))) (apt (Some maxX) (pair (apt (Some maxX) (pair (Some x) (Some y))) (Some z)))"

min_def_ExtTotalOrder : "ALL x. ALL y. op = (apt (Some minX) (pair (Some x) (Some y))) (if pApp (Some XXLtXEqXXX_3) (pair (Some x) (Some y)) then Some x else Some y)"

max_def_ExtTotalOrder : "ALL x. ALL y. op = (apt (Some maxX) (pair (Some x) (Some y))) (if pApp (Some XXLtXEqXXX_3) (pair (Some x) (Some y)) then Some y else Some x)"

ga_comm_inf : "ALL x. ALL y. op = (app (Some inf_2) (pair (Some x) (Some y))) (app (Some inf_2) (pair (Some y) (Some x)))"

ga_comm_sup : "ALL x. ALL y. op = (app (Some sup_2) (pair (Some x) (Some y))) (app (Some sup_2) (pair (Some y) (Some x)))"

inf_def_ExtPartialOrder : "ALL x. ALL y. ALL z. op = (app (Some inf_2) (pair (Some x) (Some y))) (Some z) = (pApp (Some XXLtXEqXXX_3) (pair (Some z) (Some x)) & pApp (Some XXLtXEqXXX_3) (pair (Some z) (Some y)) & (ALL t. pApp (Some XXLtXEqXXX_3) (pair (Some t) (Some x)) & pApp (Some XXLtXEqXXX_3) (pair (Some t) (Some y)) --> pApp (Some XXLtXEqXXX_3) (pair (Some t) (Some z))))"

sup_def_ExtPartialOrder : "ALL x. ALL y. ALL z. op = (app (Some sup_2) (pair (Some x) (Some y))) (Some z) = (pApp (Some XXLtXEqXXX_3) (pair (Some x) (Some z)) & pApp (Some XXLtXEqXXX_3) (pair (Some y) (Some z)) & (ALL t. pApp (Some XXLtXEqXXX_3) (pair (Some x) (Some t)) & pApp (Some XXLtXEqXXX_3) (pair (Some y) (Some t)) --> pApp (Some XXLtXEqXXX_3) (pair (Some z) (Some t))))"

geq_def_ExtPartialOrder : "ALL x. ALL y. pApp (Some XXGtXEqXXX) (pair (Some x) (Some y)) = pApp (Some XXLtXEqXXX_3) (pair (Some y) (Some x))"

less_def_ExtPartialOrder : "ALL x. ALL y. pApp (Some XXLtXXX) (pair (Some x) (Some y)) = (pApp (Some XXLtXEqXXX_3) (pair (Some x) (Some y)) & ~ op = (Some x) (Some y))"

greater_def_ExtPartialOrder : "ALL x. ALL y. pApp (Some XXGtXXX) (pair (Some x) (Some y)) = pApp (Some XXLtXXX) (pair (Some y) (Some x))"

EMSCD_rep_pos [simp] : "(pApp (Some XXGtXXX) (pair (Some r) (Some X0_2)) --> pApp (apt (Some rep) (apt (Some closedBall) (pair (Some x) (Some r)))) (Some y)) = pApp (Some XXLtXEqXXX_3) (pair (apt (Some d) (pair (Some x) (Some y))) (Some r))"

EMSCD_rep_0 [simp] : "~ pApp (Some XXGtXXX) (pair (Some r) (Some X0_2)) --> ~ pApp (apt (Some rep) (apt (Some closedBall) (pair (Some x) (Some X0_2)))) (Some y)"

EMSCD_rep_inj : "op = (apt (Some rep) (Some a)) (apt (Some rep) (Some b)) --> op = (Some a) (Some b)"

Ax4 : "EX z. EX t. op = (Some a) (apt (Some closedBall) (pair (Some z) (Some t)))"

ga_Nat_1 [simp] : "True"

lemmas P_def' = P_def [simplified]
lemmas C_def' = C_def [simplified]
lemmas O_def' = O_def [simplified]
lemmas NTP_def' = NTP_def [simplified]
lemmas Ax4' = Ax4 [simplified]
lemmas EMSCD_rep_pos' = EMSCD_rep_pos [simplified]
lemmas EMSCD_rep_0' = EMSCD_rep_0 [simplified]

thm EMSCD_rep_pos [simplified]
thm mp
thm EMSCD_rep_pos [simplified, THEN mp]



declare P_def' [simp]
declare C_def' [simp]
declare O_def' [simp]
declare NTP_def' [simp]
declare EMSCD_rep_pos' [simp]
declare EMSCD_rep_0' [simp]


theorem P_def_1 : "ALL x. ALL y. pApp (Some XXPXX) (pair (Some x) (Some y)) = (ALL z. pApp (Some XXCXX) (pair (Some z) (Some x)) --> pApp (Some XXCXX) (pair (Some z) (Some y)))"
by auto

ML "Header.record \"P_def_1\""

theorem O_def_1 : "ALL x. ALL y. pApp (Some XXOXXX) (pair (Some x) (Some y)) = (EX z. pApp (Some XXCXX) (pair (Some z) (Some z)) & pApp (Some XXPXX) (pair (Some z) (Some x)) & pApp (Some XXPXX) (pair (Some z) (Some y)))"
by auto

ML "Header.record \"O_def_1\""

theorem NTP_def_1 : "ALL x. ALL y. pApp (Some XXNTPXX) (pair (Some x) (Some y)) = (ALL z. pApp (Some XXCXX) (pair (Some z) (Some x)) --> pApp (Some XXOXXX) (pair (Some z) (Some y)))"
by auto

ML "Header.record \"NTP_def_1\""

theorem C_non_null : "ALL x. ALL y. pApp (Some XXCXX) (pair (Some x) (Some y)) --> pApp (Some XXCXX) (pair (Some x) (Some x))"
by auto

ML "Header.record \"C_non_null\""

theorem C_sym : "ALL x. ALL y. pApp (Some XXCXX) (pair (Some x) (Some y)) --> pApp (Some XXCXX) (pair (Some y) (Some x))"
by auto

ML "Header.record \"C_sym\""

theorem C_id : "ALL x. ALL y. (ALL z. pApp (Some XXCXX) (pair (Some z) (Some x)) = pApp (Some XXCXX) (pair (Some z) (Some y))) --> op = (Some x) (Some y)"
apply (auto)
apply (rule EMSCD_rep_inj [THEN mp, simplified])
apply (rule ext)
apply (auto)
apply (erule contrapos_pp)
apply (subst not_all)
apply (insert Ax4' [THEN allI, of "%x. x"])
apply (frule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (erule exE)
apply (erule exE)
apply (erule exE)
apply (erule exE)
apply (subst not_iff)
apply (case_tac "XXGtXXX (ta,X0_2)")
defer
apply (simp)
apply(force)
apply (rule_tac x="closedBall(xa,half (XXMinusXXX (d(za,xa),ta)))" in exI)
apply (subst not_iff)
apply (auto)
apply (simp add: EMSCD_rep_def)
apply (clarify)


apply (rule_tac "x= exI 
apply (clarify)

thm contrapos_pp

apply (rule allI)
apply (rule allI)
apply (rule impI)
apply (rule EMSCD_inj_inj [THEN mp])
ML "set trace_simp"
apply (simp only: pApp.simps pair.simps apt.simps option.cases)
apply (auto)

ML "Header.record \"C_id\""

theorem cp_ex : "ALL x. ALL y. EX z. ALL u. pApp (Some XXCXX) (pair (Some z) (Some u)) = (~ pApp (Some XXNTPXX) (pair (Some u) (Some x)) | ~ pApp (Some XXNTPXX) (pair (Some u) (Some y)))"
oops

ML "Header.record \"cp_ex\""

theorem no_atoms : "ALL x. pApp (Some XXCXX) (pair (Some x) (Some x)) --> (EX z. pApp (Some XXCXX) (pair (Some z) (Some z)) & pApp (Some XXNTPXX) (pair (Some z) (Some x)))"
oops

ML "Header.record \"no_atoms\""

theorem C_non_triv : "EX x. pApp (Some XXCXX) (pair (Some x) (Some x))"
oops

ML "Header.record \"C_non_triv\""

theorem Ax1 : "ALL x. pApp (Some nonempty) (Some x) = pApp (Some XXCXX) (pair (Some x) (Some x))"
oops

ML "Header.record \"Ax1\""

end
